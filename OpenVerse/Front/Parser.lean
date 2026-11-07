/-
  OpenVerse front end — parser.

  Recursive descent over the token array, with the precedence of the Book of
  Verse (ch. 4 "Operators"): `or` < `and` < comparisons < `+ -` < `* /` <
  unary `- not` < postfix `() [] . ?`. Comparisons form chains
  (`0 <= X <= 9` checks both and returns `0`).

  Layout: Verse mixes indented blocks (`if (c):` + indented lines), braces
  and inline forms (`then`). The parser uses an offside rule on columns. A
  block whose statements start at column `c` continues a statement only onto
  tokens that start a line at a column `> c`; a token starting a line at
  column `= c` starts the next statement, and `< c` ends the block.

  Columns count a tab as one column, so the indentation of every line (a
  string of tabs and spaces) must be consistent with that of the innermost
  enclosing indented block: one must be a prefix of the other. The block's
  indentation is that of the line of its first token, the one whose column
  the block uses. The parser keeps these on a stack (`PSt.blocks`) and checks
  the first token of each line when it is consumed, and when it ends a block;
  blank and comment-only lines have no token and are exempt.
-/
import OpenVerse.Front.Lexer
import OpenVerse.Front.Syntax

namespace OpenVerse.Front

structure PSt where
  toks : Array Token
  pos  : Nat := 0
  /-- The indentation of the enclosing indented blocks, innermost first
      (the top level, `""`, is not on the stack). -/
  blocks : List String := []
  /-- The files imported with `using{"relative_path"}` (#27). -/
  imports : Array (Pos × String) := #[]

abbrev PM := StateT PSt (Except String)

def peekT (k : Nat := 0) : PM Token := do
  let s ← get
  return s.toks[s.pos + k]?.getD (s.toks.back?.getD default)

def perr (t : Token) (msg : String) : PM α :=
  throw s!"{t.line}:{t.col}: {msg}"

def Token.isEof (t : Token) : Bool := match t.tok with | .eof => true | _ => false

/-- `"4 spaces"`, `"1 tab then 2 spaces"`, `"no indentation"`. -/
def describeIndent (s : String) : String :=
  let runs := s.toList.splitBy (· == ·)
  if runs.isEmpty then "no indentation" else
  " then ".intercalate <| runs.map fun r =>
    let n := r.length
    let w := if r.head! == '\t' then "tab" else "space"
    s!"{n} {w}{if n == 1 then "" else "s"}"

/-- A line starting with `t` must be indented consistently with the innermost
    enclosing indented block: one indentation is a prefix of the other. -/
def checkIndent (t : Token) : PM Unit := do
  if t.bol && !t.isEof then
    let b := (← get).blocks.headD ""
    if !(t.indent.isPrefixOf b || b.isPrefixOf t.indent) then
      perr t s!"inconsistent use of tabs and spaces: this line is indented with \
        {describeIndent t.indent} and its block with {describeIndent b}, \
        but neither is a prefix of the other"

def bump : PM Unit := do
  let s ← get
  if let some t := s.toks[s.pos]? then checkIndent t
  set { s with pos := s.pos + 1 }

/-- Run `p`, an indented block whose first token is `t`. When `t` starts a
    line, its indentation (checked against the enclosing block's) becomes the
    block's for the lines of `p`. -/
def withBlock (t : Token) (p : PM α) : PM α := do
  if !t.bol || t.isEof then p else
  checkIndent t
  modify fun s => { s with blocks := t.indent :: s.blocks }
  let r ← p
  modify fun s => { s with blocks := s.blocks.tail }
  return r

def Token.isSym (t : Token) (s : String) : Bool :=
  match t.tok with | .sym x => x == s | _ => false

def Token.isKw (t : Token) (k : String) : Bool :=
  match t.tok with | .ident x => x == k | _ => false

def Token.pos (t : Token) : Pos := { line := t.line, col := t.col, file := t.file }

def keywords : List String :=
  ["if", "then", "else", "for", "do", "loop", "break", "return", "var", "set", "and", "or",
   "not", "case", "block", "option", "logic", "array", "using", "struct", "enum", "map", "where"]

def Token.identName? (t : Token) : Option String :=
  match t.tok with
  | .ident x => if keywords.contains x then none else some x
  | _ => none

/-- `t` cannot continue an expression whose statement column is `stop`. -/
def Token.offside (t : Token) (stop : Nat) : Bool := (t.bol && t.col ≤ stop) || t.isEof

def expectSym (s : String) : PM Unit := do
  let t ← peekT
  if t.isSym s then bump else perr t s!"expected '{s}', found {t.tok.describe}"

def expectKw (k : String) : PM Unit := do
  let t ← peekT
  if t.isKw k then bump else perr t s!"expected '{k}', found {t.tok.describe}"

def expectIdent : PM String := do
  let t ← peekT
  match t.identName? with
  | some n => bump; return n
  | none => perr t s!"expected an identifier, found {t.tok.describe}"

partial def parseType : PM STy := do
  let t ← peekT
  if t.isSym "[" then
    bump
    if (← peekT).isSym "]" then bump; return .arr (← parseType)
    let k ← parseType
    expectSym "]"
    return .map k (← parseType)
  else if t.isSym "?" then
    bump; return .opt (← parseType)
  else if t.isKw "logic" && !(← peekT 1).isSym "{" then
    -- `logic` is a keyword (for `logic{…}`) and a type name
    bump; return .name "logic"
  else if t.isKw "tuple" && (← peekT 1).isSym "(" then
    bump; bump
    let mut ts := #[]
    if !(← peekT).isSym ")" then
      ts := ts.push (← parseType)
      while (← peekT).isSym "," do bump; ts := ts.push (← parseType)
    expectSym ")"
    return .tup ts.toList
  else match t.identName? with
    | some n =>
      bump
      if (← peekT).isSym "(" then
        -- `pair(int, string)`: a parametric struct applied to type arguments
        bump
        let mut ts := #[← parseType]
        while (← peekT).isSym "," do bump; ts := ts.push (← parseType)
        expectSym ")"
        return .app n ts.toList
      return .name n
    | none => perr t s!"expected a type, found {t.tok.describe}"

def cmpOps : List String := ["=", "<>", "<", "<=", ">", ">="]

mutual
/-- Lowest precedence: declarations, `set`, ranges. -/
partial def parseExpr (stop : Nat) : PM SExpr := do
  let t ← peekT
  let t1 ← peekT 1
  if t.isKw "var" then
    bump
    let n ← expectIdent
    expectSym ":"
    let ty ← parseType
    let a ← peekT
    if a.isSym "=" || a.isSym ":=" then bump else perr a "expected '=' after var declaration"
    return .decl t.pos n (some ty) true (← parseExpr stop)
  else if t.isKw "set" then
    bump
    let lhs ← parsePostfix stop
    let a ← peekT
    let op ← match a.tok with
      | .sym "=" => pure none
      | .sym "+=" => pure (some "+")
      | .sym "-=" => pure (some "-")
      | .sym "*=" => pure (some "*")
      | .sym "/=" => pure (some "/")
      | _ => perr a "expected '=' or a compound assignment in set"
    bump
    return .set t.pos lhs op (← parseExpr stop)
  else if t.identName?.isSome && t1.isSym ":=" then
    bump; bump
    return .decl t.pos t.identName?.get! none false (← parseExpr stop)
  else if t.identName?.isSome && t1.isSym ":" then
    let saved ← get
    let typed ← (do
        bump; bump
        let ty ← parseType
        let a ← peekT
        if a.isSym "=" || a.isSym ":=" then bump; return some ty else return none)
      <|> pure none
    match typed with
    | some ty => return .decl t.pos t.identName?.get! (some ty) false (← parseExpr stop)
    | none => set saved; parseRange stop
  else parseRange stop

partial def parseRange (stop : Nat) : PM SExpr := do
  let a ← parseOr stop
  let t ← peekT
  if t.isSym ".." && !t.offside stop then
    bump
    return .range t.pos a (← parseOr stop)
  return a

partial def parseOr (stop : Nat) : PM SExpr := do
  let mut a ← parseAnd stop
  repeat
    let t ← peekT
    if t.isKw "or" && !t.offside stop then
      bump; a := .orE t.pos a (← parseAnd stop)
    else break
  return a

partial def parseAnd (stop : Nat) : PM SExpr := do
  let mut a ← parseCmp stop
  repeat
    let t ← peekT
    if t.isKw "and" && !t.offside stop then
      bump; a := .andE t.pos a (← parseCmp stop)
    else break
  return a

partial def parseCmp (stop : Nat) : PM SExpr := do
  let a ← parseAdd stop
  let mut rest := #[]
  repeat
    let t ← peekT
    match t.tok with
    | .sym op =>
      if cmpOps.contains op && !t.offside stop then
        bump; rest := rest.push (op, ← parseAdd stop)
      else break
    | _ => break
  if rest.isEmpty then return a else return .cmp a.pos a rest.toList

partial def parseAdd (stop : Nat) : PM SExpr := do
  let mut a ← parseMul stop
  repeat
    let t ← peekT
    if (t.isSym "+" || t.isSym "-") && !t.offside stop then
      bump
      let op := if t.isSym "+" then "+" else "-"
      a := .bin t.pos op a (← parseMul stop)
    else break
  return a

partial def parseMul (stop : Nat) : PM SExpr := do
  let mut a ← parseUnary stop
  repeat
    let t ← peekT
    if (t.isSym "*" || t.isSym "/") && !t.offside stop then
      bump
      let op := if t.isSym "*" then "*" else "/"
      a := .bin t.pos op a (← parseUnary stop)
    else break
  return a

partial def parseUnary (stop : Nat) : PM SExpr := do
  let t ← peekT
  if t.isSym "-" then
    bump
    let e ← parseUnary stop
    match e with
    | .int _ n => return .int t.pos (-n)
    | e => return .neg t.pos e
  else if t.isSym "+" then
    bump; parseUnary stop
  else if t.isKw "not" then
    bump; return .notE t.pos (← parseUnary stop)
  else parsePostfix stop

partial def parsePostfix (stop : Nat) : PM SExpr := do
  let mut e ← parsePrimary stop
  repeat
    let t ← peekT
    if t.offside stop || t.bol then break
    if t.isSym "(" then
      -- `pair(int, string){…}`: type arguments then a struct value; otherwise a call
      let cons? ← match e with
        | .ident _ n => do
          let saved ← get
          let r ← (do
              bump
              let mut ts := #[← parseType]
              while (← peekT).isSym "," do bump; ts := ts.push (← parseType)
              expectSym ")"
              let b ← peekT
              if b.isSym "{" && !b.offside stop && !b.bol then bump; return some (n, ts.toList)
              return none) <|> pure none
          if r.isNone then set saved
          pure r
        | _ => pure none
      match cons? with
      | some (n, ts) => e := .construct t.pos n ts (← parseArgs "}")
      | none => bump; e := .app t.pos e (← parseArgs ")") false
    else if t.isSym "{" && (match e with | .ident _ _ => true | _ => false) then
      -- `point{X := 1, Y := 2}`: a struct value
      bump
      let name := match e with | .ident _ n => n | _ => ""
      e := .construct t.pos name [] (← parseArgs "}")
    else if t.isSym "[" then
      bump; e := .app t.pos e (← parseArgs "]") true
    else if t.isSym "." then
      bump; e := .member t.pos e (← expectIdent)
    else if t.isSym "?" then
      bump; e := .query t.pos e
    else break
  return e

/-- Comma-separated arguments up to `close` (consumed). Newlines are whitespace. -/
partial def parseArgs (close : String) : PM (List SExpr) := do
  if (← peekT).isSym close then bump; return []
  -- `?Name := e` is a named argument, kept as a declaration of `?Name`
  let arg : PM SExpr := do
    let t ← peekT
    if t.isSym "?" && (← peekT 1).identName?.isSome && (← peekT 2).isSym ":=" then
      bump
      let n ← expectIdent
      bump
      return .decl t.pos ("?" ++ n) none false (← parseExpr 0)
    parseExpr 0
  let mut args := #[← arg]
  repeat
    let t ← peekT
    if t.isSym "," then bump; args := args.push (← arg)
    else if t.isSym close then bump; break
    else perr t s!"expected ',' or '{close}', found {t.tok.describe}"
  return args.toList

/-- Elements of `( … )` after the `(`: separated by `,` (a tuple) or by `;` /
    newlines (a sequence). Returns the elements and whether commas were used. -/
partial def parseParenItems : PM (List SExpr × Bool) := do
  if (← peekT).isSym ")" then bump; return ([], true)
  let mut items := #[← parseExpr 0]
  let mut commas := false
  let mut semis := false
  repeat
    let t ← peekT
    if t.isSym "," then bump; commas := true; items := items.push (← parseExpr 0)
    else if t.isSym ";" then bump; semis := true; items := items.push (← parseExpr 0)
    else if t.isSym ")" then bump; break
    else if t.bol && !t.isEof then semis := true; items := items.push (← parseExpr 0)
    else perr t s!"expected ',', ';' or ')', found {t.tok.describe}"
  if commas && semis then perr (← peekT) "cannot mix ',' and ';' separators"
  return (items.toList, commas)

/-- An indented block whose statements start at column `c`. -/
partial def parseIndented (c : Nat) : PM (List SExpr) := do
  withBlock (← peekT) do
    let mut stmts := #[← parseExpr c]
    repeat
      let t ← peekT
      checkIndent t
      if t.isSym ";" then bump; stmts := stmts.push (← parseExpr c)
      else if t.isEof then break
      else if t.bol && t.col == c && !t.isKw "else" && !t.isKw "then" && !t.isSym "}" && !t.isSym ")" then
        stmts := stmts.push (← parseExpr c)
      else if t.bol && t.col > c then perr t "unexpected indentation"
      else break
    return stmts.toList

/-- A braced block after its `{`, up to the `}` (consumed). -/
partial def parseBraced (p : Pos) : PM SExpr := do
  if (← peekT).isSym "}" then bump; return .block p []
  let c := (← peekT).col
  let stmts ← withBlock (← peekT) do
    let mut stmts := #[← parseExpr c]
    repeat
      let t ← peekT
      checkIndent t
      if t.isSym ";" || t.isSym "," then bump; stmts := stmts.push (← parseExpr c)
      else if t.isSym "}" then break
      else if t.bol && !t.isEof then stmts := stmts.push (← parseExpr c)
      else perr t s!"expected ';', a new line or '}', found {t.tok.describe}"
    return stmts
  bump
  return .block p stmts.toList

/-- The body of a construct: `: block`, `:` + inline expression, or `{ block }`. -/
partial def parseBody (stop : Nat) : PM SExpr := do
  let t ← peekT
  if t.isSym ":" then
    bump
    let n ← peekT
    if n.bol then
      if n.col ≤ stop then perr n "expected an indented block"
      return .block t.pos (← parseIndented n.col)
    else return .block t.pos [← parseExpr stop]
  else if t.isSym "{" then
    bump; parseBraced t.pos
  else perr t s!"expected ':' or '\{', found {t.tok.describe}"

/-- `then` / `else` / `do` parts: a body, or an inline expression. -/
partial def parseBranch (stop : Nat) : PM SExpr := do
  let t ← peekT
  if t.isSym ":" || t.isSym "{" then parseBody stop else parseExpr stop

partial def parseIf (stop : Nat) : PM SExpr := do
  let t ← peekT
  bump
  let conds ← if (← peekT).isSym ":" then do
      -- `if:` followed by an indented block of conditions, then `then:`
      bump
      let n ← peekT
      let cs ← parseIndented n.col
      expectKw "then"
      pure cs
    else do
      expectSym "("
      let (items, _) ← parseParenItems
      pure items
  let thenE ← if (← peekT).isKw "then" then do bump; parseBranch stop else parseBody stop
  let e ← peekT
  if e.isKw "else" then
    bump
    if (← peekT).isKw "if" then return .ite t.pos conds thenE (some (← parseIf stop))
    return .ite t.pos conds thenE (some (← parseBranch stop))
  return .ite t.pos conds thenE none

/-- One `for` clause: a generator, a binding, or a filter. -/
partial def parseClause : PM SExpr := do
  let t ← peekT
  let t1 ← peekT 1
  match t.identName? with
  | some i =>
    if t1.isSym "->" then
      bump; bump
      let x ← expectIdent
      expectSym ":"
      return .gen t.pos x (some i) (← parseExpr 0)
    else if t1.isSym ":" then
      -- `X:t = e` is a typed binding; otherwise `X : src` is a generator
      let saved ← get
      let typed ← (do
          bump; bump
          let ty ← parseType
          let a ← peekT
          if a.isSym "=" || a.isSym ":=" then bump; return some ty else return none) <|> pure none
      match typed with
      | some ty => return .decl t.pos i (some ty) false (← parseExpr 0)
      | none =>
        set saved; bump; bump
        return .gen t.pos i none (← parseExpr 0)
    else parseExpr 0
  | none => parseExpr 0

partial def parseFor (stop : Nat) : PM SExpr := do
  let t ← peekT
  bump
  expectSym "("
  let mut clauses := #[]
  if !(← peekT).isSym ")" then
    clauses := clauses.push (← parseClause)
    repeat
      let s ← peekT
      if s.isSym "," || s.isSym ";" then bump; clauses := clauses.push (← parseClause)
      else if s.isSym ")" then break
      else if s.bol then clauses := clauses.push (← parseClause)
      else perr s s!"expected ',' or ')' in for clauses, found {s.tok.describe}"
  expectSym ")"
  let body ← if (← peekT).isKw "do" then do bump; parseBranch stop else parseBody stop
  return .forE t.pos clauses.toList body

partial def parseCase (stop : Nat) : PM SExpr := do
  let t ← peekT
  bump
  expectSym "("
  let scrut ← parseExpr 0
  expectSym ")"
  let parseArm (c : Nat) : PM (Option SExpr × SExpr) := do
    let a ← peekT
    let pat ← if a.isKw "_" || (match a.tok with | .ident "_" => true | _ => false) then do
        bump; pure none
      else some <$> parseAdd 0
    expectSym "=>"
    return (pat, ← parseExpr c)
  let o ← peekT
  let mut arms := #[]
  if o.isSym ":" then
    bump
    let n ← peekT
    let c := n.col
    arms ← withBlock n do
      let mut arms := #[← parseArm c]
      repeat
        let a ← peekT
        checkIndent a
        if a.bol && a.col == c && !a.isEof then arms := arms.push (← parseArm c) else break
      return arms
  else if o.isSym "{" then
    bump
    let c := (← peekT).col
    arms ← withBlock (← peekT) do
      let mut arms := #[]
      repeat
        let a ← peekT
        checkIndent a
        if a.isSym "}" then break
        if a.isSym "," || a.isSym ";" then bump
        arms := arms.push (← parseArm c)
      return arms
    bump
  else perr o "expected ':' or '{' after case (…)"
  let _ := stop
  return .caseE t.pos scrut arms.toList

/-- One struct field: `[var] Name:type [= default]`. -/
partial def parseField (c : Nat) : PM (String × STy × Option SExpr × Bool) := do
  let isVar := (← peekT).isKw "var"
  if isVar then bump
  let n ← expectIdent
  expectSym ":"
  let ty ← parseType
  let a ← peekT
  if a.isSym "=" || a.isSym ":=" then
    bump
    return (n, ty, some (← parseExpr c), isVar)
  return (n, ty, none, isVar)

/-- `struct` (after the keyword): optional specifiers, then `:` + fields or `{ fields }`. -/
partial def parseStructBody (p : Pos) : PM SExpr := do
  while (← peekT).isSym "<" do
    bump; bump; expectSym ">"
  let o ← peekT
  let mut fields := #[]
  if o.isSym ":" then
    bump
    let n ← peekT
    let c := n.col
    fields ← withBlock n do
      let mut fields := #[← parseField c]
      repeat
        let a ← peekT
        checkIndent a
        if a.isSym ";" then bump; fields := fields.push (← parseField c)
        else if a.bol && a.col == c && !a.isEof then fields := fields.push (← parseField c)
        else break
      return fields
  else if o.isSym "{" then
    bump
    repeat
      let a ← peekT
      if a.isSym "}" then bump; break
      if a.isSym "," || a.isSym ";" then bump; continue
      fields := fields.push (← parseField 0)
  else perr o "expected ':' or '{' after struct"
  return .structDef p [] fields.toList

/-- `enum` (after the keyword): `:` + values or `{ values }`. -/
partial def parseEnumBody (p : Pos) : PM SExpr := do
  while (← peekT).isSym "<" do
    bump; bump; expectSym ">"
  let o ← peekT
  let mut names := #[]
  if o.isSym ":" then
    bump
    let n ← peekT
    let c := n.col
    names ← withBlock n do
      let mut names := #[← expectIdent]
      repeat
        let a ← peekT
        checkIndent a
        if a.isSym "," || a.isSym ";" then bump; names := names.push (← expectIdent)
        else if a.bol && a.col == c && !a.isEof then names := names.push (← expectIdent)
        else break
      return names
  else if o.isSym "{" then
    bump
    repeat
      let a ← peekT
      if a.isSym "}" then bump; break
      if a.isSym "," || a.isSym ";" then bump; continue
      names := names.push (← expectIdent)
  else perr o "expected ':' or '{' after enum"
  return .enumDef p names.toList

partial def parseInterp (parts : List StrPart) : PM (List SPart) := do
  let mut out := #[]
  for part in parts do
    match part with
    | .text s => out := out.push (.text s)
    | .code src l c =>
      match lex src l c with
      | .error e => throw e
      | .ok toks =>
        let saved ← get
        set ({ toks } : PSt)
        let e ← parseExpr 0
        let rest ← peekT
        if !rest.isEof then perr rest "unexpected tokens in interpolation"
        set saved
        out := out.push (.code e)
  return out.toList

partial def parsePrimary (stop : Nat) : PM SExpr := do
  let t ← peekT
  match t.tok with
  | .int n => bump; return .int t.pos n
  | .char c => bump; return .char t.pos c
  | .str parts => bump; return .str t.pos (← parseInterp parts)
  | .sym "(" =>
    if (← peekT 1).isKw "super" && (← peekT 2).isSym ":" && (← peekT 3).isSym ")" then
      -- `(super:)M`: the parent's implementation of a method
      bump; bump; bump; bump
      return .member t.pos (.ident t.pos "(super:)") (← expectIdent)
    bump
    let (items, commas) ← parseParenItems
    match items with
    | [] => return .tuple t.pos []
    | [e] => return e
    | es => return if commas then .tuple t.pos es else .block t.pos es
  | .sym "{" => bump; parseBraced t.pos
  | .ident "if" => parseIf stop
  | .ident "for" => parseFor stop
  | .ident "case" => parseCase stop
  | .ident "loop" => bump; return .loop t.pos (← parseBody stop)
  | .ident "block" => bump; parseBody stop
  | .ident "let" =>
    if (← peekT 1).isSym "(" then
      -- `let(defs){body}`: the definitions are visible in the body only, and
      -- the value is the body's (spec: LetMacro)
      bump; bump
      let (defs, _) ← parseParenItems
      let body ← parseBody stop
      return .block t.pos (defs ++ [.block t.pos [body]])
    else
      bump; return .ident t.pos "let"
  | .ident "break" => bump; return .brk t.pos
  | .ident "return" =>
    bump
    let n ← peekT
    if n.offside stop || n.isSym ")" || n.isSym "}" || n.isSym ";" || n.isKw "else" then
      return .ret t.pos none
    return .ret t.pos (some (← parseExpr stop))
  | .ident "array" =>
    bump; expectSym "{"; return .arrayLit t.pos (← parseArgs "}")
  | .ident "map" =>
    bump; expectSym "{"
    let mut entries := #[]
    repeat
      let a ← peekT
      if a.isSym "}" then bump; break
      if a.isSym "," then bump; continue
      let k ← parseExpr 0
      expectSym "=>"
      entries := entries.push (k, ← parseExpr 0)
    return .mapLit t.pos entries.toList
  | .ident "struct" => bump; parseStructBody t.pos
  | .ident "enum" => bump; parseEnumBody t.pos
  | .ident "option" =>
    bump; expectSym "{"; return .optionLit t.pos (← parseBraced t.pos)
  | .ident "logic" =>
    bump; expectSym "{"; return .logicLit t.pos (← parseBraced t.pos)
  | .ident x =>
    if keywords.contains x then perr t s!"unexpected keyword '{x}'"
    bump; return .ident t.pos x
  | _ => perr t s!"unexpected {t.tok.describe}"
end

/-- A function body after `=`: an indented block, a braced block, or an expression. -/
def parseFnBody : PM SExpr := do
  let t ← peekT
  if t.bol then
    if t.col == 0 then perr t "expected an indented function body"
    return .block t.pos (← parseIndented t.col)
  else if t.isSym "{" then bump; parseBraced t.pos
  else parseExpr 0

/-- Skip `<specifier>` lists (`<public>`, `<decides>`, …), returning their names. -/
partial def parseSpecs : PM (List String) := do
  let mut specs := #[]
  repeat
    let t ← peekT
    if t.isSym "<" then
      bump
      let n ← match (← peekT).tok with
        | .ident x => do bump; pure x
        | _ => perr (← peekT) "expected an effect or specifier name"
      expectSym ">"
      specs := specs.push n
    else break
  return specs.toList

/-- A parameter list after its `(`, through the `)`: the parameters, and the
    type parameters of a `where` clause that ends it. -/
partial def parseParamList : PM (Array SParam × Array TParam) := do
  let mut ps := #[]
  if !(← peekT).isSym ")" && !(← peekT).isKw "where" then
    repeat
      let named := (← peekT).isSym "?"
      if named then bump
      let pn ← expectIdent
      expectSym ":"
      let pty ← parseType
      let dflt ← if (← peekT).isSym "=" then do bump; pure (some (← parseExpr 0)) else pure none
      ps := ps.push { name := pn, ty := pty, named, default := dflt }
      if (← peekT).isSym "," then bump else break
  -- `where t₁:type, t₂:subtype(comparable)` ends the parameter list
  let mut tps := #[]
  if (← peekT).isKw "where" then
    bump
    repeat
      let vt ← peekT
      let v ← expectIdent
      expectSym ":"
      let kt ← peekT
      let k ← expectIdent
      let c ← if k == "subtype" then do
          expectSym "("
          let a ← expectIdent
          expectSym ")"
          pure a
        else if k == "type" then pure "type"
        else perr kt s!"expected 'type' or 'subtype(…)' for type parameter {v}, found {kt.tok.describe}"
      tps := tps.push { pos := vt.pos, name := v, constraint := c }
      if (← peekT).isSym "," then bump else break
  expectSym ")"
  return (ps, tps)

/-- The body of a method defined at column `c`: on the following lines,
    indented more than `c`, or inline. -/
def parseFnBodyAt (c : Nat) : PM SExpr := do
  let t ← peekT
  if t.bol then
    if t.col ≤ c then perr t "expected an indented method body"
    return .block t.pos (← parseIndented t.col)
  else if t.isSym "{" then bump; parseBraced t.pos
  else parseExpr c

/-- One item of a class body at column `c`: a field `[var] Name:type [= e]`
    or a method `Name(params)<effects>:type = body`. -/
partial def parseClassItem (c : Nat) :
    PM (Sum ((String × STy × Option SExpr × Bool) × Bool) STop) := do
  let t ← peekT
  -- `block:` runs when an instance is constructed: the method `$block`
  if t.isKw "block" then
    let body ← parseExpr c
    return .inr (.fn t.pos "$block" [] [] [] (.name "void") body)
  let isVar := t.isKw "var"
  if isVar then bump
  let name ← expectIdent
  let pre ← parseSpecs
  if (← peekT).isSym ":" then
    -- a field, `Name<override>:t = e` giving an inherited field a new default
    bump
    let ty ← parseType
    let a ← peekT
    let d ← if a.isSym "=" || a.isSym ":=" then do bump; pure (some (← parseExpr c)) else pure none
    return .inl ((name, ty, d, isVar), pre.contains "override")
  if isVar then perr t "expected a field after var"
  expectSym "("
  let (ps, tps) ← parseParamList
  let effs ← parseSpecs
  expectSym ":"
  let ret ← parseType
  let a ← peekT
  if a.isSym "=" || a.isSym ":=" then
    bump
    return .inr (.fn t.pos name ps.toList tps.toList (pre ++ effs) ret (← parseFnBodyAt c))
  -- no body: an abstract method
  return .inr (.fn t.pos name ps.toList tps.toList (pre ++ effs ++ ["$abstract"]) ret (.block t.pos []))

/-- `class` or `interface` (after the keyword): specifiers, the parents
    `(base, interface₁, …)`, then `:` + items or `{ items }`. -/
partial def parseClassBody (p : Pos) (name : String) (tps : List TParam) (isIface : Bool) : PM STop := do
  let specs ← parseSpecs
  let mut parents := #[]
  if (← peekT).isSym "(" then
    bump
    repeat
      parents := parents.push (← expectIdent)
      if (← peekT).isSym "," then bump else break
    expectSym ")"
  let o ← peekT
  let mut items := #[]
  if o.isSym ":" then
    bump
    let n ← peekT
    if n.isEof || (n.bol && n.col == 0) then
      perr n s!"expected the indented body of {if isIface then "interface" else "class"} {name}"
    let c := n.col
    items ← withBlock n do
      let mut items := #[← parseClassItem c]
      repeat
        let a ← peekT
        checkIndent a
        if a.isSym ";" then bump; items := items.push (← parseClassItem c)
        else if a.bol && a.col == c && !a.isEof then items := items.push (← parseClassItem c)
        else break
      return items
  else if o.isSym "{" then
    bump
    repeat
      let a ← peekT
      if a.isSym "}" then bump; break
      if a.isSym "," || a.isSym ";" then bump; continue
      items := items.push (← parseClassItem 0)
  else perr o s!"expected ':' or '\{' after {if isIface then "interface" else "class"}"
  let fields := items.toList.filterMap fun | .inl (f, _) => some f | .inr _ => none
  let overrides := items.toList.filterMap fun | .inl ((n, _), true) => some n | _ => none
  let methods := items.toList.filterMap fun | .inr m => some m | .inl _ => none
  -- the `block:` clauses, in order, as one method
  let isBlock : STop → Bool := fun | .fn _ "$block" .. => true | _ => false
  let blocks := methods.filterMap fun | .fn _ "$block" _ _ _ _ b => some b | _ => none
  if isIface && !blocks.isEmpty then perr o s!"interface {name} cannot have a block: clause"
  let methods := methods.filter (!isBlock ·) ++
    (if blocks.isEmpty then [] else [.fn p "$block" [] [] [] (.name "void") (.block p blocks)])
  return .classDef p name tps specs parents.toList isIface fields overrides methods

partial def parseTops : PM (List STop) := do
  let mut tops := #[]
  repeat
    let t ← peekT
    if t.isEof then break
    if !t.bol || t.col != 0 then perr t "a top-level definition must start at column 0"
    if t.isKw "using" || (t.isKw "import" && (← peekT 1).isSym "{") then
      -- `using{"relative_path"}` imports a file or directory (#27); other
      -- `using { /Verse.org/… }` module paths are accepted and ignored
      bump
      if (← peekT).isSym "{" then
        if let .str parts := (← peekT 1).tok then
          let path := String.join (parts.filterMap fun | .text s => some s | _ => none)
          modify fun st => { st with imports := st.imports.push (t.pos, path) }
      repeat
        let n ← peekT
        if n.isEof || (n.bol && n.col == 0) then break
        bump
      continue
    let name ← expectIdent
    let pre ← parseSpecs
    let n ← peekT
    -- a constant has the effects of its initialiser (#35)
    if !n.isSym "(" then
      if let some e := pre.find? (["computes", "reads", "writes", "allocates", "transacts", "decides",
          "converges"].contains ·) then
        perr n s!"a constant cannot have the effect specifier <{e}>: it has the effects of its initialiser"
    if n.isSym "(" then
      bump
      let (ps, tps) ← parseParamList
      if pre.contains "constructor" then
        perr n "constructor functions are not supported yet (#11)"
      if (← peekT).isSym ":=" && (← peekT 1).isKw "class" then
        -- `name(t:type, …) := class …`: a parametric class
        bump; bump
        if !tps.isEmpty then perr n "a parametric type takes its parameters without a where clause"
        let tparams ← ps.toList.mapM fun prm => do
          let c ← match prm.named, prm.default, prm.ty with
            | false, none, .name "type" => pure "type"
            | false, none, .app "subtype" [.name c] => pure c
            | _, _, _ => perr n s!"a parameter of a parametric type is written {prm.name}:type or {prm.name}:subtype(…)"
          pure ({ pos := t.pos, name := prm.name, constraint := c } : TParam)
        tops := tops.push (← parseClassBody t.pos name tparams false)
        continue
      if (← peekT).isSym ":=" && (← peekT 1).isKw "struct" then
        -- `name(t:type, …) := struct …`: a parametric struct
        let d ← peekT
        bump
        if !tps.isEmpty then perr d "a parametric type takes its parameters without a where clause"
        let tparams ← ps.toList.mapM fun prm => do
          let c ← match prm.named, prm.default, prm.ty with
            | false, none, .name "type" => pure "type"
            | false, none, .app "subtype" [.name c] => pure c
            | _, _, _ => perr n s!"a parameter of a parametric type is written {prm.name}:type or {prm.name}:subtype(…)"
          pure ({ pos := t.pos, name := prm.name, constraint := c } : TParam)
        match ← parseFnBody with
        | .structDef bp [] fs => tops := tops.push (.const t.pos name none (.structDef bp tparams fs))
        | _ => perr d s!"only structs can be parametric in openverse ({name})"
        continue
      let effs ← parseSpecs
      expectSym ":"
      let ret ← parseType
      let a ← peekT
      if a.isSym "=" || a.isSym ":=" then bump else perr a "expected '=' before the function body"
      tops := tops.push (.fn t.pos name ps.toList tps.toList (pre ++ effs) ret (← parseFnBody))
    else if n.isSym ":=" && (← peekT 1).isKw "interface" then
      bump; bump
      tops := tops.push (← parseClassBody t.pos name [] true)
    else if n.isSym ":=" && (← peekT 1).isKw "class" then
      bump; bump
      tops := tops.push (← parseClassBody t.pos name [] false)
    else if n.isSym ":=" then
      bump
      tops := tops.push (.const t.pos name none (← parseFnBody))
    else if n.isSym ":" then
      bump
      let ty ← parseType
      let a ← peekT
      if a.isSym "=" || a.isSym ":=" then bump else perr a "expected '=' in a constant definition"
      tops := tops.push (.const t.pos name (some ty) (← parseFnBody))
    else perr n s!"expected '(', ':' or ':=' after '{name}'"
  return tops.toList

/-- Parse one expression (for `openverse run FILE do EXPR`). -/
def parseExprText (src : String) : Except String SExpr := do
  let toks ← lexSource src
  (do
    let e ← parseExpr 0
    let t ← peekT
    if !t.isEof then perr t s!"unexpected {t.tok.describe} after the expression"
    return e : PM SExpr).run' { toks }

/-- Parse a source file: its definitions, and the files it imports. `file`
    names it in error positions (empty for the main file). -/
def parseProgramImports (src : String) (file : String := "") :
    Except String (List STop × List (Pos × String)) := do
  let toks ← lexSource src
  let toks := if file.isEmpty then toks else toks.map fun t => { t with file }
  let (tops, st) ← parseTops.run { toks }
  return (tops, st.imports.toList)

/-- Parse a whole Verse source file. -/
def parseProgram (src : String) : Except String (List STop) := do
  let toks ← lexSource src
  parseTops.run' { toks }

end OpenVerse.Front
