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

  Bodies, one rule wherever a construct takes one (`Token.startsBody`): `:`
  and an indented block, the rest of the line, or nothing (an empty body,
  `Token.endsEmptyBody`); `{…}`; or `.` and an expression on its line. A
  value after `=`, `:=` or `=>` that starts a later line is the indented
  block of those lines (`parseValue`). `if`, `for` and `first` take their
  clauses in parentheses, or as such a body (`parseClauses`), then `then`
  or `do` and a branch, or nothing (the clause macros). A construction's
  fields follow its type's name in `{…}` or, after a `:` that ends the
  line, as an indented block (`fieldsFollow`).
-/
import OpenVerse.Front.Lexer
import OpenVerse.Front.Syntax
import OpenVerse.Front.EffectPolicy
import OpenVerse.Front.Choice

namespace OpenVerse.Front

structure PSt where
  toks : Array Token
  pos  : Nat := 0
  /-- The indentation of the enclosing indented blocks, innermost first
      (the top level, `""`, is not on the stack). -/
  blocks : List String := []
  /-- The files imported with `using{"relative_path"}` (#27). -/
  imports : Array (Pos × String) := #[]
  /-- The column of the definitions being parsed: 0 at the top level, the
      body's column in a module (#112). A definition's body is indented more. -/
  topCol : Nat := 0
  /-- The defaults function types write for parameters a caller may omit
      (`?N:t = e`), not yet given out: where, the parameter's name and
      type, the default (#503). -/
  typeDefaults : Array (Pos × String × STy × SExpr) := #[]
  /-- The attributes of the members of the definition being read (a class's
      or an interface's fields and methods, a struct's fields, an enum's
      values), not yet given out: where, the member's place and name, the
      attribute (`Attributes`). -/
  attrs : Array (Pos × String × String × SExpr) := #[]
  /-- The `case` arms marked `@ignore_unreachable`, by their pattern's
      position (Book of Verse tests, `Enum.versetest` 506-592). -/
  ignoredArms : Array Pos := #[]
  /-- A map literal's key is being read, where `k => v` is its entry, not
      a lambda. -/
  inMapKey : Bool := false

abbrev PM := StateT PSt (Except String)

def peekT (k : Nat := 0) : PM Token := do
  let s ← get
  return s.toks[s.pos + k]?.getD (s.toks.back?.getD default)

/-- The column of the first token on the line of token `i`: the line's
    indentation. -/
def lineColAt (i : Nat) : PM Nat := do
  let s ← get
  let some t := s.toks[i]? | return 0
  let mut j := i
  while j > 0 && (s.toks[j - 1]?.map fun u => u.line == t.line && u.file == t.file) == some true do
    j := j - 1
  return (s.toks[j]?.map (·.col)).getD 0

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

def Token.identName? (t : Token) : Option String :=
  match t.tok with
  | .ident x => if keywords.contains x then none else some x
  | _ => none

/-- A clause macro `kw{…}` has no body: refuse what looks like one after it
    (a `:`, a `{` even on the next line, `then`, or `else` after `assert`). -/
def noMacroBody (kw : String) (n : Token) (hint : String) : PM Unit := do
  if n.isSym ":" || n.isSym "{" || n.isKw "then" || (kw == "assert" && n.isKw "else") then
    perr n s!"'{kw}\{…}' has no body: {hint}"

/-- The clauses of a clause macro whose value is that of its last clause
    (`if{…} else`, `for{…}`, `first{…}`): the clauses, the last bound to a
    fresh name unless it is a binding already, and that name. -/
def clausesValue (cs : List SExpr) : List SExpr × SExpr :=
  match cs.getLast? with
  | none => ([], .tuple { line := 0, col := 0 } [])
  | some (.decl q x _ _ _) => (cs, .ident q x)
  | some (.gen q x _ _) => (cs, .ident q x)
  | some e =>
    let q := e.pos
    let v := s!"$v{q.line}_{q.col}"
    (cs.dropLast ++ [.decl q v none false e], .ident q v)

/-- `t` cannot continue an expression whose statement column is `stop`. -/
def Token.offside (t : Token) (stop : Nat) : Bool := (t.bol && t.col ≤ stop) || t.isEof

/-- After the `:` of a body whose construct is at column `col`: the body is
    empty when its next token starts a line no deeper than `col`, or ends
    the file. A body after `:` may be empty wherever one may be written,
    as `{}` may (Book of Verse tests: `class<concrete>:` with nothing, an
    empty `then:`). -/
def Token.endsEmptyBody (n : Token) (col : Nat) : Bool := n.offside col

/-- A body starts with `:` (a block, or an expression on its line), `{`, or
    `.` and an expression on its line (Book of Verse tests: `if (1 < 2).
    set Num = 42`, `for(n:nums). set curSum += n`, `spawn. F()`). -/
def Token.startsBody (t : Token) : Bool := t.isSym ":" || t.isSym "{" || t.isSym "."

/-- After a separator in an indented block at column `c`: whether `u` starts
    the block's next item, which it does unless it starts a line that ends
    the block, or ends the file. A `;` may end a line (Book of Verse tests:
    `DataMemberX<final>: int = 0;` as a class's last field). -/
def Token.continuesBlock (u : Token) (c : Nat) : Bool := !u.isEof && !(u.bol && u.col < c)

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

/-- The modules of a scope, `scoped{A, B.C}` (after `scoped`): each a name
    or a dotted path of names, or a package's path, which `resolveModules`
    refuses (Book of Verse ch. 12, "Scoped"). -/
partial def parseScopeRefs : PM (List String) := do
  expectSym "{"
  let mut refs := #[]
  repeat
    let t ← peekT
    if t.isSym "}" then bump; break
    if t.isSym "," then bump; continue
    match t.tok with
    | .path q => bump; refs := refs.push q
    | _ =>
      let mut r ← expectIdent
      while (← peekT).isSym "." do bump; r := r ++ "." ++ (← expectIdent)
      refs := refs.push r
  return refs.toList

/-- Read specifier lists before deciding their declaration role. An access
    level is `<scoped{A, B}>`, kept as `scoped{A,B}`, or a name of one a
    module defines, `<S>` or `<M.S>` (Book of Verse ch. 12, "Scoped"). -/
partial def parseSpecs : PM (List String) := do
  let mut specs := #[]
  repeat
    let t ← peekT
    if t.isSym "<" then
      bump
      let mut n ← match (← peekT).tok with
        | .ident x => do bump; pure x
        | _ => perr (← peekT) "expected an effect or specifier name"
      if n == "scoped" && (← peekT).isSym "{" then
        n := s!"scoped\{{",".intercalate (← parseScopeRefs)}}"
      -- (`<getter(GetX)>`, `<setter(SetX)>`: a field's accessors, Book of
      -- Verse ch. 10, "Fields with Accessors", kept as `getter(GetX)`)
      else if (n == "getter" || n == "setter") && (← peekT).isSym "(" then
        bump
        n := s!"{n}({← expectIdent})"
        expectSym ")"
      else
        while (← peekT).isSym "." do bump; n := n ++ "." ++ (← expectIdent)
      expectSym ">"
      specs := specs.push n
    else break
  return specs.toList


/-- A function's access specifier is written on its name, `F<public>(…)`, not
    among its effects after the parameters (Book of Verse ch. 12); there, a
    name that is no specifier openverse knows names no access level either. -/
def accessOnName (p : Pos) (name : String) (effs : List String) : PM Unit := do
  if let some sp := effs.find? EffectPolicy.isAccess then
    throw s!"{p.show}: <{sp}> after the parameters of {name}: an access specifier is written on the name, {name}<{sp}>(…)"
  if let some sp := effs.find? (!EffectPolicy.known ·) then
    throw s!"{p.show}: unknown or unsupported function specifier <{sp}> on {name} (#494)"


def cmpOps : List String := ["=", "<>", "<", "<=", ">", ">="]


/-- At a `(` (the token `off` ahead): the qualifier of `(i:)M`, `(M.i:)M`
    (#70, #112), `(local:)X` or a path's `(/a/b:)X`, if one starts there, and
    how many tokens it takes (through the `:)`). What it names is
    `resolveModules`' to decide. -/
def peekQual (off : Nat := 0) : PM (Option (String × Nat)) := do
  if !(← peekT off).isSym "(" then return none
  if let .path q := (← peekT (off + 1)).tok then
    if (← peekT (off + 2)).isSym ":" && (← peekT (off + 3)).isSym ")" then return some (q, 4)
    return none
  let some q0 := (← peekT (off + 1)).identName? | return none
  let mut q := q0
  let mut k := 2
  while (← peekT (off + k)).isSym "." && ((← peekT (off + k + 1)).identName?).isSome do
    q := q ++ "." ++ ((← peekT (off + k + 1)).identName?).getD ""
    k := k + 2
  if (← peekT (off + k)).isSym ":" && (← peekT (off + k + 1)).isSym ")" then return some (q, k + 2)
  return none

/-- The name after a qualifier `(q:)`: an identifier, or a keyword, which a
    qualifier lets an enum's value take (Book of Verse ch. 9: `(e:)for`). -/
def expectQualifiedName : PM String := do
  let t ← peekT
  match t.tok with
  | .ident x => bump; return x
  | _ => perr t s!"expected an identifier after the qualifier, found {t.tok.describe}"

/-- A definition's name: `X`, or `(q:)X` as written, qualified (the
    qualifier names where it is defined, `resolveModules` checks). -/
def expectBinder : PM String := do
  if let some (q, k) ← peekQual then
    for _ in [0:k] do bump
    return s!"({q}:){← expectIdent}"
  expectIdent

/-- A block's statements, each destructuring's declarations spliced in
    (`parseStmt`). -/
def spliceStmts (es : List SExpr) : List SExpr := es.flatMap fun
  | .app _ (.ident _ "$destructure") ds false => ds
  | e => [e]

/-- Whether a construction's fields start here: a `{` on this line, or a
    `:` that ends its line before an indented block (an archetype block,
    Book of Verse tests: `X := class1:` and `Property1 := 0` indented). -/
def fieldsFollow (stop : Nat) : PM Bool := do
  let b ← peekT
  if b.bol then return false
  if b.isSym "{" then return true
  let n ← peekT 1
  return b.isSym ":" && n.bol && n.col > stop && !n.isEof

/-- Whether a type is written as a value can be: a name, or a name applied
    to such (`c`, `box(int)`), which may be a constant's or a call. -/
partial def STy.couldBeValue : STy → Bool
  | .name n => !keywords.contains n && !n.startsWith "$"
  | .app n ts => !n.startsWith "$" && !n.startsWith "?" && ts.all STy.couldBeValue
  | _ => false

/-- A `profile` block (`parsePrimary`): its tag, checked as a string, then
    its body, whose value is the block's. A body with nothing in it is
    refused (Book of Verse tests, profile_simple.versetest: 3560). -/
def profileOf (p : Pos) (tag : Option SExpr) (body : SExpr) : PM SExpr := do
  if body == .block body.pos [] then throw s!"{p.show}: profile needs a body: the code it measures"
  -- (the tag, or "", in `$profileL_C`, which marks the block: `checkProfiles`)
  let tag := tag.getD (.str p [])
  return .block p [SExpr.decl p s!"{profilePrefix}{p.line}_{p.col}" (some (.name "string")) false tag, body]

/-- The name of a parameter written with no name, `(:t)`, `$unnamedI`: an
    extension method's receiver so written is `$receiver`
    (`parseExtensionHead?`). -/
def unnamedPrefix : String := "$unnamed"

/-- At a `(`: whether its parameters end with the `)` right before a `=>`,
    a lambda's (`some true`), or not (`none`). -/
def lambdaAhead? : PM (Option Bool) := do
  if !(← peekT).isSym "(" then return none
  let st ← get
  let mut depth : Nat := 0
  let mut i := st.pos
  while h : i < st.toks.size do
    let u := st.toks[i]
    if u.isSym "(" || u.isSym "[" || u.isSym "{" then depth := depth + 1
    else if u.isSym ")" || u.isSym "]" || u.isSym "}" then
      depth := depth - 1
      if depth == 0 then
        return if (st.toks[i + 1]?.map (fun v => v.isSym "=>" && !v.bol)) == some true then some true else none
    else if u.isEof then return none
    i := i + 1
  return none

/-- The macros whose names a specifier may follow in the Book's grammar,
    `for<par>(…)`, `array <computes> {…}`, which none admits (Book of Verse
    tests, `InvalidAttributeLocations.versetest`: 3604). -/
def macroKeywords : List String :=
  ["for", "case", "loop", "defer", "block", "branch", "spawn", "sync", "race", "rush", "array", "map",
   "option", "logic", "external", "if"]

/-- The place a definition is at, for its attributes (`Attributes`). -/
def STop.attrPlace : STop → String
  | .fn _ _ _ _ specs .. => if specs.any (constructorSpec? · |>.isSome) then "constructor" else "function"
  | .const _ n _ _ v =>
    if (moduleMarker? n).isSome then "module" else match v with
    | .structDef .. => "struct"
    | .enumDef .. => "enum"
    | .typeAlias .. | .refineDef .. => "alias"
    | .app _ (.ident _ h) _ _ => if h == scopeHead then "scope" else "data"
    | _ => "data"
  | .classDef _ _ _ _ _ _ isI .. => if isI then "interface" else "class"

/-- The name an attribute record gives a definition (`attrPlace`). -/
def STop.attrName : STop → String
  | .fn _ n .. | .classDef _ n .. => n
  | .const _ n .. => (moduleMarker? n).getD n

/-- A definition with the specifier `sp` added to those of its name. -/
def STop.addSpec (sp : String) : STop → STop
  | .fn p n ps tps specs r b => .fn p n ps tps (specs ++ [sp]) r b
  | .const p n specs t v => .const p n (specs ++ [sp]) t v
  | .classDef p n ns tps specs ps i fs ms => .classDef p n (ns ++ [sp]) tps specs ps i fs ms

/-- The record of attribute `e`, written at `p` on the definition `target`
    at `place`, in the scope `pfx`: a constant `$attr:L_C` whose specifiers
    are the place and the target, which `Attributes.apply` reads and removes. -/
def attrTop (pfx : String) (p : Pos) (place target : String) (e : SExpr) : STop :=
  .const p s!"{pfx}{attrPrefix}{p.line}_{p.col}{if p.file.isEmpty then "" else "_" ++ p.file}" [place, target] none e

/-- `tops` with the attributes `attrs` given to the first definition from
    index `start` on (past the markers of its qualifier and the defaults its
    function types write): `@name` among the specifiers of its name, and
    the records (`attrTop`) after it. -/
def attachAttrs (tops : Array STop) (start : Nat) (attrs : List (Pos × SExpr)) (pfx : String) :
    Except String (Array STop) := do
  let some i := (List.range (tops.size - start)).map (· + start) |>.find? (fun i => !tops[i]!.isBesideMarker)
    | let p := (attrs.head?.map (·.1)).getD {line := 0, col := 0}
      throw s!"{p.show}: an attribute is followed by the definition it is on"
  let d := tops[i]!
  let d := attrs.foldl (fun d (_, e) => d.addSpec ("@" ++ e.attrHead)) d
  let recs := attrs.map fun (p, e) => attrTop pfx p d.attrPlace d.attrName e
  return (tops.set! i d) ++ recs.toArray

mutual
partial def parseType : PM STy := do
  let t ← parseTypeAtom
  -- `t->r`: a function type of one parameter, or of a tuple's elements
  -- (they flatten into parameters, Book of Verse ch. 6), #210
  if (← peekT).isSym "->" && !(← peekT).bol then
    bump
    let r ← parseType
    return match t with
      | .tup ts => .fn ts [] r
      | _ => .fn [t] [] r
  return t

partial def parseTypeAtom : PM STy := do
  let t ← peekT
  -- `^t`: a pointer type (Book of Verse tests, Pointers.versetest), which
  -- the Book's chapters do not define: `$pointer(t)`, refused
  -- (`Attributes.apply`)
  if t.isSym "^" then
    bump
    return .app pointerTypeHead [← parseTypeAtom]
  -- `type{_(:t₁, …)<effects>:r}`: a function type (#210)
  if t.identName? == some "type" && (← peekT 1).isSym "{" && (← peekT 2).identName? == some "_" &&
      (← peekT 3).isSym "(" then
    bump; bump; bump
    let ty ← parseFnSig
    expectSym "}"
    return ty
  -- `(/Verse.org/Verse:)int`: a type a path qualifies, `(/p:)c`
  if t.isSym "(" then
    if let .path q := (← peekT 1).tok then
      if (← peekT 2).isSym ":" && (← peekT 3).isSym ")" && ((← peekT 4).identName?).isSome then
        for _ in [0:4] do bump
        return .name s!"({q}:){← expectIdent}"
  -- `(M:)c`: the type `M.c` (#147)
  if t.isSym "(" && ((← peekT 1).identName?).isSome then
    let mut q := ((← peekT 1).identName?).getD ""
    let mut k := 2
    while (← peekT k).isSym "." && ((← peekT (k + 1)).identName?).isSome do
      q := q ++ "." ++ ((← peekT (k + 1)).identName?).getD ""
      k := k + 2
    if (← peekT k).isSym ":" && (← peekT (k + 1)).isSym ")" && ((← peekT (k + 2)).identName?).isSome then
      for _ in [0:k + 2] do bump
      let c ← expectIdent
      return .name s!"{q}.{c}"
  -- `(t)`: a type in parentheses, `?(int->int)` (#210)
  if t.isSym "(" then
    bump
    let ty ← parseType
    expectSym ")"
    return ty
  -- (`->` binds loosest: `[]int->int` takes an array, #210)
  if t.isSym "[" then
    bump
    if (← peekT).isSym "]" then bump; return .arr (← parseTypeAtom)
    let k ← parseType
    expectSym "]"
    return .map k (← parseTypeAtom)
  else if t.isSym "?" then
    bump; return .opt (← parseTypeAtom)
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
    | some n0 =>
      bump
      -- `M.c`: a type of module `M` (#112)
      let mut n := n0
      while (← peekT).isSym "." && ((← peekT 1).identName?).isSome && !(← peekT).bol do
        bump; n := n ++ "." ++ (← expectIdent)
      if (← peekT).isSym "(" && !(← peekT).bol then
        -- `pair(int, string)`: a parametric struct applied to type arguments
        -- (a `(` starting a line starts the next item, such as `(i:)M`)
        bump
        -- (`event()`: an event without a value, `event(void)`, #156)
        if (← peekT).isSym ")" && (n == "event" || n == "sticky_event") then
          bump; return .app n [.name "void"]
        -- (`subscribable_event()`: one without a value, whose functions take
        -- none, the concurrency prelude's `$subev0`, #220)
        if (← peekT).isSym ")" && n == "subscribable_event" then
          bump; return .name "$subev0"
        -- (`c1()`: no type arguments, the type `c1`)
        if (← peekT).isSym ")" then bump; return .name n
        let mut ts := #[← parseType]
        while (← peekT).isSym "," do bump; ts := ts.push (← parseType)
        expectSym ")"
        return .app n ts.toList
      return .name n
    | none => perr t s!"expected a type, found {t.tok.describe}"

/-- A function's signature as a type, from its `(`: `(:t₁, …)<effects>:r`,
    as `type{_…}` and a parameter `F(:t₁, …):r` write it (#210). `?N:t` is a
    named parameter, whose name is part of the type, and `?N:t = e` one a
    caller may omit: the type does not include `e` (Book of Verse ch. 6),
    which is kept to be checked (`PSt.typeDefaults`, #503). -/
partial def parseFnSig : PM STy := do
  expectSym "("
  let mut ps := #[]
  if !(← peekT).isSym ")" then
    repeat
      if (← peekT).isSym "?" then
        bump
        let n ← expectIdent
        expectSym ":"
        let t ← parseType
        let d ← peekT
        let optional := d.isSym "="
        if optional then
          bump
          let e ← parseExpr 0
          modify fun st => { st with typeDefaults := st.typeDefaults.push (d.pos, n, t, e) }
        ps := ps.push (STy.namedParam n optional t)
      else
        -- (a positional parameter may be named, `X:t`, or written as a
        -- function's signature, `F(:t):u`; the name is not part of the type)
        if ((← peekT).identName?).isSome && (← peekT 1).isSym "(" then
          bump; ps := ps.push (← parseFnSig)
        else
          if ((← peekT).identName?).isSome && (← peekT 1).isSym ":" then bump
          expectSym ":"
          ps := ps.push (← parseType)
      if (← peekT).isSym "," then bump else break
  expectSym ")"
  let mut effs := #[]
  while (← peekT).isSym "<" do
    bump
    effs := effs.push (← expectIdent)
    expectSym ">"
  expectSym ":"
  return .fn ps.toList effs.toList (← parseType)

/-- An attribute, at its `@` (Book of Verse ch. 12, "Annotations and
    Metadata"; its tests, `Attributes.versetest`, `TimSyntax.versetest`): a
    name, perhaps dotted (`@a.bb`), then its arguments `(…)` right after it,
    or its fields `{…}` on its line (`@available {MinUploadedAtFNVersion :=
    3800}`), or both (`@attr(a:=1){b:=1}`, kept as `$attrCall`). A space, a
    new line or another attribute follows it: `@doc;`, `@doc:foo` and
    `X:int=@doc()4` are errors. -/
partial def parseAttr : PM SExpr := do
  let a ← peekT
  bump
  let t ← peekT
  let n0 ← match t.tok with
    | .ident x => do bump; pure x
    | _ => perr t s!"expected the name of an attribute after '@', found {t.tok.describe}"
  let p := a.pos
  let mut head : SExpr := .ident p n0
  let mut name := n0
  while (← peekT).isSym "." && !(← peekT).spaced do
    bump
    let m ← expectIdent
    head := .member p head m
    name := name ++ "." ++ m
  let mut e := head
  let o ← peekT
  if o.isSym "(" && !o.spaced then
    bump
    e := .app p head (← parseArgs ")") false
  let b ← peekT
  if b.isSym "{" && !b.bol then
    bump
    let fs ← parseItems "}" true
    e := match e with
      | .app .. => .app p (.ident p attrCallHead) [e, .construct p name [] fs] false
      | _ => .construct p name [] fs
  let n ← peekT
  if !(n.isSym "@" || n.spaced) then
    perr n s!"an attribute is followed by a space, a new line or another attribute, not {n.tok.describe} (Book of Verse tests, Attributes.versetest)"
  return e

/-- The attributes from here on, each at its `@`, in order. -/
partial def parseAttrs : PM (List (Pos × SExpr)) := do
  let mut attrs := #[]
  while (← peekT).isSym "@" do
    let p := (← peekT).pos
    attrs := attrs.push (p, ← parseAttr)
  return attrs.toList

/-- Lowest precedence: declarations, `set`, ranges. -/
partial def parseExpr (stop : Nat) : PM SExpr := do
  let t ← peekT
  let t1 ← peekT 1
  -- `@ignore_unreachable e` is `e`, whose position is recorded: no warning
  -- of code never reached follows it (`Reachability`), and a `case` arm
  -- may be one never reached (`parseCase`); other attributes on an
  -- expression or a local definition are refused (`Refused.exprAttribute`,
  -- Book of Verse tests: 3604)
  if t.isSym "@" then
    let attrs ← parseAttrs
    let e ← parseExpr stop
    -- (the refusal names the first attribute that is not `@ignore_unreachable`, where it is)
    let some (p, a) := attrs.find? (fun | (_, .ident _ "ignore_unreachable") => false | _ => true)
      | -- (recorded for the warnings of code never reached, `Reachability`)
        modify fun st => { st with ignoredArms := st.ignoredArms.push e.pos }
        return e
    return refusedForm p (.exprAttribute a.attrHead) (attrs.map (·.2) ++ [e])
  if t.isKw "var" then
    bump
    let n ← expectBinder
    expectSym ":"
    let ty ← parseType
    let a ← peekT
    if a.isSym "=" || a.isSym ":=" then bump else perr a "expected '=' after var declaration"
    return .decl t.pos n (some ty) true (← parseValue stop)
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
    return .set t.pos lhs op (← parseValue stop)
  else if t.identName?.isSome && t1.isSym ":=" then
    bump; bump
    return .decl t.pos t.identName?.get! none false (← parseValue stop)
  else if let some (q, k) ← peekQual then
    -- `(local:)X := e`, `(local:)X:t = e`: a qualified local's definition
    -- (its qualifier is `resolveModules`' to check); otherwise a use
    let n ← peekT k
    let n1 ← peekT (k + 1)
    if n.identName?.isNone || !(n1.isSym ":=" || (n1.isSym ":" && !(← peekT (k + 2)).bol)) then
      return ← parseRange stop
    let saved ← get
    for _ in [0:k + 2] do bump
    let name := s!"({q}:){n.identName?.get!}"
    if n1.isSym ":=" then return .decl t.pos name none false (← parseValue stop)
    let ty ← parseType
    let a ← peekT
    if a.isSym "=" || a.isSym ":=" then
      bump
      return .decl t.pos name (some ty) false (← parseValue stop)
    set saved
    parseRange stop
  else if t.identName?.isSome && t1.isSym ":" && !(← peekT 2).bol then
    -- (a typed declaration has its type on the line of its `:`; `sync:`
    -- and the like start an indented block)
    let saved ← get
    let typed ← (do
        bump; bump
        let ty ← parseType
        let a ← peekT
        if a.isSym "=" || a.isSym ":=" then bump; return some ty else return none)
      <|> pure none
    match typed with
    | some ty => return .decl t.pos t.identName?.get! (some ty) false (← parseValue stop)
    | none => set saved; parseRange stop
  else parseRange stop

/-- A value after `=`, `:=` or `=>`: an expression, or, when it starts a
    later line deeper than `stop`, the indented block of those lines, as a
    function's body after `=` is (Book of Verse tests: `Value :=` and an
    indented `1`, `2`, `3` is `3`). A block of one item is that item. -/
partial def parseValue (stop : Nat) : PM SExpr := do
  let t ← peekT
  if t.bol && t.col > stop && !t.isEof then
    match ← parseIndented t.col with
    | [e] => return e
    | es => return .block t.pos es
  parseExpr stop

partial def parseRange (stop : Nat) : PM SExpr := do
  -- a lambda, `(X:int) => X`, `(a, b) => c`, `a => b` (Book of Verse
  -- tests, Literals/Function.versetest: "Lambdas should be parsed, but
  -- produce an error if used outside of a map literal"), but where a map
  -- literal's key is read: a nested function, refused (`Attributes.apply`)
  let t ← peekT
  if !(← get).inMapKey then
    if let some lam ← lambdaAhead? then
      if lam then
        -- (its parameters: through the `)` before `=>`, which they are
        -- not read for, as the lambda is refused)
        let mut depth : Nat := 0
        repeat
          let u ← peekT
          if u.isSym "(" || u.isSym "[" || u.isSym "{" then depth := depth + 1
          if u.isSym ")" || u.isSym "]" || u.isSym "}" then depth := depth - 1
          bump
          if depth == 0 then break
        let a ← peekT
        bump
        let n ← peekT
        let body ← if n.offside stop || n.isSym ")" || n.isSym "," then pure (SExpr.block a.pos []) else parseValue stop
        return refusedForm t.pos .lambda [body]
  let a ← parseOr stop
  if (← peekT).isSym "=>" && !(← peekT).offside stop && !(← get).inMapKey &&
      (match a with | .ident .. | .tuple .. => true | _ => false) then
    let q ← peekT
    bump
    let n ← peekT
    let body ← if n.offside stop || n.isSym ")" || n.isSym "," then pure (SExpr.block q.pos []) else parseValue stop
    return refusedForm t.pos .lambda [a, body]
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
  let mut a ← parseNot stop
  repeat
    let t ← peekT
    if t.isKw "and" && !t.offside stop then
      bump; a := .andE t.pos a (← parseNot stop)
    else break
  return a

/-- `not e`, below the comparisons and above `and`: `not X = Y` is
    `not (X = Y)`. -/
partial def parseNot (stop : Nat) : PM SExpr := do
  let t ← peekT
  if t.isKw "not" then
    bump; return .notE t.pos (← parseNot stop)
  parseCmp stop

partial def parseCmp (stop : Nat) : PM SExpr := do
  let a ← parseChoice stop
  let mut rest := #[]
  repeat
    let t ← peekT
    match t.tok with
    | .sym op =>
      if cmpOps.contains op && !t.offside stop then
        bump; rest := rest.push (op, ← parseChoice stop)
      else break
    | _ => break
  if rest.isEmpty then return a else return .cmp a.pos a rest.toList

/-- A choice `a₁ | a₂ | …` (#208), below the comparisons and above `+`:
    `X = 1 | 2` is `X = (1 | 2)`. Its position is its first `|`'s. -/
partial def parseChoice (stop : Nat) : PM SExpr := do
  let a ← parseAdd stop
  let mut alts := #[a]
  let mut pos : Option Pos := none
  repeat
    let t ← peekT
    if t.isSym "|" && !t.offside stop then
      if pos.isNone then pos := some t.pos
      bump; alts := alts.push (← parseAdd stop)
    else break
  match pos with
  | none => return a
  | some p => return Choice.mk p alts.toList

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
  else parsePostfix stop

/-- The dotted name a chain of identifiers `A.B.c` spells (a module's
    class or struct, #112). -/
partial def SExpr.dottedName? : SExpr → Option String
  | .ident _ n => some n
  -- (`(M:)c(t){…}`: a module's parametric class, as `M.c(t){…}`)
  | .member _ (.ident _ "Self") m => match splitQual? m with
    | some (q, x) => if q.startsWith "/" || q == "local" then none else some s!"{q}.{x}"
    | none => some s!"Self.{m}"
  | .member _ x m => if m.startsWith "(" then none else (SExpr.dottedName? x).map (· ++ "." ++ m)
  | _ => none

partial def parsePostfix (stop : Nat) : PM SExpr := do
  let mut e ← parsePrimary stop
  repeat
    let t ← peekT
    if t.offside stop || t.bol then break
    if t.isSym "(" then
      -- `pair(int, string){…}`: type arguments then a struct value; otherwise a call
      let cons? ← match e.dottedName? with
        | some n => do
          let saved ← get
          let r ← (do
              bump
              -- (`event(){}`: an event without a value, `event(void)`, #156)
              let mut ts : Array STy := #[]
              let mut n := n
              if (← peekT).isSym ")" && (n == "event" || n == "sticky_event") then
                ts := #[.name "void"]
              -- (`subscribable_event(){}`, #220)
              else if (← peekT).isSym ")" && n == "subscribable_event" then
                n := "$subev0"
              -- (`c1(){…}`: no type arguments, `c1{…}`)
              else if (← peekT).isSym ")" then
                pure ()
              else
                ts := #[← parseType]
                while (← peekT).isSym "," do bump; ts := ts.push (← parseType)
              expectSym ")"
              if ← fieldsFollow stop then return some (n, ts.toList)
              return none) <|> pure none
          if r.isNone then set saved
          pure r
        | _ => pure none
      match cons? with
      | some (n, ts) => e := .construct t.pos n ts (← parseFields)
      | none => bump; e := .app t.pos e (← parseArgs ")") false
    else if (t.isSym "{" || t.isSym ":") && e.dottedName?.isSome && (← fieldsFollow stop) then
      -- `point{X := 1, Y := 2}` or `point:` and the fields indented: a
      -- struct value (`M.point{…}`: a module's)
      let name := e.dottedName?.getD ""
      e := .construct t.pos name [] (← parseFields)
    else if t.isSym "[" then
      bump; e := .app t.pos e (← parseArgs "]") true
    else if t.isSym "." then
      bump
      -- `X.(i:)M`: the method `M` of `X` as an `i` (a qualified call)
      if let some (q, k) ← peekQual then
        for _ in [0:k] do bump
        e := .member t.pos e s!"({q}:){← expectIdent}"
      else
        e := .member t.pos e (← expectIdent)
    else if t.isSym "?" then
      bump; e := .query t.pos e
    else if t.isSym "^" then
      -- `e^`, a pointer's dereference (Book of Verse tests, Roundtrip/
      -- Operators.versetest), which the Book's chapters do not define
      bump
      e := refusedForm t.pos .pointerDeref [e]
    else if t.isKw "of" || t.isKw "at" then
      -- `F of X` is `F(X)` and `F at X` is `F[X]` (Book of Verse tests,
      -- `Operators/Of.versetest`, `Operators/At.versetest`): the argument
      -- is `{…}`, the arguments in braces, or a body after `:` or `.`, or
      -- an operand, `F of 42`, `F of array: …`, `F of (4;5)`
      bump
      let o ← peekT
      let args ← if o.isSym "{" && !o.bol then do bump; parseArgs "}"
        else if (o.isSym ":" || o.isSym ".") && !o.bol then do pure [← parseBody stop]
        else do pure [← parseUnary stop]
      e := .app t.pos e args (t.isKw "at")
    else break
  return e

/-- Comma-separated arguments up to `close` (consumed), each perhaps a
    `;` sequence. Newlines are whitespace. -/
partial def parseArgs (close : String) : PM (List SExpr) := parseItems close false

/-- A construction's field initializers, at the `{` or `:` that
    `fieldsFollow` found: up to the `}`, separated by commas, or by `;` and
    new lines, not both (Book of Verse tests, error 3552); or the indented
    block after the `:` (an archetype block). -/
partial def parseFields : PM (List SExpr) := do
  let b ← peekT
  bump
  if b.isSym "{" then parseItems "}" true else spliceStmts <$> parseIndentedWith parseStmt (← peekT).col

/-- Items up to `close` (consumed), separated by commas, or, with `lines`,
    by `;` and new lines instead (a construction's fields, an array's
    elements); new lines are whitespace otherwise. -/
partial def parseItems (close : String) (lines : Bool) : PM (List SExpr) := do
  if (← peekT).isSym close then bump; return []
  -- `?Name := e` is a named argument, kept as a declaration of `?Name`
  let arg : PM SExpr := do
    let t ← peekT
    if t.isSym "?" && (← peekT 1).identName?.isSome && (← peekT 2).isSym ":=" then
      bump
      let n ← expectIdent
      bump
      return .decl t.pos ("?" ++ n) none false (← parseExpr 0)
    let e ← parseExpr 0
    -- (an argument may be a sequence, `F(1; 2)`, whose last value is passed,
    -- Book of Verse ch. 1, "Semicolons vs Commas")
    if lines || !(← peekT).isSym ";" then return e
    let mut es := #[e]
    while (← peekT).isSym ";" do bump; es := es.push (← parseExpr 0)
    return .block t.pos es.toList
  let mut args := #[← arg]
  let mut commas := false
  let mut semis := false
  repeat
    let t ← peekT
    if t.isSym close then bump; break
    if t.isSym "," then bump; commas := true
    else if lines && (t.isSym ";" || (t.bol && !t.isEof)) then
      if t.isSym ";" then bump
      semis := true
    else perr t s!"expected ',' or '{close}', found {t.tok.describe}"
    if commas && semis then perr t "cannot mix ',' and ';' separators"
    -- (a `;` or new line may end the items: `}` on its own line)
    if semis && (← peekT).isSym close then bump; break
    args := args.push (← arg)
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

/-- A parenthesized expression after its `(`, at `p`: one item, a tuple
    (items separated by `,`) or a sequence (by `;` or new lines). -/
partial def parseParenExpr (p : Pos) : PM SExpr := do
  let (items, commas) ← parseParenItems
  match items with
  | [] => return .tuple p []
  | [e] => return e
  | es => return if commas then .tuple p es else .block p es

/-- A statement of a block: an expression, or a tuple's destructuring
    `(X:t, _, Z:u) = e` (Book of Verse tests, Tuple.versetest), when at
    least one element is named: `e` in a fresh name, then each named
    element bound in order, `_` skipping one. Its declarations are spliced
    into the block (`spliceStmts`), so the names are the block's. -/
partial def parseStmt (c : Nat) : PM SExpr := do
  let t ← peekT
  if t.isSym "(" then
    let saved ← get
    let pattern? ← (do
        bump
        let mut items : Array (Option (String × STy)) := #[]
        repeat
          if (← peekT).identName? == some "_" then bump; items := items.push none
          else
            let x ← expectIdent
            expectSym ":"
            items := items.push (some (x, ← parseType))
          if (← peekT).isSym "," then bump else break
        expectSym ")"
        let a ← peekT
        if !(a.isSym "=" || a.isSym ":=") || items.all (·.isNone) then throw "not a destructuring"
        bump
        return some items) <|> pure none
    if let some items := pattern? then
      let tuple := s!"$tuple{t.line}_{t.col}"
      let e ← parseValue c
      let p := t.pos
      let names := items.toList.zipIdx.filterMap fun (it, i) => it.map fun (x, ty) =>
        SExpr.decl p x (some ty) false (.app p (.ident p tuple) [.int p i] false)
      return .app p (.ident p "$destructure") (.decl p tuple none false e :: names) false
    set saved
  parseExpr c

/-- A statement of a block, and the ones a comma on its line joins to it
    (the Book of Verse, ch. 1, "Semicolons vs Commas": in a block, `;` and
    new lines make a sequence and `,` a tuple; its tests,
    `SemicolonsVsCommas.versetest` 70, 95, 100: `Value :=` and the line
    `1, 2, 3` is `(1, 2, 3)`, `{3, X}` and `option{1, 2}` hold a tuple): the
    tuple of them. When every one is a definition, they are the block's
    definitions in turn (ch. 1: "semicolons and commas are interchangeable
    as separators between definitions", `X:int = 0, Y:int = 0`). When some
    are, each element in order, a definition as itself and any other bound
    to a name of its own, then the tuple of their values, so a definition is
    visible to the elements after it and after the group: `(V := X, V > 0,
    V)` is `V := X; T := V > 0; (V, T, V)` (a `var`'s value is taken where
    it is defined). A comma that starts a line is not the group's: it ends
    the block, and belongs to the list around it. -/
partial def parseStmtTuple (c : Nat) : PM SExpr := do
  let t ← peekT
  let first ← parseStmt c
  let comma : PM Bool := do
    let n ← peekT
    return n.isSym "," && !n.bol
  if !(← comma) then return first
  let mut items := #[first]
  while ← comma do
    bump
    items := items.push (← parseStmt c)
  let isDecl : SExpr → Bool := fun
    | .decl .. | .app _ (.ident _ "$destructure") _ false => true
    | _ => false
  let es := items.toList
  if es.all isDecl then return .app t.pos (.ident t.pos "$destructure") (spliceStmts es) false
  if !es.any isDecl then return .tuple t.pos es
  let name (i : Nat) : String := s!"$comma{t.line}_{t.col}_{i}"
  let parts := es.zipIdx.map fun (e, i) => match e with
    | .decl q n _ false _ => ([e], SExpr.ident q (bareName n))
    | .decl q n _ true _ => ([e, .decl q (name i) none false (.ident q (bareName n))], .ident q (name i))
    | .app q (.ident _ "$destructure") ds@(.decl _ tup _ _ _ :: _) false => (ds, .ident q tup)
    | e => ([.decl e.pos (name i) none false e], .ident e.pos (name i))
  return .app t.pos (.ident t.pos "$destructure")
    (parts.flatMap (·.1) ++ [.tuple t.pos (parts.map (·.2))]) false

/-- An indented block whose items start at column `c`, each read by `item`. -/
partial def parseIndentedWith (item : Nat → PM SExpr) (c : Nat) : PM (List SExpr) := do
  withBlock (← peekT) do
    let mut stmts := #[← item c]
    repeat
      let t ← peekT
      checkIndent t
      if t.isSym ";" then
        bump
        if (← peekT).continuesBlock c then stmts := stmts.push (← item c)
      else if t.isEof then break
      else if t.bol && t.col == c && !t.isKw "else" && !t.isKw "then" && !t.isSym "}" && !t.isSym ")" then
        stmts := stmts.push (← item c)
      else if t.bol && t.col > c then perr t "unexpected indentation"
      else break
    return stmts.toList

/-- An indented block whose statements start at column `c` (statements a
    comma joins are a tuple, `parseStmtTuple`). -/
partial def parseIndented (c : Nat) : PM (List SExpr) := spliceStmts <$> parseIndentedWith parseStmtTuple c

/-- A braced block after its `{`, up to the `}` (consumed): its statements
    separated by `;` and new lines, statements a comma joins a tuple
    (`parseStmtTuple`); with `arms`, the arms of `sync`, `race` and `rush`,
    separated by commas too. -/
partial def parseBraced (p : Pos) (arms : Bool := false) : PM SExpr := do
  if (← peekT).isSym "}" then bump; return .block p []
  let c := (← peekT).col
  let stmt : Nat → PM SExpr := if arms then parseStmt else parseStmtTuple
  let stmts ← withBlock (← peekT) do
    let mut stmts := #[← stmt c]
    repeat
      let t ← peekT
      checkIndent t
      if t.isSym ";" || (arms && t.isSym ",") then
        bump
        -- (`{a; b;}`: a `;` may end the block)
        if !(t.isSym ";" && (← peekT).isSym "}") then stmts := stmts.push (← stmt c)
      else if t.isSym "}" then break
      else if t.bol && !t.isEof then stmts := stmts.push (← stmt c)
      else perr t s!"expected ';', a new line or '}', found {t.tok.describe}"
    return stmts
  bump
  return .block p (spliceStmts stmts.toList)

/-- Items after a `{`, up to the `}` (consumed), separated by `;`, `,` or
    new lines: the clauses of `if{…}`, `for{…}`, `first{…}` and `assert{…}`. -/
partial def parseBracedItems (item : Nat → PM SExpr) : PM (List SExpr) := do
  if (← peekT).isSym "}" then bump; return []
  let c := (← peekT).col
  let items ← withBlock (← peekT) do
    let mut items := #[← item c]
    repeat
      let t ← peekT
      checkIndent t
      if t.isSym ";" || t.isSym "," then
        bump
        if !(t.isSym ";" && (← peekT).isSym "}") then items := items.push (← item c)
      else if t.isSym "}" then break
      else if t.bol && !t.isEof then items := items.push (← item c)
      else perr t s!"expected ';', a new line or '}', found {t.tok.describe}"
    return items
  bump
  return items.toList

/-- The items of `array` or `map` written after `:` (an indented block, or
    the rest of its line) or `.` (one, on its line), separated by `,`, `;`
    or new lines (Book of Verse tests: `array:` and `1,2;`, `map:` and a
    line per entry). -/
partial def parseItemBlock {α : Type} [Inhabited α] (item : Nat → PM α) (stop : Nat) : PM (List α) := do
  let o ← peekT
  if !(o.isSym ":" || o.isSym ".") then perr o s!"expected '\{', ':' or '.', found {o.tok.describe}"
  bump
  let n ← peekT
  if o.isSym "." then
    if n.bol || n.isEof then perr n "expected an expression after '.', on its line"
    return [← item stop]
  if n.endsEmptyBody stop then return []
  let c := n.col
  withBlock n do
    let mut items := #[← item c]
    repeat
      let t ← peekT
      checkIndent t
      if t.isSym "," || t.isSym ";" then
        bump
        -- (a separator may end a line)
        let u ← peekT
        if !u.bol && !u.isEof then items := items.push (← item c)
      else if t.bol && t.col == c && !t.isEof then items := items.push (← item c)
      else if t.bol && t.col > c then perr t "unexpected indentation"
      else break
    return items.toList

/-- The body of a construct: `: block`, `:` + inline expression, `{ block }`,
    or `.` + inline expression. -/
partial def parseBody (stop : Nat) (arms : Bool := false) : PM SExpr := do
  let t ← peekT
  if t.isSym "." then
    bump
    let n ← peekT
    if n.bol || n.isEof then perr n "expected an expression after '.', on its line"
    return .block t.pos [← parseExpr stop]
  if t.isSym ":" then
    bump
    let n ← peekT
    if n.endsEmptyBody stop then return .block t.pos []
    if n.bol then
      return .block t.pos (← parseIndented n.col)
    else return .block t.pos [← parseExpr stop]
  else if t.isSym "{" then
    bump; parseBraced t.pos arms
  else perr t s!"expected ':', '\{' or '.', found {t.tok.describe}"

/-- `then` / `else` / `do` parts: a body, or an inline expression. -/
partial def parseBranch (stop : Nat) : PM SExpr := do
  let t ← peekT
  if t.startsBody then parseBody stop else
  -- (a branch that is only a `defer` is its own scope)
  match ← parseExpr stop with
  | e@(.app _ (.ident _ "$defer") _ _) => return .block t.pos [e]
  | e => return e

/-- The clauses of `if`, `for` or `first` written without parentheses, at
    their `{`, `:` or `.`: `{…}` (perhaps none); `:` and an indented block,
    or an expression on its line; `.` and an expression on its line. Each
    is read by `item`. -/
partial def parseClauses (kw : String) (item : Nat → PM SExpr) (stop : Nat) : PM (List SExpr) := do
  let o ← peekT
  bump
  if o.isSym "{" then return ← parseBracedItems item
  let n ← peekT
  if n.offside stop || (o.isSym "." && n.bol) then
    perr n s!"expected the clauses of {kw} after '{if o.isSym "." then "." else ":"}'"
  if n.bol then parseIndentedWith item n.col else return [← item stop]

/-- `if`: its conditions in parentheses, then a body or `then` and a branch;
    or its clauses as `{…}`, `:` and a block, or `.` and an expression
    (`parseClauses`), then `then` and a branch, or nothing: the clause macro
    `if{c}`, which has no value, and `if{c} else e`, whose value is that of
    `c`'s last clause when `c` succeeds, else `e`'s. The clauses run in a
    failure context. -/
partial def parseIf (stop : Nat) : PM SExpr := do
  let t ← peekT
  let ifLine ← lineColAt (← get).pos
  bump
  -- (an `else` that starts a line belongs to the `if` whose line has its
  -- indentation, not to a more indented one, #159)
  let elseNext : PM Bool := do
    let e ← peekT
    return e.isKw "else" && !(e.bol && e.col < ifLine)
  let withElse (conds : List SExpr) (thenE : SExpr) : PM SExpr := do
    if !(← elseNext) then return .ite t.pos conds thenE none
    bump
    if (← peekT).isKw "if" then return .ite t.pos conds thenE (some (← parseIf stop))
    return .ite t.pos conds thenE (some (← parseBranch stop))
  let o ← peekT
  if o.isSym "(" then
    bump
    let (conds, _) ← parseParenItems
    let thenE ← if (← peekT).isKw "then" then do bump; parseBranch stop else parseBody stop
    return ← withElse conds thenE
  if !o.startsBody then perr o s!"expected '(', '\{', ':' or '.' after if, found {o.tok.describe}"
  let cs ← parseClauses "if" parseExpr stop
  if cs.isEmpty then perr o "'if{}' needs a clause"
  if (← peekT).isKw "then" then
    bump
    return ← withElse cs (← parseBranch stop)
  if ← elseNext then
    let (cs, v) := clausesValue cs
    return ← withElse cs v
  noMacroBody "if" (← peekT) "its value is its last clause's; write 'if (…):' for a body"
  return .ite t.pos cs (.block o.pos []) none

/-- One `for` clause: a generator, a binding, or a filter (an expression
    ends at a line starting at column `stop` or before). -/
partial def parseClause (stop : Nat := 0) : PM SExpr := do
  let t ← peekT
  -- `(local:)X : src`: a qualified generator (`(local:)X := e` is a binding,
  -- as `parseExpr` reads it)
  if let some (q, k) ← peekQual then
    if ((← peekT k).identName?).isSome && (← peekT (k + 1)).isSym ":" then
      let saved ← get
      for _ in [0:k] do bump
      let x := s!"({q}:){← expectIdent}"
      let typed ← (do
          bump
          let ty ← parseType
          let a ← peekT
          if a.isSym "=" || a.isSym ":=" then bump; return some ty else return none) <|> pure none
      if let some ty := typed then return .decl t.pos x (some ty) false (← parseValue stop)
      set saved
      for _ in [0:k + 2] do bump
      return .gen t.pos x none (← parseExpr stop)
  let t1 ← peekT 1
  match t.identName? with
  | some i =>
    if t1.isSym "->" then
      bump; bump
      let x ← expectIdent
      expectSym ":"
      return .gen t.pos x (some i) (← parseExpr stop)
    else if t1.isSym ":" then
      -- `X:t = e` is a typed binding; otherwise `X : src` is a generator
      let saved ← get
      let typed ← (do
          bump; bump
          let ty ← parseType
          let a ← peekT
          if a.isSym "=" || a.isSym ":=" then bump; return some ty else return none) <|> pure none
      match typed with
      | some ty => return .decl t.pos i (some ty) false (← parseValue stop)
      | none =>
        set saved; bump; bump
        return .gen t.pos i none (← parseExpr stop)
    else parseExpr stop
  | none => parseExpr stop

/-- The clauses of `for` or `first` in parentheses, after the `(`, through
    the `)`: separated by `,`, `;` or new lines. -/
partial def parseParenClauses : PM (List SExpr) := do
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
  return clauses.toList

/-- `for`: its clauses in parentheses, then a body or `do` and a branch; or
    its clauses as `{…}`, `:` and a block, or `.` and an expression
    (`parseClauses`), then `do` and a branch, or nothing: the clause macro
    `for{c}`, the value of `c`'s last clause for each way the clauses
    succeed. -/
partial def parseFor (stop : Nat) : PM SExpr := do
  let t ← peekT
  bump
  let o ← peekT
  if o.isSym "(" then
    bump
    let clauses ← parseParenClauses
    let body ← if (← peekT).isKw "do" then do bump; parseBranch stop else parseBody stop
    return .forE t.pos clauses body
  if !o.startsBody then perr o s!"expected '(', '\{', ':' or '.' after for, found {o.tok.describe}"
  let cs ← parseClauses "for" (fun c => parseClause c) stop
  if cs.isEmpty then perr o "'for{}' needs a generator"
  if (← peekT).isKw "do" then
    bump
    return .forE t.pos cs (← parseBranch stop)
  noMacroBody "for" (← peekT) "its value is its last clause's; write 'for (…):' for a body"
  let (cs, v) := clausesValue cs
  return .forE t.pos cs v

partial def parseCase (stop : Nat) : PM SExpr := do
  let t ← peekT
  bump
  -- (the value in parentheses, perhaps a sequence: `case(Bar; Baz)`)
  let o ← peekT
  if !o.isSym "(" then perr o s!"expected '(', found {o.tok.describe}"
  bump
  let scrut ← parseParenExpr o.pos
  let parseArm (c : Nat) : PM (Option SExpr × SExpr) := do
    -- (`@ignore_unreachable` on an arm: it may be one never reached, Book
    -- of Verse tests, `Enum.versetest` 506-592)
    let a0 ← peekT
    let mut ignored := false
    if a0.isSym "@" then
      for (q, attr) in ← parseAttrs do
        match attr with
        | .ident _ "ignore_unreachable" => ignored := true
        | _ => throw s!"{q.show}: a case arm takes no attribute but @ignore_unreachable"
    let a ← peekT
    let pat ← if a.isKw "_" || (match a.tok with | .ident "_" => true | _ => false) then do
        bump; pure none
      else some <$> parseAdd 0
    expectSym "=>"
    let v ← parseValue c
    -- (marked by where `elabCase` reports an arm never reached)
    if ignored then
      let q := (pat.map (·.pos)).getD v.pos
      modify fun st => { st with ignoredArms := st.ignoredArms.push q }
    return (pat, v)
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

/-- One struct field: `[var<specs>] Name<specs>:type [= default]`, after
    its attributes, as a class's (`parseClassItem`). -/
partial def parseField (c : Nat) : PM SField := do
  let attrs ← parseAttrs
  let f ← parseField0 c
  if attrs.isEmpty then return f
  modify fun st => { st with attrs := st.attrs ++ (attrs.map fun (p, e) => (p, "structField", f.name, e)).toArray }
  return { f with specs := f.specs ++ attrs.map fun (_, e) => "@" ++ e.attrHead }

partial def parseField0 (c : Nat) : PM SField := do
  let start ← peekT
  let isVar := (← peekT).isKw "var"
  if isVar then bump
  let varSpecs ← if isVar then parseSpecs else pure []
  let n ← expectBinder
  let specs ← parseSpecs
  expectSym ":"
  let ty ← parseType
  let a ← peekT
  let d ← if a.isSym "=" || a.isSym ":=" then do bump; pure (some (← parseValue c)) else pure none
  ofExcept <| EffectPolicy.checkField start.pos .structField n specs varSpecs d.isSome isVar
  return { name := n, ty, default := d, isVar, specs, varSpecs }

/-- `struct` (after the keyword): optional specifiers, then `:` + fields or `{ fields }`. -/
partial def parseStructBody (p : Pos) : PM SExpr := do
  let specs ← parseSpecs
  ofExcept <| EffectPolicy.checkData p "struct" specs
  let o ← peekT
  let mut fields := #[]
  if o.isSym ":" then
    bump
    let n ← peekT
    let c := n.col
    if !n.endsEmptyBody (← get).topCol then
      fields ← withBlock n do
        let mut fields := #[← parseField c]
        repeat
          let a ← peekT
          checkIndent a
          if a.isSym ";" then
            bump
            if (← peekT).continuesBlock c then fields := fields.push (← parseField c)
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
  return .structDef p [] specs fields.toList

/-- `enum` (after the keyword): `:` + values or `{ values }`. -/
partial def parseEnumBody (p : Pos) : PM SExpr := do
  let mut isOpen := false
  let mut seen : List String := []
  while (← peekT).isSym "<" do
    bump
    let st ← peekT
    let sp ← expectIdent
    expectSym ">"
    -- (`<persistable>` has no meaning in openverse: accepted and ignored)
    if !["open", "closed", "persistable"].contains sp then
      perr st s!"an enum's specifier is <open>, <closed> or <persistable>, not <{sp}>"
    if (sp == "open" && seen.contains "closed") || (sp == "closed" && seen.contains "open") then
      perr st "an enum is <open> or <closed>, not both"
    if seen.contains sp then perr st s!"<{sp}> is given twice"
    seen := seen ++ [sp]
    if sp == "open" then isOpen := true
  let o ← peekT
  let mut names := #[]
  -- (a value `(e:)v`, qualified with its enum, may take a reserved word's or
  -- a keyword's name, Book of Verse ch. 9: `resolveModules` checks `e`)
  let value : PM String := do
    -- (its attributes: their records, `PSt.attrs`)
    let attrs ← parseAttrs
    let v ← (do
      if let some (q, k) ← peekQual then
        for _ in [0:k] do bump
        return s!"({q}:){← expectQualifiedName}"
      expectIdent)
    modify fun st => { st with attrs := st.attrs ++ (attrs.map fun (p, e) => (p, "enumerator", v, e)).toArray }
    return v
  if o.isSym ":" then
    bump
    let n ← peekT
    let c := n.col
    if !n.endsEmptyBody (← get).topCol then
      names ← withBlock n do
        let mut names := #[← value]
        repeat
          let a ← peekT
          checkIndent a
          if a.isSym "," || a.isSym ";" then
            bump
            if (← peekT).continuesBlock c then names := names.push (← value)
          else if a.bol && a.col == c && !a.isEof then names := names.push (← value)
          else break
        return names
  else if o.isSym "{" then
    bump
    repeat
      let a ← peekT
      if a.isSym "}" then bump; break
      if a.isSym "," || a.isSym ";" then bump; continue
      names := names.push (← value)
  else perr o "expected ':' or '{' after enum"
  return .enumDef p names.toList isOpen

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
        -- (several values, `{2, 3}` or `{2, 3, ?Factor := 4}`, are the
        -- arguments of a call of `ToString`, Book of Verse tests,
        -- Literals/String.versetest 242, 243)
        let item : PM SExpr := do
          let t ← peekT
          if t.isSym "?" && (← peekT 1).identName?.isSome && (← peekT 2).isSym ":=" then
            bump
            let n ← expectIdent
            bump
            return .decl t.pos ("?" ++ n) none false (← parseExpr 0)
          parseExpr 0
        let first ← peekT
        let mut items := #[← item]
        while (← peekT).isSym "," do
          bump
          items := items.push (← item)
        let rest ← peekT
        if !rest.isEof then perr rest "unexpected tokens in interpolation"
        set saved
        let e : SExpr := match items.toList with
          | [e@(.decl _ n _ _ _)] => if n.startsWith "?" then .app first.pos (.ident first.pos "ToString") [e] false else e
          | [e] => e
          | es => .app first.pos (.ident first.pos "ToString") es false
        out := out.push (.code e)
  return out.toList

partial def parsePrimary (stop : Nat) : PM SExpr := do
  let t ← peekT
  -- `for<par>(…)`, `array <computes> {…}`: a macro's specifiers (Book of
  -- Verse tests, TimSyntax.versetest, InvalidAttributeLocations.versetest),
  -- which none admits: taken out of the tokens, the macro read, and refused
  if let .ident kw := t.tok then
    if macroKeywords.contains kw && (← peekT 1).isSym "<" && !(← peekT 1).bol &&
        ((← peekT 2).tok matches .ident _) && (← peekT 3).isSym ">" then
      let sp := match (← peekT 2).tok with | .ident x => x | _ => ""
      modify fun st => { st with toks := st.toks.extract 0 (st.pos + 1) ++ st.toks.extract (st.pos + 4) st.toks.size }
      let e ← parsePrimary stop
      return refusedForm t.pos (.macroSpecifier sp kw) [e]
  -- `type{_X:t where c, …}`: a refinement type (Book of Verse ch. 11)
  if t.identName? == some "type" && (← peekT 1).isSym "{" then
    bump; bump
    let v ← expectIdent
    expectSym ":"
    let base ← parseType
    if !(← peekT).isKw "where" then perr (← peekT) "expected 'where' and the conditions of the refinement"
    bump
    let mut conds := #[← parseExpr 0]
    while (← peekT).isSym "," do
      bump
      conds := conds.push (← parseExpr 0)
    expectSym "}"
    return .refineDef t.pos v base conds.toList
  if let .ident d := t.tok then
    if (← peekT 1).isSym "<" && (← peekT 2).isKw "constructor" && (← peekT 3).isSym ">" then
      perr t s!"{d}<constructor>(…) delegates to a constructor: it can only be an item of a constructor's body; call it as {d}(…)"
  match t.tok with
  | .int n => bump; return .int t.pos n
  | .char c => bump; return .char t.pos c
  | .char32 c => bump; return .char32 t.pos c
  | .float b => bump; return .float t.pos b
  | .str parts => bump; return .str t.pos (← parseInterp parts)
  -- (a path is a name no identifier spells: the elaborator refuses it as
  -- a value, Book of Verse ch. 16)
  | .path p => bump; return .ident t.pos p
  -- (as is a float literal of a width openverse lacks, `1.5f32`)
  | .floatWidth f => bump; return .ident t.pos f
  | .sym "(" =>
    if (← peekT 1).isKw "super" && (← peekT 2).isSym ":" && (← peekT 3).isSym ")" then
      -- `(super:)M`: the parent's implementation of a method
      bump; bump; bump; bump
      return .member t.pos (.ident t.pos "(super:)") (← expectIdent)
    if let some (q, k) ← peekQual then
      -- `(q:)x`: `Self.(q:)x`, which `resolveModules` reads by what `q`
      -- names: a module's member, a local, a built-in, an enum's value, or
      -- a qualified member of the current object (#70)
      for _ in [0:k] do bump
      let m ← expectQualifiedName
      -- (`(M:)c{…}`: a construction of the module's `c`, #147)
      if ← fieldsFollow stop then
        return .construct t.pos s!"{q}.{m}" [] (← parseFields)
      return .member t.pos (.ident t.pos "Self") s!"({q}:){m}"
    -- `(t(int)){…}`: a construction of a parenthesized type (Book of Verse
    -- tests, ParametricTypes.versetest), as `t(int){…}` is
    let saved ← get
    let made? ← (do
        bump
        let ty ← parseType
        expectSym ")"
        if !(← fieldsFollow stop) then throw "not a construction"
        match ty with
        | .name n => return some (n, ([] : List STy))
        | .app n ts => return some (n, ts)
        | _ => throw "not a construction") <|> pure none
    if let some (n, ts) := made? then return .construct t.pos n ts (← parseFields)
    set saved
    -- `(?int)(X)`, `([]int)(X)`: `X` converted to a type written only as a
    -- type can be (Book of Verse tests, Cast.versetest 61, 62), the head
    -- `$type(t)` (`elabConversionWith`)
    let conv? ← (do
        bump
        let ty ← parseType
        expectSym ")"
        let o ← peekT
        if !o.isSym "(" || o.spaced then throw "not a conversion"
        if ty.couldBeValue then throw "a name: a call"
        return some ty) <|> pure none
    if let some ty := conv? then return .construct t.pos "$type" [ty] []
    set saved
    bump
    parseParenExpr t.pos
  | .sym "{" => bump; parseBraced t.pos
  | .ident "if" => parseIf stop
  | .ident "for" => parseFor stop
  | .ident "case" => parseCase stop
  | .ident "loop" => bump; return .loop t.pos (← parseBody stop)
  -- `defer:` (Book of Verse ch. 7): runs when its scope exits; `$defer(body)`
  | .ident "defer" => bump; return .app t.pos (.ident t.pos "$defer") [← parseBody stop] false
  | .ident "block" => bump; parseBody stop
  -- `sync:` and `race:` (#156): each statement of the block is an arm
  -- `branch:` (#156): a background task over the enclosing function's frame
  -- `profile(Tag): body`, `profile: body`, `profile{body}` (Book of Verse
  -- ch. 7, "Profiling": it "measures execution time" and its value is the
  -- body's, "without changing the program's behavior"): the tag, a string,
  -- then the body; openverse measures nothing (`profileOf`)
  | .ident "profile" =>
    let n ← peekT 1
    if n.startsBody && !n.bol then
      bump
      return ← profileOf t.pos none (← parseBody stop)
    if n.isSym "(" && !n.spaced then
      let saved ← get
      bump; bump
      let tag ← parseExpr 0
      if (← peekT).isSym ")" && (← peekT 1).startsBody && !(← peekT 1).bol then
        bump
        return ← profileOf t.pos (some tag) (← parseBody stop)
      set saved
    bump; return .ident t.pos "profile"
  | .ident "branch" =>
    let n ← peekT 1
    if n.startsBody then
      bump
      let b ← parseBody stop
      return .app t.pos (.ident t.pos "$branch") [b] false
    else
      bump; return .ident t.pos "branch"
  -- `spawn{F(…)}` (#156)
  | .ident "spawn" =>
    if (← peekT 1).startsBody then
      bump
      let b ← parseBody stop
      return .app t.pos (.ident t.pos "$spawn") [b] false
    else
      bump; return .ident t.pos "spawn"
  | .ident "sync" | .ident "race" | .ident "rush" =>
    let n ← peekT 1
    if n.startsBody then
      bump
      let kw := if t.isKw "sync" then "$sync" else if t.isKw "race" then "$race" else "$rush"
      let arms := match ← parseBody stop (arms := true) with
        | .block _ es => es
        | e => [e]
      return .app t.pos (.ident t.pos kw) arms false
    else
      bump; return .ident t.pos (t.identName?.getD "sync")
  | .ident "let" =>
    let n1 ← peekT 1
    if n1.isSym "(" || n1.isSym "{" then
      -- `let(defs){body}`, and `let{defs} do body` (Tim Sweeney's tests):
      -- the definitions are visible in the body only, and the value is the
      -- body's
      bump; bump
      let defs ← if n1.isSym "(" then (·.1) <$> parseParenItems else parseBracedItems parseExpr
      let body ← if n1.isSym "(" then parseBody stop else do expectKw "do"; parseBranch stop
      return .block t.pos (defs ++ [.block t.pos [body]])
    else
      bump; return .ident t.pos "let"
  | .ident "first" =>
    -- `first` takes its clauses as `for` does, generators too (Book of
    -- Verse tests: `first{I->X:Xs; X > 15}`, `first:` … `do:`), and gives
    -- the value of its body, or of its last clause, at the first way they
    -- succeed; it fails if they do not (the first success of the clauses
    -- when they have a choice, which the elaborator sees once calls of
    -- functions with several values are inlined, #208, #235; else a block)
    let firstOf (cs : List SExpr) (v : SExpr) : SExpr :=
      .app t.pos (.ident t.pos "$first") [.block t.pos (cs ++ [v])] false
    let n1 ← peekT 1
    if n1.isSym "(" then
      -- `first(c){b}`, `first(c). b`, `first(c) do b`; otherwise (no body
      -- on the same line, or no clauses in the parentheses) a call
      let saved ← get
      bump; bump
      let cs? ← (some <$> parseParenClauses) <|> pure none
      let n ← peekT
      if let some cs := cs? then
        if !n.bol && (n.startsBody || n.isKw "do") then
          let b ← if n.isKw "do" then do bump; parseBranch stop else parseBody stop
          return firstOf cs (.block t.pos [b])
      set saved
      bump; return .ident t.pos "first"
    if n1.isSym "{" || (n1.isSym ":" && (← peekT 2).bol) then
      -- `first{c}`, `first:` and a block, then `do` and a branch or nothing
      bump
      let cs ← parseClauses "first" (fun c => parseClause c) stop
      if cs.isEmpty then perr n1 "'first{}' needs a clause"
      if (← peekT).isKw "do" then
        bump
        return firstOf cs (.block t.pos [← parseBranch stop])
      noMacroBody "first" (← peekT) "its value is its last clause's; write 'first(…) {…}' for a body"
      let (cs, v) := clausesValue cs
      return firstOf cs v
    bump; return .ident t.pos "first"
  | .ident "assert" =>
    if (← peekT 1).isSym "{" then
      -- `assert{c}`: a runtime error unless `c` succeeds
      bump
      let b ← peekT
      bump
      let cs ← parseBracedItems parseExpr
      if cs.isEmpty then perr b "'assert{}' needs a clause"
      noMacroBody "assert" (← peekT) "it only checks its clauses"
      return .ite t.pos cs (.block t.pos []) (some (.app t.pos (.ident t.pos "Err") [] false))
    else
      bump; return .ident t.pos "assert"
  | .ident "break" => bump; return .brk t.pos
  | .ident "return" =>
    bump
    let n ← peekT
    if n.offside stop || n.isSym ")" || n.isSym "}" || n.isSym ";" || n.isKw "else" then
      return .ret t.pos none
    return .ret t.pos (some (← parseExpr stop))
  | .ident "array" =>
    bump
    -- (`array{1; 2; 3}`: its elements separated as a construction's fields,
    -- Book of Verse ch. 1, "Semicolons vs Commas")
    if (← peekT).isSym "{" then bump; return .arrayLit t.pos (← parseItems "}" true)
    return .arrayLit t.pos (← parseItemBlock (fun c => parseExpr c) stop)
  | .ident "map" =>
    bump
    let entry (c : Nat) : PM (SExpr × SExpr) := do
      let inKey := (← get).inMapKey
      modify fun st => { st with inMapKey := true }
      let k ← parseExpr c
      modify fun st => { st with inMapKey := inKey }
      expectSym "=>"
      return (k, ← parseExpr c)
    if !(← peekT).isSym "{" then return .mapLit t.pos (← parseItemBlock entry stop)
    bump
    let mut entries := #[]
    repeat
      let a ← peekT
      if a.isSym "}" then bump; break
      if a.isSym "," then bump; continue
      entries := entries.push (← entry 0)
    return .mapLit t.pos entries.toList
  | .ident "struct" => bump; parseStructBody t.pos
  | .ident "enum" => bump; parseEnumBody t.pos
  -- (`option:`, `option. e`: the body as any other)
  | .ident "option" =>
    bump
    if (← peekT).isSym "{" then bump; return .optionLit t.pos (← parseBraced t.pos)
    return .optionLit t.pos (← parseBody stop)
  | .ident "logic" =>
    bump
    -- (`logic(X)`: `X` converted to logic, Book of Verse tests, Cast.versetest:59)
    if (← peekT).isSym "(" && !(← peekT).spaced then return .ident t.pos "logic"
    -- (`F(logic)`: the type, as an argument, a type given as one)
    if (← peekT).isSym ")" || (← peekT).isSym "," then return .ident t.pos "logic"
    if (← peekT).isSym "{" then bump; return .logicLit t.pos (← parseBraced t.pos)
    return .logicLit t.pos (← parseBody stop)
  | .ident x =>
    if keywords.contains x then perr t s!"unexpected keyword '{x}'"
    bump; return .ident t.pos x
  | _ =>
    -- (`?A := e` outside a call's arguments: a tuple's named element)
    if t.isSym "?" && (← peekT 1).identName?.isSome && (← peekT 2).isSym ":=" then
      perr t "a tuple with a named element (?Name := …) is not supported: the pinned Book of Verse does not settle such values, and named parameters inside a tuple parameter are not implemented"
    perr t s!"unexpected {t.tok.describe}"
end

/-- A function body after `=`: an indented block, a braced block (whose `{`
    may start the next line), or an expression. -/
def parseFnBody : PM SExpr := do
  let t ← peekT
  let top := (← get).topCol
  -- (a braced body's `{` may start the next line, at the definition's
  -- column; deeper, it starts an indented block)
  if t.isSym "{" && (!t.bol || t.col == top) then bump; parseBraced t.pos
  else if t.bol then
    if t.col ≤ top then perr t "expected an indented function body"
    return .block t.pos (← parseIndented t.col)
  else parseExpr top

/-- A parameter, or a parenthesized group of them that destructures a tuple
    argument (Book of Verse ch. 6, "Tuple as Arguments"): its name, type and
    whether it is named, its default, and the names a group binds, each
    with its type and its path of element indices. A group of one parameter
    is that parameter. -/
partial def parseParamItem : PM (Pos × String × STy × Bool × Option SExpr × List (String × STy × List Nat)) := do
  let t ← peekT
  if t.isSym "@" then
    perr t "an attribute cannot be written on a parameter: attributes go on the definitions of a module, a class, an interface, a struct or an enum (Book of Verse tests, Function.versetest, deprecated.versetest: 3596)"
  -- `(local:)X:t`: a qualified parameter (Book of Verse ch. 16, "Local
  -- Qualifiers"), not a group
  if (← peekQual).isSome then
    let pn ← expectBinder
    let pty ← if (← peekT).isSym "(" then parseFnSig else do expectSym ":"; parseType
    let dflt ← if (← peekT).isSym "=" then do bump; pure (some (← parseExpr 0)) else pure none
    return (t.pos, pn, pty, false, dflt, [])
  if t.isSym "(" then
    bump
    let mut items := #[]
    if !(← peekT).isSym ")" then
      repeat
        items := items.push (← parseParamItem)
        if (← peekT).isSym "," then bump else break
    expectSym ")"
    if items.isEmpty then perr t "an empty parameter group: write a tuple() parameter"
    if let some (_, n, _) := items.find? (·.2.2.2.1) then
      perr t s!"a named parameter inside a tuple parameter (?{n}) is not supported yet"
    if let #[one] := items then return one
    let binds := items.toList.zipIdx.flatMap fun ((_, n, ty, _, _, inner), i) =>
      if !inner.isEmpty then inner.map fun (m, mt, path) => (m, mt, i :: path)
      else if n.isEmpty then [] else [(n, ty, [i])]
    return (t.pos, "", .tup (items.toList.map (·.2.2.1)), false, none, binds)
  let named := t.isSym "?"
  if named then bump
  if named && (← peekQual).isSome then
    perr (← peekT) "a named parameter cannot be qualified: its name is how a call gives it (Book of Verse tests, DefaultNamed.versetest)"
  -- (`F(:t)`: an unnamed parameter, as function types write one; its name
  -- is "", which the parameter list makes one no program can write)
  let pn ← if !named && t.isSym ":" then pure "" else expectIdent
  -- (`F(:t):u`: a parameter of a function type, written as a function's
  -- signature, Book of Verse ch. 6)
  let pty ← if (← peekT).isSym "(" then parseFnSig else do expectSym ":"; parseType
  let dflt ← if (← peekT).isSym "=" then do bump; pure (some (← parseExpr 0)) else pure none
  return (t.pos, pn, pty, named, dflt, [])

/-- A parameter list after its `(`, through the `)`: the parameters, the
    type parameters of a `where` clause that ends it, and the declarations
    a body starts with to bind the names its groups destructure. A group is
    a parameter of its tuple type (`$tuple{i}`), so calls, overloads and
    function values see a tuple parameter there. A later parameter's
    default may use a destructured name, as an earlier parameter. -/
partial def parseParamList (close : String := ")") : PM (Array SParam × Array TParam × List SExpr) := do
  let mut ps := #[]
  let mut binds : List SExpr := []
  -- (each destructured name, the element of its group's parameter it is)
  let mut σ : List (String × SExpr) := []
  if !(← peekT).isSym close && !(← peekT).isKw "where" then
    repeat
      let (q, pn, pty, named, dflt, inner) ← parseParamItem
      let dflt := dflt.map (·.substIdents σ)
      let pn := if !inner.isEmpty then s!"$tuple{ps.size}" else if pn.isEmpty then s!"{unnamedPrefix}{ps.size}" else pn
      for (n, ty, path) in inner do
        let e := path.foldl (fun e (i : Nat) => SExpr.app q e [.int q (Int.ofNat i)] false) (.ident q pn)
        σ := σ ++ [(n, e)]
        binds := binds ++ [.decl q n (some ty) false e]
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
      let tp ← if ["subtype", "castable_subtype", "concrete_subtype"].contains k then do
          expectSym "("
          let a ← parseType
          expectSym ")"
          pure (if k == "subtype" then TParam.withUpperBound vt.pos v a else TParam.withMetatype vt.pos v k a)
        else if k == "type" then pure { pos := vt.pos, name := v, constraint := "type" }
        else perr kt s!"expected 'type', 'subtype(…)' or 'castable_subtype(…)' for type parameter {v}, found {kt.tok.describe}"
      tps := tps.push tp
      if (← peekT).isSym "," then bump else break
  expectSym close
  return (ps, tps, binds)

/-- A body that starts with the declarations `binds` (`parseParamList`). -/
def withBinds (binds : List SExpr) (body : SExpr) : SExpr :=
  if binds.isEmpty then body else match body with
    | .block p items => .block p (binds ++ items)
    | e => .block e.pos (binds ++ [e])

/-- At a definition's start: `(R:t).`, the receiver of an extension method
    `(R:t).M(…)` (Book of Verse ch. 6, "Extension Methods"), when a group in
    parentheses followed by `.` and a name starts here, through the `.`: the
    receiver and the type parameters a `where` in its parentheses declares
    (`(X:[]t where t:type)`). The receiver is one parameter, which may be
    unnamed (`(:t)`); `(A:int, B:int)` and `()` are refused (ch. 6: "You
    cannot use destructured parameter syntax"), and so is a named one or a
    default. -/
def parseExtensionHead? : PM (Option (SParam × List TParam)) := do
  let t ← peekT
  if !t.isSym "(" then return none
  -- (the group's closing parenthesis, then `.` and a name on its line)
  let mut depth : Nat := 0
  let mut k := 0
  repeat
    let u ← peekT k
    if u.isEof then return none
    if u.isSym "(" then depth := depth + 1
    else if u.isSym ")" then
      depth := depth - 1
      if depth == 0 then break
    k := k + 1
  let dot ← peekT (k + 1)
  if !dot.isSym "." || dot.bol || ((← peekT (k + 2)).identName?).isNone then return none
  bump
  let (ps, tps, binds) ← parseParamList
  let some r := (if ps.size == 1 && binds.isEmpty then ps[0]? else none)
    | perr t "the receiver of an extension method is one parameter, (Name:type) or (:type): a tuple's type is written tuple(…) (Book of Verse ch. 6)"
  if r.named || r.default.isSome then
    perr t "the receiver of an extension method is one parameter, (Name:type) or (:type), not a named one or one with a default"
  expectSym "."
  -- (an unnamed receiver's name, which no program can write)
  return some ({ r with name := if r.name.startsWith unnamedPrefix then "$receiver" else r.name }, tps.toList)

/-- Why `(R:t).M` must be followed by its parameters. -/
def noExtensionFields : String :=
  "an extension method takes parameters, (R:t).M(…): there are no extension fields (Book of Verse ch. 6)"

/-- The body of a method defined at column `c`: on the following lines,
    indented more than `c`, braced (from the next line, at `c`), or inline. -/
def parseFnBodyAt (c : Nat) : PM SExpr := do
  let t ← peekT
  if t.isSym "{" && (!t.bol || t.col == c) then bump; parseBraced t.pos
  else if t.bol then
    if t.col ≤ c then perr t "expected an indented method body"
    return .block t.pos (← parseIndented t.col)
  else parseExpr c

/-- An item of a constructor function's body (Book of Verse ch. 10): a field
    initializer `F := e`, `let:` declarations, a `block:` clause, or a
    delegation `D<constructor>(args)` to another constructor of the class or
    of a class above it. A `let:` is `$let(block)`, a delegation the call of
    `$ctor:D`. -/
partial def parseCtorItem (c : Nat) : PM SExpr := do
  let t ← peekT
  if t.isKw "let" && (← peekT 1).isSym ":" then
    bump
    return .app t.pos (.ident t.pos "$let") [← parseBody c] false
  if let some d0 := t.identName? then
    -- (`M.D<constructor>(…)`: a module's constructor, #112)
    let mut k := 1
    let mut d := d0
    while (← peekT k).isSym "." && ((← peekT (k + 1)).identName?).isSome do
      d := d ++ "." ++ ((← peekT (k + 1)).identName?).getD ""
      k := k + 2
    if (← peekT k).isSym "<" && (← peekT (k + 1)).isKw "constructor" && (← peekT (k + 2)).isSym ">" then
      for _ in [0:k + 3] do bump
      let a ← peekT
      if a.isSym "(" then bump; return .app t.pos (.ident t.pos (delegationHead d)) (← parseArgs ")") false
      if a.isSym "[" then bump; return .app t.pos (.ident t.pos (delegationHead d)) (← parseArgs "]") true
      perr a s!"expected the arguments of {d}<constructor>"
  match ← parseExpr c with
  | e@(.decl _ _ none false _) => return e
  | e@(.block ..) => if t.isKw "block" then return e else perr t "a constructor's body has field initializers F := e, let:, block: and delegations D<constructor>(…)"
  | _ => perr t "a constructor's body has field initializers F := e, let:, block: and delegations D<constructor>(…)"

/-- The items of a constructor function's body, after its class name: an
    indented block after `:`, items on the line after `:` (separated by `;`),
    or `{…}`. -/
partial def parseCtorBody (stop : Nat) : PM (List SExpr) := do
  let t ← peekT
  if t.isSym "{" then
    bump
    return ← parseBracedItems parseCtorItem
  if !t.isSym ":" then perr t s!"expected ':' or '\{' after the constructor's class, found {t.tok.describe}"
  bump
  let n ← peekT
  if n.endsEmptyBody stop then return []
  if !n.bol then
    let mut items := #[← parseCtorItem stop]
    while (← peekT).isSym ";" do bump; items := items.push (← parseCtorItem stop)
    return items.toList
  let c := n.col
  withBlock n do
    let mut items := #[← parseCtorItem c]
    repeat
      let t ← peekT
      checkIndent t
      if t.isSym ";" then
        bump
        if (← peekT).continuesBlock c then items := items.push (← parseCtorItem c)
      else if t.isEof then break
      else if t.bol && t.col == c then items := items.push (← parseCtorItem c)
      else if t.bol && t.col > c then perr t "unexpected indentation"
      else break
    return items.toList

/-- One item of a class body at column `c`: a field `[var] Name:type [= e]`
    or a method `Name(params)<effects>:type = body`. -/
partial def parseClassItem0 (c : Nat) : PM (Sum SField STop) := do
  let t ← peekT
  -- `block:` runs when an instance is constructed: the method `$block`
  if t.isKw "block" then
    let body ← parseExpr c
    return .inr (.fn t.pos "$block" [] [] [] (.name "void") body)
  let isVar := t.isKw "var"
  if isVar then bump
  -- (`var<private> X<public>:t`: its write access, Book of Verse ch. 12)
  let varSpecs ← if isVar then parseSpecs else pure []


  -- `(q:)M`, `(q:)F:t`: a member whose qualifier names where it is defined:
  -- the class itself, or, for an override, what introduces it (an
  -- implementation of interface `q`'s `M` only, #70); `resolveModules` and
  -- the classes' elaboration check `q`
  -- `(R:t).M(…)`: an extension method in the class, its method `$ext:M`, whose
  -- first parameter is the receiver (Book of Verse ch. 6)
  let ext ← if isVar || (← peekQual).isSome then pure none else parseExtensionHead?
  let name ← match ext with
    | some _ => do pure (extensionName (← expectIdent))
    | none => expectBinder
  let pre ← parseSpecs
  if ext.isSome && !(← peekT).isSym "(" then perr (← peekT) noExtensionFields
  if (← peekT).isSym ":" then
    -- a field, `Name<override>:t = e` giving an inherited field a new default
    bump
    let ty ← parseType
    let a ← peekT
    let d ← if a.isSym "=" || a.isSym ":=" then do bump; pure (some (← parseValue c)) else pure none
    ofExcept <| EffectPolicy.checkField t.pos .field name pre varSpecs d.isSome isVar
    return .inl { name, ty, default := d, isVar, specs := pre, varSpecs }
  if isVar then perr t "expected a field after var"
  expectSym "("
  let (ps, tps, binds) ← parseParamList
  let ps := (ext.map (·.1)).toList ++ ps.toList
  let tps := ((ext.map (·.2)).getD []) ++ tps.toList
  let effs ← parseSpecs
  accessOnName t.pos name effs
  expectSym ":"
  let ret ← parseType
  let a ← peekT
  if a.isSym "=" || a.isSym ":=" then
    bump
    return .inr (.fn t.pos name ps tps (pre ++ effs) ret (withBinds binds (← parseFnBodyAt c)))
  if ext.isSome then perr a "expected '=' before the extension method's body"
  -- no body: an abstract method
  return .inr (.fn t.pos name ps tps (pre ++ effs ++ ["$abstract"]) ret (.block t.pos []))

/-- One item of a class body at column `c`, after its attributes, if any
    (`parseClassItem0`): its attributes among the specifiers of its name,
    `@name`, and their records (`PSt.attrs`, given out after the class). -/
partial def parseClassItem (c : Nat) : PM (Sum SField STop) := do
  let attrs ← parseAttrs
  let item ← parseClassItem0 c
  if attrs.isEmpty then return item
  let specs := attrs.map fun (_, e) => "@" ++ e.attrHead
  let (place, name, item) := match item with
    | .inl f => (if f.isOverride then "field:override" else "field", f.name, Sum.inl { f with specs := f.specs ++ specs })
    | .inr m => match m with
      | .fn _ n _ _ mspecs .. =>
        (if mspecs.contains "override" then "method:override" else "method", n, .inr (specs.foldl (fun (m : STop) sp => STop.addSpec sp m) m))
      | _ => ("method", "", .inr m)
  modify fun st => { st with attrs := st.attrs ++ (attrs.map fun (p, e) => (p, place, name, e)).toArray }
  return item

/-- `class` or `interface` (after the keyword): specifiers, the parents
    `(base, interface₁, …)`, then `:` + items or `{ items }`. -/
partial def parseClassBody (p : Pos) (name : String) (nameSpecs : List String) (tps : List TParam)
    (isIface : Bool) : PM STop := do
  let specs ← parseSpecs
  let mut parents := #[]
  -- (`class()`: no parents, as `class`)
  if (← peekT).isSym "(" then
    bump
    if !(← peekT).isSym ")" then
      repeat
        parents := parents.push (← parseType)
        if (← peekT).isSym "," then bump else break
    expectSym ")"
  let o ← peekT
  let mut items := #[]
  if o.isSym ":" then
    bump
    let n ← peekT
    let c := n.col
    if !n.endsEmptyBody (← get).topCol then
      items ← withBlock n do
        let mut items := #[← parseClassItem c]
        repeat
          let a ← peekT
          checkIndent a
          if a.isSym ";" then
            bump
            if (← peekT).continuesBlock c then items := items.push (← parseClassItem c)
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
  let fields := items.toList.filterMap fun | .inl f => some f | .inr _ => none
  let methods := items.toList.filterMap fun | .inr m => some m | .inl _ => none
  -- the `block:` clauses, in order, as one method
  let isBlock : STop → Bool := fun | .fn _ "$block" .. => true | _ => false
  let blocks := methods.filterMap fun | .fn _ "$block" _ _ _ _ b => some b | _ => none
  if isIface then
    if let some (.fn q _ ..) := methods.find? isBlock then
      throw s!"{q.line}:{q.col}: interface {name} cannot have a block: clause"
  let methods := methods.filter (!isBlock ·) ++
    (if blocks.isEmpty then [] else [.fn p "$block" [] [] [] (.name "void") (.block p blocks)])
  return .classDef p name nameSpecs tps specs parents.toList isIface fields methods

/-- After the `:=` of a definition at the top level or in a module: the type
    of a type alias, when the definition's value is written as only a type
    can be (`?int`, `[]t`, `[k]v`, `tuple(…)`, `t->u`, `type{_(…):r}`,
    `logic`; Book of Verse ch. 11, "Type Aliases"), through the end of the
    definition. A name, or a name applied to names (`c`, `box(int)`), could
    be a value too: it is parsed as one, and `Aliases.expand` decides by
    what the names are. -/
def typeAliasRHS? : PM (Option STy) := do
  let t ← peekT
  if t.bol || t.isEof then return none
  let saved ← get
  let ty? ← tryCatch (some <$> parseType) fun _ => pure none
  if let some ty := ty? then
    let n ← peekT
    let ends := n.isEof || (n.bol && n.col ≤ (← get).topCol) ||
      (!n.bol && (n.isSym ";" || n.isSym "," || n.isSym "}"))
    if ends && !ty.couldBeValue then return some ty
  set saved
  return none

/-- The type parameters of `name(t:type, u:subtype(…), …) := class …`,
    `:= struct …` or a type alias's, defined at `p`; `n` is where a malformed
    one is reported. One may be unnamed, `t(:type)` (Book of Verse tests), as
    nothing then names it. -/
def typeParamsOf (p : Pos) (n : Token) (ps : Array SParam) : PM (List TParam) :=
  ps.toList.mapM fun prm => do
    match prm.named, prm.default, prm.ty with
    | false, none, .name "type" => pure { pos := p, name := prm.name, constraint := "type" }
    | false, none, .app "subtype" [bound] => pure (TParam.withUpperBound p prm.name bound)
    | false, none, .app k [bound] =>
      if ["castable_subtype", "concrete_subtype"].contains k then pure (TParam.withMetatype p prm.name k bound)
      else
        let w := if prm.name.startsWith "$tuple" then "t" else prm.name
        perr n s!"a parameter of a parametric type is written {w}:type or {w}:subtype(…)"
    | _, _, _ =>
      -- (a group has no name the program wrote)
      let w := if prm.name.startsWith "$tuple" then "t" else prm.name
      perr n s!"a parameter of a parametric type is written {w}:type or {w}:subtype(…)"

/-- The definitions at column `col`, their names qualified by `pfx` (the
    enclosing modules, `A::B::`, #112). A module is flattened: its members
    are definitions of qualified names, and markers record the module
    (`$module:A`, with its specifiers) and its `using{M}`s (`$open:A::|M`),
    for the names' resolution in Elab. With
    `braced`, the definitions of `module{…}`, through the `}`. -/
partial def parseTopsIn (col : Nat) (pfx : String) (braced : Bool := false) (parentCol : Option Nat := none) :
    PM (List STop) := do
  let mut tops := #[]
  let marker (p : Pos) (m : String) (specs : List String := []) : STop := .const p m specs none (.block p [])
  -- (#503) after a definition, the defaults its function types write, each
  -- a constant `$typeDefault:N` of the parameter's type in its scope, which
  -- the elaborator checks and drops
  let typeDefaults : PM (Array STop) := do
    let ds := (← get).typeDefaults
    modify fun st => { st with typeDefaults := #[] }
    return ds.map fun (p, n, t, e) => .const p s!"{pfx}{typeDefaultPrefix}{n}" [] (some t) e
  -- (after a definition, the records of its members' attributes, each
  -- naming its member `owner.M`)
  let memberAttrs (owner : String) : PM (Array STop) := do
    let as := (← get).attrs
    modify fun st => { st with attrs := #[] }
    return as.map fun (p, place, m, e) => attrTop pfx p place s!"{owner}.{m}" e
  let saved := (← get).topCol
  modify fun st => { st with topCol := col }
  -- (definitions on one line are separated by `;` or `,`: `X:int=0, Y:int=0`,
  -- Book of Verse ch. 1, "Semicolons vs Commas")
  let mut afterSep := false
  -- (the attributes of the definition read last, from where it starts in
  -- `tops`, and its name)
  let mut pending : List (Pos × SExpr) := []
  let mut pendingFrom := 0
  let mut owner := ""
  repeat
    if !pending.isEmpty then
      tops ← ofExcept (attachAttrs tops pendingFrom pending pfx)
      pending := []
    tops := tops ++ (← memberAttrs owner) ++ (← typeDefaults)
    let t0 ← peekT
    if braced then
      if t0.isEof then perr t0 "expected '}' to end the module"
      if t0.isSym "}" then bump; break
      if t0.isSym ";" || t0.isSym "," then bump; continue
    else
      if t0.isEof then break
      if col > 0 && t0.bol && t0.col < col && parentCol.isNone then break
      -- (a module's items are the lines indented more than the line of its
      -- `module:`, each at a column of its own: Book of Verse tests,
      -- Modules/Module.versetest:167, AccessLevelInheritance.versetest:605)
      if let some pc := parentCol then if t0.bol && t0.col ≤ pc then break
      if !t0.bol && (t0.isSym ";" || t0.isSym ",") then bump; afterSep := true; continue
      if (!t0.bol && !afterSep) || (t0.bol && t0.col != col && parentCol.isNone) then
        perr t0 (if col == 0 then "a top-level definition must start at column 0"
          else "a definition in a module must start at the module body's column")
      afterSep := false
    -- `@name` before a definition: its attributes (Book of Verse ch. 12,
    -- "Annotations and Metadata"), on its line or on lines of their own at
    -- the definition's column
    if t0.isSym "@" then
      pending ← parseAttrs
      pendingFrom := tops.size
      let d ← peekT
      if d.isEof || (braced && d.isSym "}") || d.isSym ";" || d.isSym "," then
        perr d "an attribute is followed by the definition it is on"
      if !braced && d.bol && d.col != col && parentCol.isNone then
        perr d (if col == 0 then "a top-level definition must start at column 0"
          else "a definition in a module must start at the module body's column")
      if d.isKw "using" then perr d "an attribute goes on a definition, not on using"
    let t ← peekT
    if t.isKw "using" || (t.isKw "import" && (← peekT 1).isSym "{") then
      -- `using{"relative_path"}` imports a file or directory (#27); other
      -- `using { /Verse.org/… }` module paths are accepted and ignored
      bump
      -- (`using` is reserved: `using:int = 42` is no definition)
      if !(← peekT).isSym "{" then perr (← peekT) s!"expected '\{' after using, found {(← peekT).tok.describe}"
      if (← peekT).isSym "{" then
        if let .str parts := (← peekT 1).tok then
          let path := String.join (parts.filterMap fun | .text s => some s | _ => none)
          modify fun st => { st with imports := st.imports.push (t.pos, path) }
        else if ((← peekT 1).identName?).isSome || (← peekQual 1).isSome then
          -- `using{M}`, `using{A.B}`, `using{(A:)B}`: a module's public
          -- members, unqualified
          bump
          let mut path ← (do
            if let some (q, k) ← peekQual then
              for _ in [0:k] do bump
              return s!"({q}:){← expectIdent}"
            expectIdent)
          while (← peekT).isSym "." do bump; path := path ++ "::" ++ (← expectIdent)
          expectSym "}"
          tops := tops.push (marker t.pos (openMarker pfx path))
      -- (the rest of the `using{…}`, through its own `}`)
      let mut depth : Nat := 0
      repeat
        let n ← peekT
        if n.isEof || (n.bol && n.col ≤ col && depth == 0) then break
        if depth == 0 && braced && (n.isSym "}" || n.isSym ";") then break
        if n.isSym "{" then depth := depth + 1
        if n.isSym "}" then
          depth := depth - 1
          bump
          if depth == 0 then break
          continue
        bump
      continue
    -- (`(q:)name`: a qualified definition, whose qualifier must name the
    -- module it is in, `$qual:A::name|q` for `resolveModules` to check)
    let qual? ← match ← peekQual with
      | some (q, k) => do for _ in [0:k] do bump
                          pure (some q)
      | none => pure none
    -- `(R:t).M(…)`: an extension method, the function `$ext:M` whose first
    -- parameter is the receiver (Book of Verse ch. 6)
    let ext ← if qual?.isSome then pure none else parseExtensionHead?
    let name0 ← match ext with
      | some _ => do pure (extensionName (← expectIdent))
      | none => expectIdent
    let name := pfx ++ name0
    owner := name
    if let some q := qual? then tops := tops.push (marker t.pos (qualMarker name q))
    let pre ← parseSpecs
    let n ← peekT
    if ext.isSome && !n.isSym "(" then perr n noExtensionFields
    -- `name := module:` and its definitions, indented (Book of Verse ch. 16)
    if n.isSym ":=" && (← peekT 1).isKw "module" then
      ofExcept <| EffectPolicy.checkNonFunction t.pos "module" pre
      bump; bump
      let o ← peekT
      let inner ← if o.isSym ":" then do
          bump
          let b ← peekT
          if b.endsEmptyBody col then pure []
          else if !b.bol then perr b "expected the module's definitions, indented on the following lines"
          else withBlock b (parseTopsIn b.col (name ++ "::") (parentCol := some t.col))
        else if o.isSym "{" then do
          bump
          let b ← peekT
          parseTopsIn (if b.bol then b.col else col) (name ++ "::") (braced := true)
        else perr o "expected ':' or '{' after module"
      tops := tops.push (marker t.pos (moduleMarker name) pre)
      tops := tops ++ inner.toArray
      continue
    -- `F of {X:int}:t = …`: a function, its parameters in braces after
    -- `of` (Book of Verse tests, `Operators/Of.versetest:112`); `F at
    -- {…}` defines nothing (`Operators/At.versetest:112`, 3621)
    let ofParams := n.isKw "of" && (← peekT 1).isSym "{"
    if n.isKw "at" && (← peekT 1).isSym "{" then
      perr n s!"{name0} at \{…} defines nothing: a function's parameters are written {name0}(…), or {name0} of \{…}, and one that can fail is {name0}(…)<decides> (Book of Verse tests, Operators/At.versetest: 3621)"
    if ofParams then bump
    let n ← peekT
    let n := if ofParams then { n with tok := .sym "(" } else n
    -- a constant has the effects of its initialiser (#35)
    if !n.isSym "(" then
      ofExcept <| EffectPolicy.checkName t.pos pre
      if let some e := pre.find? EffectPolicy.effectNames.contains then
        perr n s!"a constant cannot have the effect specifier <{e}>: it has the effects of its initialiser"
    if n.isSym "(" then
      bump
      let (ps, tps, binds) ← parseParamList (if ofParams then "}" else ")")
      if ext.isSome && (pre.contains "constructor" || (← peekT).isSym ":=") then
        perr (← peekT) "an extension method is a function, (R:t).M(…)<effects>:type = body (Book of Verse ch. 6)"
      -- (an extension method's receiver, then its parameters)
      let (ps, tps) := match ext with
        | some (r, rtps) => (#[r] ++ ps, rtps.toArray ++ tps)
        | none => (ps, tps)
      if pre.contains "constructor" then
        -- `Name<constructor>(params)<effects> := cls:` and its items (#11):
        -- an `fn` with the effect `$constructor:cls`, expanded with the classes
        let effs ← parseSpecs
        if !(← peekT).isSym ":=" then perr (← peekT) "expected ':=' and the class after a constructor's parameters"
        bump
        let ct ← peekT
        let mut cls ← expectIdent
        -- (`:= M.c:`: a module's class, #112)
        while (← peekT).isSym "." && ((← peekT 1).identName?).isSome && !(← peekT).bol do
          bump; cls := cls ++ "." ++ (← expectIdent)
        -- `:= box(t):` for a parametric class: its type arguments
        let targs ← if (← peekT).isSym "(" && !(← peekT).bol then do
            bump
            let mut ts := #[← parseType]
            while (← peekT).isSym "," do bump; ts := ts.push (← parseType)
            expectSym ")"
            pure ts.toList
          else pure []
        -- (its destructured names, bound by a `let:` first)
        let items := (if binds.isEmpty then [] else [SExpr.app ct.pos (.ident ct.pos "$let") [.block ct.pos binds] false]) ++
          (← parseCtorBody t.col)
        tops := tops.push (.fn t.pos name ps.toList tps.toList
          ((pre.filter (· != "constructor")) ++ effs ++ [constructorSpec cls])
          (if targs.isEmpty then .name cls else .app cls targs) (.block ct.pos items))
        continue
      if (← peekT).isSym ":=" && ((← peekT 1).isKw "class" || (← peekT 1).isKw "interface") then
        ofExcept <| EffectPolicy.checkNonFunction t.pos "type declaration" pre
        -- `name(t:type, …) := class …`: a parametric class (or interface, #53)
        let isIface := (← peekT 1).isKw "interface"
        bump; bump
        if !tps.isEmpty then perr n "a parametric type takes its parameters without a where clause"
        tops := tops.push (← parseClassBody t.pos name pre (← typeParamsOf t.pos n ps) isIface)
        continue
      if (← peekT).isSym ":=" && (← peekT 1).isKw "struct" then
        ofExcept <| EffectPolicy.checkNonFunction t.pos "type declaration" pre
        -- `name(t:type, …) := struct …`: a parametric struct
        let d ← peekT
        bump
        if !tps.isEmpty then perr d "a parametric type takes its parameters without a where clause"
        let tparams ← typeParamsOf t.pos n ps
        match ← parseFnBody with
        | .structDef bp [] specs fs => tops := tops.push (.const t.pos name pre none (.structDef bp tparams specs fs))
        | _ => perr d s!"only structs can be parametric in openverse ({name})"
        continue
      -- `name(u:type, …) := t`: a parametric type alias (Book of Verse ch.
      -- 10, "Aliases")
      if (← peekT).isSym ":=" then
        ofExcept <| EffectPolicy.checkNonFunction t.pos "type declaration" pre
        let d ← peekT
        bump
        if !tps.isEmpty then perr d "a parametric type takes its parameters without a where clause"
        let tparams ← typeParamsOf t.pos n ps
        let a ← peekT
        tops := tops.push (.const t.pos name pre none (.typeAlias a.pos tparams (← parseType)))
        continue
      let effs ← parseSpecs
      accessOnName t.pos name0 effs
      expectSym ":"
      let ret ← parseType
      let a ← peekT
      -- (a declaration with no body, `F():void` on its line: Book of Verse
      -- tests, Roundtrip/Newlines.versetest; openverse has no functions
      -- defined elsewhere, refused)
      if a.isEof || (a.bol && a.col ≤ (← get).topCol) || (!a.bol && (a.isSym ";" || a.isSym ",")) then
        tops := tops.push (.fn t.pos name ps.toList tps.toList (pre ++ effs) ret
          (refusedForm t.pos (.declaredFunction name0) []))
        continue
      if a.isSym "=" || a.isSym ":=" then bump else perr a "expected '=' before the function body"

      tops := tops.push (.fn t.pos name ps.toList tps.toList (pre ++ effs) ret (withBinds binds (← parseFnBody)))
    else if n.isSym ":=" && (← peekT 1).isKw "interface" then
      bump; bump
      tops := tops.push (← parseClassBody t.pos name pre [] true)
    else if n.isSym ":=" && (← peekT 1).isKw "class" then
      bump; bump
      tops := tops.push (← parseClassBody t.pos name pre [] false)
    else if n.isSym ":=" then
      bump
      let a ← peekT
      -- `name := scoped{A, B}`: an access level, which specifiers may name
      -- (Book of Verse ch. 12, "Scoped Definitions"): `$scope(A, B)`, which
      -- `resolveSpecifiers` reads and removes
      if a.identName? == some "scoped" && (← peekT 1).isSym "{" then
        bump
        let refs ← parseScopeRefs
        tops := tops.push (.const t.pos name pre none (.app a.pos (.ident a.pos scopeHead) (refs.map (.ident a.pos ·)) false))
        continue
      -- `name := t`: a type alias, when `t` is written as only a type can be

      if let some ty ← typeAliasRHS? then
        tops := tops.push (.const t.pos name pre none (.typeAlias a.pos [] ty))
        continue
      let b ← parseFnBody
      -- (a module's data states its type, Book of Verse ch. 16, also at a
      -- file's top level, which is a module's scope (the Book's tests,
      -- `Union.versetest` 23, 290); `X := c`, where `c` may be a type, is
      -- `Aliases.expand`'s to decide)
      match b with
      | .structDef .. | .enumDef .. | .refineDef .. => pure ()
      | b => if b.asType?.isNone && !b.isTypeLikeForm then
          perr n s!"a constant {if pfx.isEmpty then "at the top level" else "in a module"} needs its type: write {name0}:t = … (Book of Verse ch. 16: \"type inference with := alone is not allowed\")"
      tops := tops.push (.const t.pos name pre none b)
    else if n.isSym ":" then
      bump
      let ty ← parseType
      let a ← peekT
      if a.isEof || (a.bol && a.col ≤ (← get).topCol) || (!a.bol && (a.isSym ";" || a.isSym ",")) then
        tops := tops.push (.const t.pos name pre (some ty)
          (refusedForm t.pos (.declaredData name0) []))
        continue
      if a.isSym "=" || a.isSym ":=" then bump else perr a "expected '=' in a constant definition"
      tops := tops.push (.const t.pos name pre (some ty) (← parseFnBody))
    else perr n s!"expected '(', ':' or ':=' after '{name}'"
  if !pending.isEmpty then tops ← ofExcept (attachAttrs tops pendingFrom pending pfx)
  tops := tops ++ (← memberAttrs owner) ++ (← typeDefaults)
  modify fun st => { st with topCol := saved }
  return tops.toList

partial def parseTops : PM (List STop) := parseTopsIn 0 ""

/-- Parse one expression (for `openverse run FILE do EXPR`). -/
def parseExprText (src : String) : Except String SExpr := do
  let toks ← lexSource src
  (do
    let e ← parseExpr 0
    let t ← peekT
    if !t.isEof then perr t s!"unexpected {t.tok.describe} after the expression"
    return e : PM SExpr).run' { toks }

/-- A marker that the source may use rationals (`/` or the type
    `rational`): the elaborator then adds the rational helpers (#116). -/
def ratMarker : String := "$uses:rational"

def usesRational (toks : Array Token) : Bool := Id.run do
  -- (not the `/` of a module path, `using { /Verse.org/… }`)
  let mut inUsing := false
  for t in toks do
    if t.isKw "using" then inUsing := true
    else if inUsing && t.isSym "}" then inUsing := false
    else if !inUsing && (t.isSym "/" || t.identName? == some "rational") then return true
  return false

/-- Whether a source text may use rationals (for an expression read from a
    file, as a `.value`'s). -/
def textUsesRational (src : String) : Bool :=
  match lexSource src with
  | .ok toks => usesRational toks
  | .error _ => false

/-- A marker that the source may use `ReplaceAll` (#150). -/
def replaceAllMarker : String := "$uses:replaceAll"

/-- The functions the Book calls bitwise, by their names in a program. -/
def bitwiseFunctions : List String :=
  ["BitAnd", "BitOr", "BitXor", "BitNot", "BitShiftLeft", "BitShiftRight"]

/-- A marker that the source may call a bitwise function (`BitNot` needs no
    helper): the elaborator then adds the helpers (`Front/Bitwise.lean`). -/
def bitwiseMarker : String := "$uses:bitwise"

/-- Whether the source writes a qualifier other than `(super:)`: `(`, a
    name, `.` and names, or a path, then `:)` (`peekQual`'s shape), also in
    a string's interpolations. -/
partial def usesQualifiers (toks : Array Token) : Bool := Id.run do
  for i in [0:toks.size] do
    if let .str parts := toks[i]!.tok then
      for part in parts do
        if let .code src l c := part then
          if let .ok inner := lex src l c then
            if usesQualifiers inner then return true
    if !toks[i]!.isSym "(" then continue
    let mut k := i + 1
    match (toks[k]?.map (·.tok) : Option Tok) with
    | some (.path _) => k := k + 1
    | some (.ident x) =>
      if x == "super" || keywords.contains x then continue
      k := k + 1
      while (toks[k]?.map (·.isSym ".")) == some true && ((toks[k + 1]?.bind (·.identName?))).isSome do
        k := k + 2
    | _ => continue
    if (toks[k]?.map (·.isSym ":")) == some true && (toks[k + 1]?.map (·.isSym ")")) == some true then
      return true
  return false

/-- Whether the source names a bitwise function that needs a helper (all
    but `BitNot`), also in a string's interpolations. -/
partial def usesBitwise (toks : Array Token) : Bool :=
  toks.any fun t => match t.tok with
    | .ident n => n != "BitNot" && bitwiseFunctions.contains n
    | .str parts => parts.any fun
      | .code src l c => match lex src l c with
        | .ok inner => usesBitwise inner
        | .error _ => false
      | _ => false
    | _ => false

def withRatMarker (toks : Array Token) (tops : List STop) : List STop :=
  let p : Pos := { line := 0, col := 0 }
  let tops := if usesRational toks then tops ++ [.const p ratMarker [] none (.block p [])] else tops
  let tops := if usesQualifiers toks then tops ++ [.const p qualifierMarker [] none (.block p [])] else tops
  let tops := if toks.any (·.identName? == some "ReplaceAll") then tops ++ [.const p replaceAllMarker [] none (.block p [])]
    else tops
  if usesBitwise toks then tops ++ [.const p bitwiseMarker [] none (.block p [])] else tops

/-- The definitions of a source file, and the marker of its `case` arms
    marked `@ignore_unreachable` (`ignoredArmsMarker`), if any. -/
def withIgnoredArms (tops : List STop) (st : PSt) : List STop :=
  if st.ignoredArms.isEmpty then tops else
  let p : Pos := { line := 0, col := 0 }
  tops ++ [.const p ignoredArmsMarker [] none (.block p (st.ignoredArms.toList.map (.ident · "")))]

/-- Parse a source file: its definitions, and the files it imports. `file`
    names it in error positions (empty for the main file). -/

def parseProgramImports (src : String) (file : String := "") :
    Except String (List STop × List (Pos × String)) := do
  let toks ← lexSource src
  let toks := if file.isEmpty then toks else toks.map fun t => { t with file }
  let (tops, st) ← parseTops.run { toks }
  return (withRatMarker toks (withIgnoredArms tops st), st.imports.toList)

/-- Parse a whole Verse source file. -/
def parseProgram (src : String) : Except String (List STop) := do
  let toks ← lexSource src
  let (tops, st) ← parseTops.run { toks }
  return withRatMarker toks (withIgnoredArms tops st)

/-- Parse the source of built-in helpers, renaming the given names to
    `$name`, which no program can write or define. -/
def parsePrelude (src : String) (names : List String) : Except String (List STop) := do
  let toks ← lexSource src
  let toks := toks.map fun t => match t.tok with
    | .ident x => if names.contains x then { t with tok := .ident ("$" ++ x) } else t
    | _ => t
  parseTops.run' { toks }

end OpenVerse.Front
