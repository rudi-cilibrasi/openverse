/-
  OpenVerse front end — lexer.

  Produces tokens with their line and column. Layout (indented blocks) is
  handled by the parser from the columns, with an offside rule: see
  `OpenVerse.Front.Parser`.

  Source text, per Verse's lexical grammar:
  * a source file is UTF-8 (`decodeSource` rejects malformed bytes at their
    line and column), and a byte order mark U+FEFF as its first character is
    skipped;
  * these characters are rejected anywhere, including inside strings, char
    literals and comments: C0 controls other than tab, LF and CR; DEL; C1
    controls U+0080–U+009F; U+2028 and U+2029;
  * LF, CR LF and a lone CR are each exactly one line break, for line and
    column numbers, the start-of-line flag, the end of `#` comments, and
    string literals (which cannot contain one);
  * columns count characters, so a tab is one column; each token that starts
    a line carries its line's indentation (its leading tabs and spaces), which
    the parser checks for a consistent use of tabs and spaces.

  Supported lexical syntax (Book of Verse, ch. 1 "Expressions", ch. 2
  "Primitives"): `#` line comments, nested `<# … #>` block comments, `<#>`
  indented comments, identifiers, decimal and `0x` hex integer literals,
  `'c'` char literals (`c` printable ASCII U+0020–U+007E, or an escape),
  `0oHH` char literals (one or two hex digits: that UTF-8 code unit, so
  `0o41` is 'A'; `0o` is not octal), string literals with escapes and `{…}`
  interpolation, and the operator symbols of ch. 4. Not supported: float
  literals, `0u` char32 literals, path literals.

  A `<#>` indented comment is the rest of its line and every following line
  indented more than the line that contains the `<#>` (blank lines included).
  It ends before the first non-blank line indented no more than that line.
  `<#` opens a nested block comment only when the next character is not `>`.
-/
namespace OpenVerse.Front

/-- A piece of a string literal: text (bytes), or an interpolated expression. -/
inductive StrPart where
  | text : String → StrPart
  /-- Source of the interpolant and the position where it starts. -/
  | code : String → Nat → Nat → StrPart
  deriving Repr, Inhabited

inductive Tok where
  | ident : String → Tok
  | int   : Int → Tok
  | char  : Nat → Tok
  | str   : List StrPart → Tok
  | sym   : String → Tok
  | eof   : Tok
  deriving Repr, Inhabited

structure Token where
  tok  : Tok
  line : Nat
  col  : Nat
  /-- The first token on its line. -/
  bol  : Bool
  /-- When `bol`: the indentation (leading tabs and spaces) of the token's line. -/
  indent : String := ""
  deriving Repr, Inhabited

def Tok.describe : Tok → String
  | .ident s => s!"'{s}'"
  | .int i => s!"{i}"
  | .char c => s!"char {c}"
  | .str _ => "string literal"
  | .sym s => s!"'{s}'"
  | .eof => "end of file"

structure LexSt where
  cs   : Array Char
  pos  : Nat := 0
  line : Nat := 1
  col  : Nat := 0
  /-- No token emitted yet on the current line. -/
  bol  : Bool := true
  /-- Where the current line starts in `cs`. -/
  lineStart : Nat := 0

abbrev LexM := StateT LexSt (Except String)

/-- The length of the line break at `pos` (LF, CR LF or a lone CR), or 0. -/
def breakLen (cs : Array Char) (pos : Nat) : Nat :=
  match cs[pos]? with
  | some '\n' => 1
  | some '\r' => if cs[pos + 1]? == some '\n' then 2 else 1
  | _ => 0

/-- Move past one character; a line break (CR LF included) counts as one. -/
def LexSt.step (s : LexSt) : LexSt :=
  match breakLen s.cs s.pos with
  | 0 => if s.pos < s.cs.size then { s with pos := s.pos + 1, col := s.col + 1 } else s
  | n => { s with pos := s.pos + n, line := s.line + 1, col := 0, bol := true, lineStart := s.pos + n }

def peekC (k : Nat := 0) : LexM (Option Char) := do
  let s ← get
  return s.cs[s.pos + k]?

def advance : LexM Unit := modify LexSt.step

def lexErr (msg : String) : LexM α := do
  let s ← get
  throw s!"{s.line}:{s.col}: {msg}"

/-- The leading tabs and spaces from `i` on. -/
def indentAt (cs : Array Char) (i : Nat) : String := Id.run do
  let mut acc := ""
  let mut j := i
  while h : j < cs.size do
    let c := cs[j]
    if c == ' ' || c == '\t' then acc := acc.push c; j := j + 1 else break
  return acc

/-- `U+XXXX` (at least four upper-case hex digits). -/
def uPlus (n : Nat) : String :=
  let h := String.ofList ((Nat.toDigits 16 n).map Char.toUpper)
  "U+" ++ String.ofList (List.replicate (4 - h.length) '0') ++ h

/-- Characters that may not appear anywhere in Verse source. -/
def forbiddenChar (c : Char) : Bool :=
  let n := c.toNat
  (n < 0x20 && c != '\t' && c != '\n' && c != '\r') || n == 0x7F || (0x80 ≤ n && n ≤ 0x9F) ||
    n == 0x2028 || n == 0x2029

/-- Reject the first forbidden character of the source, at its line and column.
    The state is unchanged when there is none. -/
def checkChars : LexM Unit := do
  let s ← get
  match (s.cs.extract s.pos s.cs.size).findIdx? forbiddenChar with
  | none => pure ()
  | some k =>
    let i := s.pos + k
    let at_ := Id.run do
      let mut t := s
      while t.pos < i do t := t.step
      return t
    throw s!"{at_.line}:{at_.col}: character {uPlus s.cs[i]!.toNat} is not allowed in Verse source"

/-- Skip to the end of the current line (the line break is not consumed). -/
partial def skipRestOfLine : LexM Unit := do
  let s ← get
  if s.pos < s.cs.size && breakLen s.cs s.pos == 0 then advance; skipRestOfLine

/-- Skip a nested block comment; the opening `<#` is already consumed. -/
partial def skipBlockComment (depth : Nat) : LexM Unit := do
  match ← peekC, ← peekC 1 with
  | none, _ => lexErr "unterminated block comment"
  | some '#', some '>' => advance; advance; if depth > 1 then skipBlockComment (depth - 1)
  | some '<', some '#' =>
    -- `<#>` is not a nested block comment
    if (← peekC 2) == some '>' then advance; skipBlockComment depth
    else advance; advance; skipBlockComment (depth + 1)
  | _, _ => advance; skipBlockComment depth

/-- Skip a `<#>` indented comment, at its `<#>`: the rest of the line, then
    every following line that is blank or indented more than the line of the
    `<#>`. Stops at the line break before the first other line. -/
partial def skipIndentedComment : LexM Unit := do
  let s ← get
  let base := (indentAt s.cs s.lineStart).length
  advance; advance; advance
  skipRestOfLine
  let rec lines : LexM Unit := do
    let s ← get
    let b := breakLen s.cs s.pos
    if b == 0 then return
    let next := s.pos + b
    let w := (indentAt s.cs next).length
    let blank := next + w ≥ s.cs.size || breakLen s.cs (next + w) > 0
    if blank || w > base then
      advance; skipRestOfLine; lines
  lines

partial def skipSpace : LexM Unit := do
  match ← peekC, ← peekC 1 with
  | some ' ', _ | some '\t', _ | some '\r', _ | some '\n', _ => advance; skipSpace
  | some '#', _ => skipRestOfLine; skipSpace
  | some '<', some '#' =>
    if (← peekC 2) == some '>' then skipIndentedComment
    else advance; advance; skipBlockComment 1
    skipSpace
  | _, _ => pure ()

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'
def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c ∧ c ≤ 'f') || ('A' ≤ c ∧ c ≤ 'F')

def escapeChar : Char → Option Char
  | 't' => some '\t' | 'n' => some '\n' | 'r' => some '\r' | '"' => some '"'
  | '\'' => some '\'' | '\\' => some '\\' | '{' => some '{' | '}' => some '}'
  | '<' => some '<' | '>' => some '>' | '&' => some '&' | '#' => some '#' | '~' => some '~'
  | _ => none

/-- Consume one character (a CR LF line break as a whole) and append it to `acc`. -/
def advanceInto (acc : String) : LexM String := do
  let s ← get
  advance
  let s' ← get
  return (s.cs.extract s.pos s'.pos).foldl String.push acc

/-- Read the source of an interpolant up to its matching `}` (consumed). -/
partial def readInterp (acc : String) (depth : Nat) : LexM String := do
  match ← peekC with
  | none => lexErr "unterminated interpolation"
  | some '}' =>
    advance
    if depth == 0 then return acc else readInterp (acc.push '}') (depth - 1)
  | some '{' => advance; readInterp (acc.push '{') (depth + 1)
  | some '"' =>
    -- a nested string literal: copy it verbatim
    advance
    let rec copyStr (a : String) : LexM String := do
      match ← peekC with
      | none => lexErr "unterminated string"
      | some '\\' => advance; match ← peekC with
        | some _ => copyStr (← advanceInto (a.push '\\'))
        | none => lexErr "unterminated string"
      | some '"' => advance; return a.push '"'
      | some _ => copyStr (← advanceInto a)
    readInterp (← copyStr (acc.push '"')) depth
  | some _ => readInterp (← advanceInto acc) depth

partial def readString (parts : Array StrPart) (cur : String) : LexM (List StrPart) := do
  match ← peekC with
  | none | some '\n' | some '\r' => lexErr "unterminated string literal"
  | some '"' =>
    advance
    let parts := if cur.isEmpty then parts else parts.push (.text cur)
    return parts.toList
  | some '\\' =>
    advance
    match ← peekC with
    | some c => match escapeChar c with
      | some e => advance; readString parts (cur.push e)
      | none => lexErr s!"unknown escape \\{c}"
    | none => lexErr "unterminated string literal"
  | some '{' =>
    advance
    let s ← get
    let (l, c) := (s.line, s.col)
    let code ← readInterp "" 0
    let parts := if cur.isEmpty then parts else parts.push (.text cur)
    -- empty interpolants (only whitespace) are ignored (Book of Verse §1.6)
    if code.all Char.isWhitespace then readString parts "" else readString (parts.push (.code code l c)) ""
  | some c => advance; readString parts (cur.push c)

partial def readWhile (p : Char → Bool) (acc : String) : LexM String := do
  match ← peekC with
  | some c => if p c then do advance; readWhile p (acc.push c) else return acc
  | none => return acc

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- The symbols, longest first. -/
def symbols : List String :=
  ["<decides>", ":=", "<>", "<=", ">=", "..", "->", "=>", "+=", "-=", "*=", "/=",
   "(", ")", "[", "]", "{", "}", ",", ";", ":", "=", "<", ">", "+", "-", "*", "/", ".", "?"]

def matchSym (cs : Array Char) (pos : Nat) : Option String :=
  -- `<decides>` and friends are lexed by the parser from `<`, ident, `>`
  symbols.filter (· != "<decides>") |>.find? fun s =>
    let sc := s.toList
    (List.range sc.length).all fun k => cs[pos + k]? == sc[k]?

partial def lexAll (acc : Array Token) : LexM (Array Token) := do
  skipSpace
  let s ← get
  let mk (t : Tok) : Token :=
    { tok := t, line := s.line, col := s.col, bol := s.bol,
      indent := if s.bol then indentAt s.cs s.lineStart else "" }
  let emit (t : Tok) : LexM (Array Token) := do
    modify fun st => { st with bol := false }
    return acc.push (mk t)
  let errHere (msg : String) : LexM Unit := throw s!"{s.line}:{s.col}: {msg}"
  match ← peekC with
  | none => return acc.push (mk .eof)
  | some c =>
    if isIdStart c then
      let id ← readWhile isIdChar ""
      lexAll (← emit (.ident id))
    else if c.isDigit then
      if c == '0' && (← peekC 1) == some 'x' then
        advance; advance
        let h ← readWhile isHex ""
        if h.isEmpty then lexErr "empty hex literal"
        lexAll (← emit (.int (h.foldl (fun n c => n * 16 + hexVal c) 0)))
      else if c == '0' && (← peekC 1) == some 'o' then
        -- `0oHH`: a char given by its code unit in hex (not octal)
        advance; advance
        let h ← readWhile isHex ""
        let trailing := ((← peekC).map isIdChar).getD false
        if h.isEmpty || h.length > 2 || trailing then
          errHere "a 0o char literal needs one or two hex digits, not followed by a letter, digit or '_' (0o41 is 'A')"
        lexAll (← emit (.char (h.foldl (fun n c => n * 16 + hexVal c) 0)))
      else
        let d ← readWhile Char.isDigit ""
        if (← peekC) == some '.' && ((← peekC 1).map Char.isDigit).getD false then
          lexErr "float literals are not supported by openverse v1"
        lexAll (← emit (.int d.toNat!))
    else if c == '"' then
      advance
      let parts ← readString #[] ""
      lexAll (← emit (.str parts))
    else if c == '\'' then
      advance
      let ch ← match ← peekC with
        | some '\\' => do
          advance
          match (← peekC).bind escapeChar with
          | some e => advance; pure e
          | none => lexErr "bad escape in char literal"
        | some ch => do
          if ch.toNat ≥ 128 then lexErr "non-ASCII char literals (char32) are not supported by openverse v1"
          if ch.toNat < 0x20 || ch.toNat == 0x7F then
            let hint := if ch == '\t' then " (write '\\t' for a tab)" else ""
            lexErr s!"a char literal must be a printable ASCII character or an escape, not {uPlus ch.toNat}{hint}"
          advance; pure ch
        | none => lexErr "unterminated char literal"
      if (← peekC) != some '\'' then lexErr "char literal must be one character"
      advance
      lexAll (← emit (.char ch.toNat))
    else match matchSym s.cs s.pos with
      | some sym =>
        for _ in [0:sym.length] do advance
        lexAll (← emit (.sym sym))
      | none =>
        let code := if c.toNat < 0x7F then "" else s!" ({uPlus c.toNat})"
        lexErr s!"unexpected character '{c}'{code}"

/-- Tokenise a piece of source text (positions start at `line`, `col`), such as an interpolant. -/
def lex (src : String) (line : Nat := 1) (col : Nat := 0) : Except String (Array Token) :=
  (lexAll #[]).run' { cs := src.toList.toArray, line, col, bol := line == 1 && col == 0 }

/-- The byte order mark U+FEFF. -/
def bom : Char := Char.ofNat 0xFEFF

/-- Tokenise a whole source file: skip a leading byte order mark, reject
    forbidden characters, then lex. -/
def lexSource (src : String) : Except String (Array Token) :=
  let cs := src.toList.toArray
  let start := if cs[0]? == some bom then 1 else 0
  (do checkChars; lexAll #[]).run' { cs, pos := start, lineStart := start }

/-- The offset of the first byte of `b` (from `i`) that does not start a
    well-formed UTF-8 sequence, or `b.size`. -/
partial def utf8BadOffset (b : ByteArray) (i : Nat := 0) : Nat :=
  if i < b.size then
    let c := b[i]!.toNat
    let inR (k lo hi : Nat) : Bool :=
      match b[i + k]? with
      | some x => lo ≤ x.toNat && x.toNat ≤ hi
      | none => false
    let tail (n : Nat) : Bool := (List.range' 1 (n - 1)).all fun k => inR k 0x80 0xBF
    let n :=
      if c < 0x80 then 1
      else if 0xC2 ≤ c && c ≤ 0xDF && tail 2 then 2
      else if c == 0xE0 && inR 1 0xA0 0xBF && inR 2 0x80 0xBF then 3
      else if c == 0xED && inR 1 0x80 0x9F && inR 2 0x80 0xBF then 3
      else if 0xE1 ≤ c && c ≤ 0xEF && c != 0xED && tail 3 then 3
      else if c == 0xF0 && inR 1 0x90 0xBF && inR 2 0x80 0xBF && inR 3 0x80 0xBF then 4
      else if 0xF1 ≤ c && c ≤ 0xF3 && tail 4 then 4
      else if c == 0xF4 && inR 1 0x80 0x8F && inR 2 0x80 0xBF && inR 3 0x80 0xBF then 4
      else 0
    if n == 0 then i else utf8BadOffset b (i + n)
  else b.size

/-- Decode the bytes of a source file. Malformed UTF-8 is an error at the line
    and column of its first byte. -/
def decodeSource (b : ByteArray) : Except String String :=
  match String.fromUTF8? b with
  | some s => .ok s
  | none =>
    let i := utf8BadOffset b
    let pre := (String.fromUTF8? (b.extract 0 i)).getD ""
    let cs := pre.toList.toArray
    let start := if cs[0]? == some bom then 1 else 0
    let s := Id.run do
      let mut s : LexSt := { cs, pos := start, lineStart := start }
      while s.pos < cs.size do s := s.step
      return s
    let byte := match b[i]? with | some x => s!" (byte 0x{String.ofList ((Nat.toDigits 16 x.toNat).map Char.toUpper)})" | none => ""
    .error s!"{s.line}:{s.col}: the file is not valid UTF-8{byte}"

end OpenVerse.Front
