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
  `0o41` is 'A'; `0o` is not octal), `0uHHHHHH` char32 literals (a Unicode
  scalar value, up to `0u10FFFF`), string
  literals with escapes and `{…}` interpolation, float literals, path
  literals (`/Verse.org/Random`, where an operand starts: see `readPath`),
  and the operator symbols of ch. 4.

  A `<#>` indented comment is the rest of its line and every following line
  indented more than the line that contains the `<#>` (blank lines included).
  It ends before the first non-blank line indented no more than that line.
  `<#` opens a nested block comment only when the next character is not `>`.
-/
import OpenVerse.Core.Float
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
  /-- A `0u` char32 literal: a Unicode scalar value. -/
  | char32 : Nat → Tok
  /-- A float literal (#127): the bits of the nearest double, canonical. -/
  | float : UInt64 → Tok
  | str   : List StrPart → Tok
  /-- A path literal `/Verse.org/Random` (Book of Verse ch. 1, "Path
      Literals"; ch. 16, "Paths"). -/
  | path  : String → Tok
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
  /-- The file the token comes from, when it is not the main one (#27). -/
  file : String := ""
  deriving Repr, Inhabited

def Tok.describe : Tok → String
  | .ident s => s!"'{s}'"
  | .int i => s!"{i}"
  | .char c => s!"char {c}"
  | .char32 c => s!"char32 {c}"
  | .float b => s!"float {VFloat.render b}"
  | .str _ => "string literal"
  | .path p => s!"path {p}"
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

/-- The identifiers the parser reserves for its forms. -/
def keywords : List String :=
  ["if", "then", "else", "for", "do", "loop", "break", "return", "var", "set", "and", "or",
   "not", "case", "block", "option", "logic", "array", "using", "struct", "enum", "map", "where",
   "defer"]

/-- Whether a token can end an operand, so that a `/` after it divides:
    a name other than a keyword, a literal, or a closing bracket or `?`. -/
def Tok.endsOperand : Tok → Bool
  | .ident x => !keywords.contains x
  | .int _ | .char _ | .char32 _ | .float _ | .str _ | .path _ => true
  | .sym s => [")", "]", "}", "?"].contains s
  | .eof => false

/-- The characters of a path's label: ASCII letters and digits, `.`, `-`. -/
def isLabelChar (c : Char) : Bool := c.isAlphanum || c == '.' || c == '-'

/-- A path literal, at its `/` (Book of Verse ch. 1, "Path Literals"; ch. 16,
    "Paths"): `/` and a label, which starts with a letter or digit, then
    optionally `@` and a label (`/user@example.com`), then segments `/X`,
    each an identifier (which may end in a quoted part, `/a/b'+'`) that a
    qualifier `(/path:)` may precede. A path cannot be followed by `/` or
    `@`: `/a/1b` and `/a@b@c` are errors. -/
partial def readPath : LexM String := do
  advance
  let mut p := "/" ++ (← readWhile isLabelChar "")
  if (← peekC) == some '@' then
    advance
    if !(((← peekC).map Char.isAlphanum).getD false) then
      lexErr "expected a label after '@' in a path: a letter or digit, then letters, digits, '.' and '-'"
    p := p ++ "@" ++ (← readWhile isLabelChar "")
  repeat
    if (← peekC) != some '/' then break
    let qualified := (← peekC 1) == some '(' && (← peekC 2) == some '/'
    if !qualified && !(((← peekC 1).map isIdStart).getD false) then break
    advance
    if qualified then
      advance
      let q ← readPath
      if (← peekC) != some ':' || (← peekC 1) != some ')' then
        lexErr "expected ':)' to end the qualifier of a path's segment"
      advance; advance
      p := p ++ "/(" ++ q ++ ":)"
      if !(((← peekC).map isIdStart).getD false) then lexErr "expected an identifier after a path's qualifier"
    else p := p ++ "/"
    p := p ++ (← readWhile isIdChar "")
    -- (`b'+'`: an identifier with a quoted part)
    if (← peekC) == some '\'' then
      advance
      let q ← readWhile (fun c => c != '\'' && c != '\n' && c != '\r') ""
      if q.isEmpty || (← peekC) != some '\'' then lexErr "expected the quoted part of a path's identifier, ending in '"
      advance
      p := p ++ "'" ++ q ++ "'"
  if (← peekC) == some '/' || (← peekC) == some '@' then
    lexErr "a path's segments after its label are identifiers: '/' must be followed by a letter or '_', and '@' comes once, after the first label"
  return p

/-- The symbols, longest first. -/
def symbols : List String :=
  ["<decides>", ":=", "<>", "<=", ">=", "..", "->", "=>", "+=", "-=", "*=", "/=",
   "(", ")", "[", "]", "{", "}", ",", ";", ":", "=", "<", ">", "+", "-", "*", "/", ".", "?", "|"]

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
      else if c == '0' && (← peekC 1) == some 'u' then
        -- `0uHHHHHH`: a char32, a Unicode scalar value
        advance; advance
        let h ← readWhile isHex ""
        let trailing := ((← peekC).map isIdChar).getD false
        let v := h.foldl (fun n c => n * 16 + hexVal c) 0
        if h.isEmpty || h.length > 6 || trailing then
          errHere "a 0u char32 literal needs one to six hex digits, not followed by a letter, digit or '_' (0u1F600)"
        if v > 0x10FFFF then errHere s!"0u{h} is past the last Unicode code point, 0u10FFFF"
        if 0xD800 ≤ v && v ≤ 0xDFFF then errHere s!"0u{h} is a UTF-16 surrogate, not a Unicode scalar value"
        lexAll (← emit (.char32 v))
      else
        let d ← readWhile Char.isDigit ""
        let digitAt (k : Nat) : LexM Bool := do return ((← peekC k).map Char.isDigit).getD false
        let isE : LexM Bool := do return (← peekC) == some 'e' || (← peekC) == some 'E'
        let expAhead : LexM Bool := do
          return (← isE) && ((← digitAt 1) || (((← peekC 1) == some '+' || (← peekC 1) == some '-') && (← digitAt 2)))
        let frac := (← peekC) == some '.' && (← digitAt 1)
        if frac || (← expAhead) then
          -- a float (#127): digits, then `.` and digits, or an exponent `e±N`,
          -- or both (`1e3` too, as in shipped Verse); the nearest double
          -- (`Float.ofScientific` rounds correctly)
          let mut f := ""
          if frac then
            advance
            f ← readWhile Char.isDigit ""
          let mut ex : Int := 0
          if ← expAhead then
            advance
            let neg := (← peekC) == some '-'
            if (← peekC) == some '+' || (← peekC) == some '-' then advance
            let es ← readWhile Char.isDigit ""
            ex := if neg then -(es.toNat! : Int) else es.toNat!
          if ((← peekC).map isIdChar).getD false then
            lexErr "a float literal is digits, a point and digits, then an optional exponent (1.5, 2.0e-7, 1e3)"
          let m := (d ++ f).toNat!
          let e10 : Int := ex - f.length
          let x : Float := if e10 < 0 then Float.ofScientific m true e10.natAbs else Float.ofScientific m false e10.toNat
          return (← lexAll (← emit (.float (VFloat.canon x))))
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
          if ch.toNat ≥ 128 then
            lexErr s!"a char literal must be ASCII: write {uPlus ch.toNat} as the char32 literal 0u{(String.ofList (Nat.toDigits 16 ch.toNat)).toUpper}"
          if ch.toNat < 0x20 || ch.toNat == 0x7F then
            let hint := if ch == '\t' then " (write '\\t' for a tab)" else ""
            lexErr s!"a char literal must be a printable ASCII character or an escape, not {uPlus ch.toNat}{hint}"
          advance; pure ch
        | none => lexErr "unterminated char literal"
      if (← peekC) != some '\'' then lexErr "char literal must be one character"
      advance
      lexAll (← emit (.char ch.toNat))
    else if c == '/' && (((← peekC 1).map Char.isAlphanum).getD false) &&
        !((acc.back?.map (·.tok.endsOperand)).getD false) then
      -- (a `/` where an operand starts, before a letter or digit)
      lexAll (← emit (.path (← readPath)))
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
