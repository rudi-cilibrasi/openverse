/-
  OpenVerse front end — `ToDiagnostic` (the Book of Verse's API reference:
  `ToDiagnostic(Value:any)<predicts><reads>:diagnostic`, "Accepts any value
  at all"), written in Verse (docs/research/to-diagnostic.md).

  A program that calls `ToDiagnostic` (the parser's marker
  `$uses:diagnostic`) gets the helpers below: the interface `$anything`,
  whose method `$Diagnose` prints a value, the class `diagnostic` with its
  `String`, the interface `diagnosable`, `ToDiagnostic` itself, and the
  printers of strings, chars and rationals. In such a program, and only
  there, an `any` keeps what it needs to print itself: a value of type `t`
  converted to `any` is an object of the class `$any_t` the front end
  writes for `t` (`wrapperDecls`), below `$anything`, whose `$Diagnose`
  calls the printer of `t`, a function `$diag_t` of its own; Verse Core,
  its proofs, OVBC and the runtime are unchanged (`any` is a reference
  type there). The wrapper classes and printers are asked for by the
  elaboration of the conversions (`Requests.anys`) and added in the next
  round, as subtype dictionaries are.
-/
import OpenVerse.Front.Types
import OpenVerse.Front.Parser
import OpenVerse.Front.BuiltinValues

namespace OpenVerse.Front.Diagnostic

/-- The interface every value converted to `any` is an object below, in a
    program that calls `ToDiagnostic`. -/
def anyInterface : String := anyInterfaceName

/-- The class of the empty value as an `any` (`void`, `tuple()`): the
    class below `$anything` that a slot of type `any` starts as. -/
def anyEmpty : String := "$anyEmpty"

/-- The method that prints an `any`. -/
def diagnoseMethod : String := "$Diagnose"

/-- The names of the helpers' definitions, parameters and locals that no
    program may write: each becomes `$name` (`parsePrelude`). -/
def preludeNames : List String :=
  ["anything", "anyEmpty", "Diagnose", "asAnything", "diagHex", "diagHex2", "diagEscaped", "diagChar",
   "diagChar32", "diagByte", "diagCont", "diagSeq", "diagString", "diagJoin", "diagArray", "diagMap",
   "diagRational", "rationalParts", "dValue", "dN", "dM", "dOut", "dR", "dQ", "dD", "dE", "dC", "dS",
   "dI", "dB", "dB0", "dC1", "dC2", "dC3", "dLo", "dHi", "dSeq", "dCP", "dP", "dParts"]

/-- The helpers, in Verse. The format is the Book of Verse's tests'
    (`Tests/Intrinsics/ToDiagnostic.versetest`): a char printable in ASCII
    in quotes, `'a'`, with `\t`, `\n`, `\r` and the characters a string
    escapes written escaped (`'\#'`), any other as `0oXX`; a char32 as
    `0uX`; a string in double quotes, escaped, a valid UTF-8 sequence of
    more than one byte as `{0uX}` and a byte of no valid sequence, or a
    control character, as `{0oXX}`; an array of one element `array{X}`, of
    any other number `(X, Y)`; a map `map{K => V, …}`; a rational reduced,
    `N/D`, or its int. -/
def prelude : String := "
anything := interface<computes>:
    Diagnose()<reads>:string

anyEmpty := class<computes>(anything):
    Diagnose<override>()<reads>:string = \"false\"

diagnosable := interface<computes>:
    GetDiagnostic()<reads>:diagnostic

diagnostic := class<computes>(diagnosable):
    String<public>:string
    GetDiagnostic<override>()<reads>:diagnostic = Self

ToDiagnostic(dValue:any)<reads>:diagnostic = diagnostic{String := asAnything(dValue).Diagnose()}

diagHex(dN:int)<computes>:string =
    var dOut:string = \"\"
    var dM:int = dN
    loop:
        if (dR := Mod[dM, 16], dQ := Quotient[dM, 16], dD := \"0123456789abcdef\"[dR]):
            set dOut = array{dD} + dOut
            set dM = dQ
        if (dM = 0) then break
    dOut

diagHex2(dN:int)<computes>:string = if (dN < 16) then \"0\" + diagHex(dN) else diagHex(dN)

diagEscaped(dN:int)<computes>:?string =
    if (dN = 9) then option{\"\\\\t\"} else if (dN = 10) then option{\"\\\\n\"} else if (dN = 13) then option{\"\\\\r\"}
    else if (dN = 34 or dN = 35 or dN = 38 or dN = 39 or dN = 60 or dN = 62 or dN = 92 or dN = 123 or dN = 125 or dN = 126, dC := dN.ToChar[]) then option{\"\\\\\" + array{dC}}
    else false

diagChar(dC:char)<computes>:string =
    dN := dC.ToCodeUnit()
    if (dE := diagEscaped(dN)?) then \"'\" + dE + \"'\"
    else if (dN >= 32, dN <= 126) then \"'\" + array{dC} + \"'\"
    else \"0o\" + diagHex2(dN)

diagChar32(dC:char32)<computes>:string = \"0u\" + diagHex(dC.ToCodePoint())

diagByte(dS:string, dI:int)<computes>:int = if (dC := dS[dI]) then dC.ToCodeUnit() else -1

diagCont(dS:string, dI:int, dLo:int, dHi:int)<computes><decides>:int =
    dB := diagByte(dS, dI)
    dB >= dLo
    dB <= dHi
    dB - 128

diagSeq(dS:string, dI:int)<computes>:tuple(int, int) =
    dB0 := diagByte(dS, dI)
    if (dB0 < 128) then (1, dB0)
    else if (dB0 >= 194, dB0 <= 223, dC1 := diagCont[dS, dI + 1, 128, 191]) then (2, (dB0 - 192) * 64 + dC1)
    else if (dB0 >= 224, dB0 <= 239,
             dC1 := (if (dB0 = 224) then diagCont[dS, dI + 1, 160, 191] else if (dB0 = 237) then diagCont[dS, dI + 1, 128, 159] else diagCont[dS, dI + 1, 128, 191]),
             dC2 := diagCont[dS, dI + 2, 128, 191]) then (3, ((dB0 - 224) * 64 + dC1) * 64 + dC2)
    else if (dB0 >= 240, dB0 <= 244,
             dC1 := (if (dB0 = 240) then diagCont[dS, dI + 1, 144, 191] else if (dB0 = 244) then diagCont[dS, dI + 1, 128, 143] else diagCont[dS, dI + 1, 128, 191]),
             dC2 := diagCont[dS, dI + 2, 128, 191], dC3 := diagCont[dS, dI + 3, 128, 191]) then (4, (((dB0 - 240) * 64 + dC1) * 64 + dC2) * 64 + dC3)
    else (1, -1)

diagString(dS:string)<computes>:string =
    var dOut:string = \"\\\"\"
    var dI:int = 0
    loop:
        if (dI >= dS.Length) then break
        dSeq := diagSeq(dS, dI)
        dN := dSeq(0)
        dCP := dSeq(1)
        if (dCP < 0, dB := diagByte(dS, dI)):
            set dOut += \"\\{0o\" + diagHex2(dB) + \"\\}\"
        else if (dN > 1):
            set dOut += \"\\{0u\" + diagHex(dCP) + \"\\}\"
        else if (dE := diagEscaped(dCP)?):
            set dOut += dE
        else if (dCP >= 32, dCP <= 126, dC := dCP.ToChar[]):
            set dOut += array{dC}
        else:
            set dOut += \"\\{0o\" + diagHex2(dCP) + \"\\}\"
        set dI += dN
    dOut + \"\\\"\"

diagJoin(dParts:[]string)<computes>:string =
    var dOut:string = \"\"
    for (dI -> dP : dParts):
        if (dI > 0) then set dOut += \", \"
        set dOut += dP
    dOut

diagArray(dParts:[]string)<computes>:string =
    if (dParts.Length = 1, dP := dParts[0]) then \"array\\{\" + dP + \"\\}\" else \"(\" + diagJoin(dParts) + \")\"

diagMap(dParts:[]string)<computes>:string = \"map\\{\" + diagJoin(dParts) + \"\\}\"

diagRational(dP:tuple(int, int))<computes>:string =
    if (dP(1) = 1) then ToString(dP(0)) else ToString(dP(0)) + \"/\" + ToString(dP(1))
"

/-- The names of the Book's definitions the helpers give: a program that
    defines one of them itself gets none of the helpers (its own are the
    ones it calls, and its `any` is unchanged). -/
def bookNames : List String := ["ToDiagnostic", "diagnostic", "diagnosable"]

/-- The helpers, parsed (their names renamed). -/
def tops : Except String (List STop) := parsePrelude prelude preludeNames

/-- A name made of the letters and digits of `s`, every other character
    written as its code. -/
def safeName (s : String) : String :=
  s.foldl (fun acc c => if c.isAlphanum then acc.push c else acc ++ s!"_{c.toNat}_") ""

/-- The class of the values of type `t` converted to `any`. -/
def wrapperName (t : Ty) : String := s!"$any_{safeName t.show}"

/-- The function that prints a value of type `t`. -/
def printerName (t : Ty) : String := s!"$diag_{safeName t.show}"

/-- Whether a type's values are written by a class or interface the front
    end writes for another purpose, which `ToDiagnostic` cannot print yet:
    a function type's shape (`$fn…`), a type value (`$type:…`), the
    compiler's own. -/
def hiddenName (n : String) : Bool := n.startsWith "$"

/-- A definition's name as `ToDiagnostic` prints it: a module member's
    with its module's path as a qualifier, `(M.N:)c`; one at the top level
    bare, as openverse's top level has no path (the Book's tests print
    the test runner's package, `(/Verse.org/VerseTests:)c`). -/
def displayName (n : String) : String :=
  match n.splitOn "::" with
  | [x] => x
  | parts => s!"({".".intercalate parts.dropLast}:){parts.getLast!}"

section Build
variable (p : Pos)

private def str (s : String) : SExpr := .str p [.text s]
private def id (n : String) : SExpr := .ident p n
private def call (f : String) (args : List SExpr) : SExpr := .app p (id p f) args false
private def plus (a b : SExpr) : SExpr := .bin p "+" a b
private def concat : List SExpr → SExpr
  | [] => str p ""
  | e :: es => es.foldl (plus p) e

end Build

/-- The printer of a value of type `t`: the function `$diag_t($X:t)<reads>:string`,
    and the types of the values its body prints with their own. -/
def printer (env : TyEnv) (p : Pos) (t : Ty) : Except String (STop × List Ty) := do
  let x := SExpr.ident p "$X"
  let s := str p
  let pr (u : Ty) (e : SExpr) : SExpr := call p (printerName u) [e]
  let refuse (what : String) : Except String (SExpr × List Ty) :=
    throw what
  -- (a record's parts: its text, and each field's value with its type)
  let fields (n : String) (args : List Ty) (y : SExpr) : List (SExpr × Option Ty) :=
    ((env.fields n args).filter fun (f, _, _) => !f.startsWith "$").zipIdx.flatMap fun ((f, ft, _), i) =>
      [(s ((if i == 0 then "" else ", ") ++ f ++ " := "), none), (.member p y f, some ft)]
  let record (name : String) (parts : List (SExpr × Option Ty)) : SExpr :=
    concat p ([s (name ++ "{")] ++ parts.map (fun (e, u) => match u with | some u => pr u e | none => e) ++
      [s "}"])
  let partTys (parts : List (SExpr × Option Ty)) : List Ty := parts.filterMap (·.2)
  let (body, deps) ← match t with
    | .int => pure (call p "ToString" [x], [])
    | .logic => pure (SExpr.ite p [.query p x] (s "true") (some (s "false")), [])
    | .rational => pure (call p "$diagRational" [call p "$rationalParts" [x]], [])
    | .char => pure (call p "$diagChar" [x], [])
    | .char32 => pure (call p "$diagChar32" [x], [])
    | .arr .char => pure (call p "$diagString" [x], [])
    | .void | .tup [] | .never => pure (s "false", [])
    | .any => pure (SExpr.app p (.member p (call p "$asAnything" [x]) diagnoseMethod) [] false, [])
    | .refine n => match env.refines.lookup n with
      | some (b, _) => pure (pr b x, [b])
      | none => refuse s!"the refinement type {n}"
    | .opt u =>
      pure (SExpr.ite p [.decl p "$Y" none false (.query p x)]
        (concat p [s "option{", pr u (.ident p "$Y"), s "}"]) (some (s "false")), [u])
    | .arr u => pure (call p "$diagArray" [.forE p [.gen p "$E" none x] (pr u (.ident p "$E"))], [u])
    | .tup us =>
      let parts := us.zipIdx.map fun (u, i) => pr u (.app p x [.int p i] false)
      pure (concat p ([s "("] ++ (parts.zipIdx.map fun (e, i) => if i == 0 then e else plus p (s ", ") e) ++
        [s ")"]), us)
    | .map k v =>
      pure (call p "$diagMap" [.forE p [.gen p "$V" (some "$K") x]
        (concat p [pr k (.ident p "$K"), s " => ", pr v (.ident p "$V")])], [k, v])
    | .enum n =>
      let values := (env.enums.lookup n).getD []
      let arms := values.map fun v =>
        (some (SExpr.member p (.ident p n) v), s s!"{displayName n}.{v}")
      let arms := if env.openEnums.contains n then arms ++ [(none, s s!"{displayName n}")] else arms
      pure (SExpr.caseE p x arms, [])
    | .struct n ts =>
      if let some (shape, _) := FnValues.parseWritten n then
        -- a function value: the function's name and its parameters' types
        -- at the value's type, `F(:int, :float)` (the Book's tests:
        -- `(/Verse.org/VerseTests:)GlobalFunction(:float)`, and the
        -- language's own `(/Verse.org/Verse:)ToDiagnostic(:any)`), by casts
        -- over the classes of the functions it may be (`F$fn`, `c$M$fn`)
        let params := "(" ++ ", ".intercalate ((ts.take (shape.arity - shape.named.length)).map
          (":" ++ ·.show)) ++ ")"
        let below := (env.concreteBelow n).filter fun d =>
          (d.splitOn "$fn").length > 1 && (env.sparams.lookup d).isNone && env.upArgs d [] n == ts
        let named (d : String) : String :=
          match ((d.splitOn "$fn").headD d).splitOn "$" with
          | [f] => if bookNames.contains f || BuiltinValues.signatures.any (·.1 == f) then s!"(/Verse.org/Verse:){f}"
            else displayName f
          | parts => s!"({".".intercalate (parts.dropLast.map displayName)}:){parts.getLast!}"
        let e := below.foldr (fun d e =>
          SExpr.ite p [.decl p "$Y" none false (.app p (.ident p d) [x] true)] (s (named d ++ params)) (some e))
          (s ("function" ++ params))
        pure (e, [])
      else if hiddenName n then
        if n.startsWith "$type" then refuse "a type"
        else refuse s!"a value of the compiler's type {n}"
      else if !env.classes.contains n then
        -- a struct: its fields in the order they are declared
        let parts := fields n ts x
        pure (record (displayName n) parts, partTys parts)
      else
        -- an object: of the class it is an instance of, by casts from the
        -- most derived class down; a `diagnosable` one prints its own
        -- diagnostic (the API reference: "For objects whose class
        -- implements the internal diagnosable interface it delegates to
        -- that class's own GetDiagnostic")
        let object (d : String) (args : List Ty) (y : SExpr) : SExpr × List Ty :=
          if env.isSub d "diagnosable" then
            (.member p (.app p (.member p y "GetDiagnostic") [] false) "String", [])
          else
            let parts := fields d args y
            (record (displayName d) parts, partTys parts)
        -- (those that may be one: no other instance of a parametric class
        -- or interface `n`)
        let below := (env.concreteBelow n).filter fun d =>
          d != n && !hiddenName d && (env.sparams.lookup d).isNone && env.upArgs d [] n == ts
        let below := below.toArray.qsort (fun a b => (env.supers a).length > (env.supers b).length) |>.toList
        let (last, lastDeps) :=
          if (env.concreteBelow n).contains n then object n ts x
          else (s s!"{displayName n}\{}", [])
        let (e, deps) := below.foldr (fun d (e, deps) =>
          let (o, ds) := object d [] (.ident p "$Y")
          (SExpr.ite p [.decl p "$Y" none false (.app p (.ident p d) [x] true)] o (some e), ds ++ deps))
          (last, lastDeps)
        pure (e, deps)
    | .float => refuse "a float (the shortest decimal that reads back is a Verse Core primitive not written yet)"
    | .dyn => refuse "a comparable (the type of its value is in its box, which no Verse code reads)"
    | .param n _ => refuse s!"a value of the type parameter {n}"
    | .weakMap .. => refuse "a weak_map"
  return (.fn p (printerName t) [{ name := "$X", ty := t.toSTy }] [] ["reads"] (.name "string") body, deps)

/-- The class of the values of type `t` as an `any`, and the printers it
    needs, of `t` and of the types of the values inside one: each once,
    the closure over the printers' bodies. -/
def wrapperDecls (env : TyEnv) (p : Pos) (t : Ty) : Except String (List STop) := do
  let cls : STop := .classDef p (wrapperName t) [] [] ["computes"] [.name anyInterface] false
    [{ name := "$V", ty := t.toSTy }]
    [.fn p diagnoseMethod [] [] ["override", "reads"] (.name "string") (call p (printerName t) [.ident p "$V"])]
  let mut out : Array STop := #[cls]
  let mut seen : List String := []
  let mut todo : List Ty := [t]
  -- (each type once: the printers of types that refer to each other, a
  -- class whose field holds one of its own, call each other)
  for _ in [0:4096] do
    match todo with
    | [] => break
    | u :: rest =>
      todo := rest
      if seen.contains (printerName u) then continue
      seen := printerName u :: seen
      let (fn, deps) ← match printer env p u with
        | .ok r => pure r
        | .error what => throw s!"ToDiagnostic of {what} is not supported yet: a value of type {t.show} is converted to any{if u == t then "" else s!", which holds a value of type {u.show},"} in a program that calls ToDiagnostic"
      out := out.push fn
      todo := todo ++ deps
  if !todo.isEmpty then throw s!"ToDiagnostic of a value of type {t.show}: too many types to print"
  return out.toList

end OpenVerse.Front.Diagnostic
