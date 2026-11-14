/-
  OpenVerse front end — localized messages (Book of Verse ch. 12,
  "Localization"), a desugaring before the source rules.

  A definition marked `<localizes>` is a message: a constant
  `X<localizes>:message = "text"`, a function
  `F<localizes>(Name:string, Number:int):message = "text with {Name}"`, or a
  field of a class or an interface. A `message` is its default text rendered:
  openverse has no culture, so `Localize(M)` is the text, an `int` in it is
  written with comma separators ("190,091", ch. 12), a `float` as `ToString`
  writes it, and `Join(Messages, Separator)` puts the separator between them.
  So a `message` is a `string` (`resolveTy`), and this pass writes:

  - the definition without `<localizes>`, its text a string whose
    interpolants are the parameters' rendered values, each computed once
    for every parameter (`$localizeValue`, overloaded on `int`, `float` and
    `string`: a parameter of another type has none, as the tests refuse,
    "No overload of the function `MakeLocalizableValue` matches"); an
    interpolant that names no parameter is its text, `{Name}`, and a code
    point is the character (`{0u004d}`);
  - calls of `Localize` and `Join`, which the program does not define, as
    calls of the helpers `$localize` and `$localizeJoin`.

  The rules the tests pin (`Localization.versetest`), each refused here: the
  type is written, and is `message` (3639, 3509); the value is a string
  literal (3638); an interpolant is a parameter's name or a code point
  (3652). A message inside a function (3651) is a local definition with a
  specifier, which the parser refuses already.
-/
import OpenVerse.Front.Parser

namespace OpenVerse.Front.Localization

def spec : String := "localizes"

/-- The helpers' names, and their parameters' and locals', each `$name`. -/
def names : List String :=
  ["localize", "localizeValue", "localizeGrouped", "localizeJoin", "X", "N", "Q", "R", "Ms", "Sep", "I", "M"]

def prelude : String := "
localize(X:string)<computes>:string = X
localize(X:int)<computes>:string = ToString(X)
localize(X:float)<computes>:string = ToString(X)
localizeValue(X:string)<computes>:string = X
localizeValue(X:float)<computes>:string = ToString(X)
localizeValue(X:int)<computes>:string =
    if (X < 0) then \"-\" + localizeGrouped(-X) else localizeGrouped(X)
localizeGrouped(N:int)<computes>:string =
    if (N >= 1000, Q := Quotient[N, 1000], R := Mod[N, 1000]):
        localizeGrouped(Q) + (if (R < 10) then \",00\" else if (R < 100) then \",0\" else \",\") + ToString(R)
    else ToString(N)
localizeJoin(Ms:[]string, Sep:string)<computes>:string =
    Concatenate(for (I -> M : Ms) { if (I = 0) then M else Sep + M })
"

/-- Whether a program defines a function of this name itself. -/
def defines (tops : List STop) (n : String) : Bool :=
  tops.any fun
    | .fn _ m .. => m == n || m.endsWith s!"::{n}"
    | _ => false

/-- The text of a message, its interpolants rewritten: a name in `vals` is
    that value's local, another name its text in braces, a code point
    stays. -/
def text (p : Pos) (parts : List SPart) (vals : List (String × String)) : Except String (List SPart) :=
  parts.mapM fun
    | .text s => pure (.text s)
    | .code (.ident q n) =>
      match vals.lookup n with
      | some v => pure (.code (.ident q v))
      | none => pure (.text s!"\{{n}}")
    | .code e@(.char ..) | .code e@(.char32 ..) => pure (.code e)
    | .code e => throw s!"{(if e.pos.line == 0 then p else e.pos).show}: an interpolant of a <localizes> message is a parameter's name or a code point (Book of Verse ch. 12: \"Only parameter names and Unicode code points allowed in braces\"; its tests, Localization.versetest, 3652)"

/-- A message's value, refused unless a string literal, and its type,
    refused unless `message`. -/
def checkForm (p : Pos) (n : String) (ty : Option STy) (v : Option SExpr) : Except String Unit := do
  match ty with
  | none => throw s!"{p.show}: the <localizes> definition {n} states its type, message: write {n}<localizes>:message = \"…\" (Book of Verse tests, Localization.versetest: forms without the type are not supported, 3639)"
  | some (.name "message") => pure ()
  | some t => throw s!"{p.show}: the <localizes> definition {n} is of type message, not {match t with | .name m => m | _ => "another type"} (Book of Verse ch. 12; its tests, Localization.versetest:119, 3509)"
  match v with
  | some (.str ..) | none => pure ()
  | some e => throw s!"{e.pos.show}: the value of the <localizes> definition {n} is a string literal (Book of Verse tests, Localization.versetest:105, 3638)"

/-- A function's body: the parser's projections of its destructured
    parameters, then the message's text. -/
def bodyParts : SExpr → Option (List SExpr × Pos × List SPart)
  | .str p parts => some ([], p, parts)
  | .block _ ss => match ss.getLast? with
    | some (.str p parts) =>
      let pre := ss.dropLast
      if pre.all (fun | .decl _ _ _ false _ => true | _ => false) then some (pre, p, parts) else none
    | _ => none
  | _ => none

/-- A call of `Localize` (when `lz`) or `Join` (when `jn`) as a call of its
    helper; any other expression as it is. -/
def rewriteCall (lz jn : Bool) (e : SExpr) : SExpr :=
  match e with
  | .app p (.ident q "Localize") args br => if lz then .app p (.ident q "$localize") args br else e
  | .app p (.ident q "Join") args br => if jn then .app p (.ident q "$localizeJoin") args br else e
  | e => e

partial def mentions (n : String) : SExpr → Bool
  | .ident _ m => m == n
  | e => e.children.any (mentions n)

/-- The program with its messages written out, and whether it needs the
    helpers. -/
partial def desugar (tops : List STop) : Except String (List STop × Bool) := do
  let mut used := false
  let mut out : Array STop := #[]
  let field (f : SField) : Except String SField := do
    if !f.specs.contains spec then return f
    checkForm { line := 0, col := 0 } f.name (some f.ty) f.default
    let default ← f.default.mapM fun
      | .str q parts => do return .str q (← text q parts [])
      | d => pure d
    return { f with specs := f.specs.filter (· != spec), default }
  for t in tops do
    match t with
    | .const p n specs ty v =>
      if specs.contains spec then
        checkForm p n ty (some v)
        let .str q parts := v | unreachable!
        used := true
        out := out.push (.const p n (specs.filter (· != spec)) ty (.str q (← text q parts [])))
      else out := out.push t
    | .fn p n ps tps specs ret body =>
      if specs.contains spec then
        checkForm p n (some ret) none
        let some (pre, q, parts) := bodyParts body
          | throw s!"{body.pos.show}: the value of the <localizes> definition {n} is a string literal (Book of Verse tests, Localization.versetest:105, 3638)"
        -- (every parameter's value rendered once, as the tests have it: a
        -- parameter of a type that has none is refused, used or not)
        let bound := (ps.filter (!·.name.startsWith "$")).map (·.name) ++
          pre.filterMap fun | .decl _ x _ _ _ => some x | _ => none
        let vals := bound.map fun x => (x, s!"$localized{x}")
        let renders := vals.map fun (x, v) =>
          SExpr.decl q v none false (.app q (.ident q "$localizeValue") [.ident q x] false)
        used := true
        out := out.push (.fn p n ps tps (specs.filter (· != spec)) ret
          (.block q (pre ++ renders ++ [.str q (← text q parts vals)])))
      else out := out.push t
    | .classDef p n nsp tps specs parents isI fs ms =>
      let fs' ← fs.mapM field
      if fs.any (·.specs.contains spec) then used := true
      out := out.push (.classDef p n nsp tps specs parents isI fs' ms)
  let lz := !defines tops "Localize"
  let jn := !defines tops "Join"
  let calls := fun (e : SExpr) => (lz && mentions "Localize" e) || (jn && mentions "Join" e)
  if out.any (fun t => t.code.any calls) then used := true
  -- (the calls in all of a definition's code, a struct's fields' defaults too)
  return (if used then out.toList.map (STop.mapAll id (rewriteCall lz jn)) else tops, used)

def tops : Except String (List STop) := parsePrelude prelude names

end OpenVerse.Front.Localization
