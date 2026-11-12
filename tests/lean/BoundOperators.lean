import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def p : Pos := { line := 1, col := 1 }
private def a : Ty := .param "a" false
private def b : Ty := .param "b" false
private def t : Ty := .param "t" false
private def vehicle : Ty := .struct "vehicle" []
private def car : Ty := .struct "car" []
private def types : TyEnv := {
  classes := ["vehicle", "car", "left", "right"]
  structs := [("vehicle", []), ("car", []), ("left", []), ("right", [])]
  cinfo := [("vehicle", {}), ("car", { parent := some "vehicle" }),
    ("left", { isIface := true }), ("right", { isIface := true })]
  tvars := [("a", a), ("b", b), ("t", t)]
  boundFacts := [(vehicle, a), (vehicle, b), (.int, t)] }

private def proof (name : String) (upper lower : Ty) (dummy : Bool := false) : Local := {
  name, slot := 0, ty := (Bound.mk upper lower).ty, mutable := false, typeValue := dummy }
private def context (locals : List Local) : Ctx := {
  sigs := [], sigProg := { fns := [], main := 0 }, types, locals }

private def joins (ctx : Ctx) (inputs : List Ty) (expected : Option Ty := none) : Option Ty :=
  joinView? ctx.types ctx.evidenceTypes inputs expected

def main : IO Unit := do
  let actual := [proof "A" vehicle a, proof "B" vehicle b]
  for locals in [actual, actual.reverse] do
    let ctx := context locals
    need "element proofs infer the common array view in either order"
      (joins ctx [.arr a, .arr b] == some (.arr vehicle))
    need "an explicit compatible result is supported"
      (joins ctx [.arr a, .arr b] (some (.arr vehicle)) == some (.arr vehicle))
    need "an expected result does not invent reverse narrowing"
      (joins ctx [.arr a, .arr b] (some (.arr car)) == some (.arr vehicle))
  for ctx in [context [], context (actual.map fun l => { l with typeValue := true })] do
    need "static facts and dummy proofs do not authorize an operational join"
      ((joins ctx [.arr a, .arr b] (some (.arr vehicle))).isNone)
  let whole := context [proof "A" (.arr vehicle) (.arr a), proof "B" (.arr vehicle) (.arr b)]
  need "whole-array proofs can join their whole values"
    (joins whole [.arr a, .arr b] == some (.arr vehicle))
  need "whole-array proofs do not establish a component join"
    ((joins whole [a, b] (some vehicle)).isNone)
  let left := Ty.struct "left" []
  let right := Ty.struct "right" []
  let ambiguous := [proof "AL" left a, proof "AR" right a, proof "BL" left b, proof "BR" right b]
  for locals in [ambiguous, ambiguous.reverse] do
    let ctx := context locals
    need "unrelated common interfaces remain ambiguous"
      ((joins ctx [.arr a, .arr b]).isNone)
    need "an explicit common interface resolves the result domain"
      (joins ctx [.arr a, .arr b] (some (.arr left)) == some (.arr left))
  let numeric (ctx : Ctx) := ctx.valueView p t (arithmeticType ctx.types) "arithmetic"
  for ctx in [context [], context [proof "D" .int t true]] do
    need "numeric operations need real proof inputs"
      (match numeric ctx with | .ok value => value.isNone | _ => false)
  for locals in [[proof "I" .int t, proof "R" .rational t],
      [proof "R" .rational t, proof "I" .int t]] do
    need "a numeric view keeps the most specific available domain"
      (match numeric (context locals) with | .ok value => value == some .int | _ => false)
  for locals in [[proof "I" .int t, proof "F" .float t],
      [proof "F" .float t, proof "I" .int t]] do
    need "unrelated numeric domains are ambiguous in either order"
      (match numeric (context locals) with | .error _ => true | _ => false)
  IO.println "bound operator contracts passed (actual joins, ambiguity, whole relations and numeric domains)"
