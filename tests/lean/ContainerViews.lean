import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def p : Pos := { line := 1, col := 1 }
private def t : Ty := .param "t" false
private def a : Ty := .param "a" false
private def vehicle : Ty := .struct "vehicle" []
private def car : Ty := .struct "car" []
private def types : TyEnv := {
  classes := ["vehicle", "car"]
  structs := [("vehicle", []), ("car", [])]
  cinfo := [("vehicle", {}), ("car", { parent := some "vehicle" })]
  tvars := [("t", t), ("a", a)] }

private def proof (name : String) (upper lower : Ty) (dummy : Bool := false) : Local := {
  name, slot := 5, ty := (Bound.mk upper lower).ty, mutable := false, typeValue := dummy }

private def context (locals : List Local) : Ctx := {
  sigs := [], sigProg := { fns := [], main := 0 }
  types := { types with boundFacts := [(.arr vehicle, t)] }, locals }

private def arrays : Ty → Bool
  | .arr _ => true
  | _ => false

private def viewIs (expected : Option Ty) : Except String (Option Ty) → Bool
  | .ok actual => actual == expected
  | .error _ => false

def main : IO Unit := do
  need "whole-array capability exposes an operational view"
    (viewIs (some (.arr vehicle)) ((context [proof "D" (.arr vehicle) t]).containerView p t arrays "index"))
  for locals in [[], [proof "D" (.arr vehicle) t true]] do
    need "facts or dummy dictionaries cannot create an operational view"
      (viewIs none ((context locals).containerView p t arrays "index"))
  for locals in [[proof "Base" (.arr vehicle) t, proof "Precise" (.arr car) t],
      [proof "Precise" (.arr car) t, proof "Base" (.arr vehicle) t]] do
    need "most-specific array selection is independent of dictionary order"
      (viewIs (some (.arr car)) ((context locals).containerView p t arrays "index"))
  let erased := [proof "Any" (.arr .any) t, proof "Void" (.arr .void) t]
  let first := (context erased).containerView p t arrays "index"
  need "equivalent uppers retain an operational view" (match first with | .ok (some _) => true | _ => false)
  match first, (context erased.reverse).containerView p t arrays "index" with
  | .ok first, .ok second => need "equivalent uppers have a stable representative" (first == second)
  | _, _ => throw (IO.userError "equivalent array uppers became ambiguous")
  let indices : Ty → Bool := fun | .arr _ | .map .. => true | _ => false
  for locals in [[proof "Array" (.arr .int) t, proof "Map" (.map .int .int) t],
      [proof "Map" (.map .int .int) t, proof "Array" (.arr .int) t]] do
    match (context locals).containerView p t indices "index" with
    | .error message =>
      need "unrelated container views diagnose ambiguity"
        ((message.splitOn "ambiguous bound index").length > 1)
    | .ok _ => throw (IO.userError "unrelated indexed views were selected")
  let whole := context [proof "Whole" (.arr vehicle) (.arr a)]
  need "a whole-container relation cannot become an element relation"
    ((SubtypeEvidence.find? whole.types whole.evidenceTypes ⟨vehicle, a⟩).isNone)
  let marked := Ty.param "a" true
  for locals in [[proof "Marked" (.arr marked) t, proof "Plain" (.arr a) t],
      [proof "Plain" (.arr a) t, proof "Marked" (.arr marked) t]] do
    match (context locals).containerView p t arrays "index" with
    | .ok (some (.arr (.param "a" comparable))) =>
      need "duplicate identities intersect comparable flags" (!comparable)
    | _ => throw (IO.userError "lost the equal array view")
  IO.println "container view contracts passed (real evidence, specificity, equivalence, ambiguity and whole relations)"
