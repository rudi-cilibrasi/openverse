import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def p : Pos := { line := 1, col := 1 }
private def t : Ty := .param "t" false
private def pureShape := (FnValues.shapeOf 1 ["computes"]).name
private def readsShape := (FnValues.shapeOf 1 ["reads"]).name
private def pureFn : Ty := .struct pureShape [.int, .int]
private def readsFn : Ty := .struct readsShape [.int, .int]
private def types : TyEnv := {
  classes := [pureShape, readsShape]
  structs := [(pureShape, []), (readsShape, [])]
  cinfo := [(pureShape, { parent := some readsShape }), (readsShape, {})]
  sparams := [pureShape, readsShape].map (·, [("input", false), ("result", false)])
  pargs := [(pureShape, [.param "input" false, .param "result" false])]
  tvars := [("t", t)] }

private def proof (name : String) (upper : Ty) (dummy : Bool := false) : Local := {
  name, slot := 9, ty := (Bound.mk upper t).ty, mutable := false, typeValue := dummy }

private def context (locals : List Local) : Ctx := {
  sigs := [], sigProg := { fns := [], main := 0 }
  types := { types with boundFacts := [(pureFn, t), (readsFn, t)] }, locals }

private def viewIs (expected : Option Ty) : Except String (Option Ty) → Bool
  | .ok actual => actual == expected
  | .error _ => false

def main : IO Unit := do
  need "concrete function values keep their own shape"
    (viewIs (some pureFn) ((context []).callableView p pureFn))
  need "an actual dictionary exposes a callable upper"
    (viewIs (some pureFn) ((context [proof "D" pureFn]).callableView p t))
  need "dummy dictionaries do not expose callable uppers"
    (viewIs none ((context [proof "D" pureFn true]).callableView p t))
  need "static facts do not expose callable uppers"
    (viewIs none ((context []).callableView p t))
  for locals in [[proof "Pure" pureFn, proof "Reads" readsFn],
      [proof "Reads" readsFn, proof "Pure" pureFn]] do
    need "effect-subtype preference is independent of dictionary order"
      (viewIs (some pureFn) ((context locals).callableView p t))
  let other := Ty.struct pureShape [.string, .int]
  for locals in [[proof "Ints" pureFn, proof "Strings" other],
      [proof "Strings" other, proof "Ints" pureFn]] do
    match (context locals).callableView p t with
    | .error message =>
      need "unrelated callable views diagnose ambiguity"
        ((message.splitOn "ambiguous callable bound").length > 1)
    | .ok _ => throw (IO.userError "unrelated callable views were selected")
  IO.println "callable bound contracts passed (actual evidence, effects, ambiguity and order)"
