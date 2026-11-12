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
  let arrays2 := Ty.arr (.arr .int)
  let event := Ty.struct "event" [.int]
  need "actual event proofs expose intrinsic Await"
    (viewIs (some event) ((context [proof "Event" event t]).concurrencyView p t "Await"))
  for locals in [[], [proof "Event" event t true]] do
    let ctx := { context locals with types := { types with boundFacts := [(event, t)] } }
    need "intrinsic concurrency views refuse static facts and dummy proofs"
      (viewIs none (ctx.concurrencyView p t "Await"))
  let worker := Ty.struct "worker" []
  let method : Sig := {
    idx := 0, name := "worker.Await", params := [worker], ret := .int, decides := false, isConst := false }
  let ordinary (related : Bool) (locals : List Local) : Ctx := {
    context locals with
    sigs := [method]
    types := { types with
      classes := types.classes ++ ["worker", "event"]
      structs := types.structs ++ [("worker", []), ("event", [])]
      cinfo := types.cinfo ++ [("worker", { parent := if related then some "event" else none }), ("event", {})]
      sparams := [("event", [("element", false)])]
      pargs := [("worker", [.int])] } }
  for locals in [[proof "Worker" worker t, proof "Event" event t],
      [proof "Event" event t, proof "Worker" worker t]] do
    need "a more-specific ordinary method precedes a redundant intrinsic view"
      (viewIs (some worker) ((ordinary true locals).concurrencyView p t "Await"))
    need "unrelated ordinary and intrinsic views remain ambiguous"
      (match (ordinary false locals).concurrencyView p t "Await" with | .error _ => true | _ => false)
  for locals in [[proof "Event" event t, proof "Task" (.struct "task" [.int]) t],
      [proof "Task" (.struct "task" [.int]) t, proof "Event" event t]] do
    need "unrelated intrinsic concurrency views remain ambiguous in either order"
      (match (context locals).concurrencyView p t "Await" with | .error _ => true | _ => false)
  need "payload signals do not acquire a zero-argument intrinsic"
    (viewIs none ((context [proof "Event" event t]).concurrencyView p t "Signal"))
  need "opaque nested arrays provide a flattening view"
    (viewIs (some arrays2) ((context [proof "D" arrays2 t]).arrayView p t 2 "Concatenate"))
  for locals in [[], [proof "D" arrays2 t true]] do
    need "flattening cannot use static facts or dummy dictionaries"
      (viewIs none ((context locals).arrayView p t 2 "Concatenate"))
  need "component proofs establish a nested array shape"
    (viewIs (some arrays2) ((context [proof "D" (.arr .int) a]).arrayView p (.arr a) 2 "Concatenate"))
  let composed := context [proof "Whole" (.arr a) t, proof "Element" (.arr .int) a]
  need "whole and component proofs compose for flattening"
    (viewIs (some arrays2) (composed.arrayView p t 2 "Concatenate"))
  let wholeOnly := context [proof "Whole" arrays2 (.arr a)]
  need "a whole proof can expose the complete nested array"
    (viewIs (some arrays2) (wholeOnly.arrayView p (.arr a) 2 "Concatenate"))
  need "a whole flattening view does not create an element proof"
    ((find? wholeOnly.types wholeOnly.evidenceTypes ⟨.arr .int, a⟩).isNone)
  for locals in [[proof "Flat" (.arr .int) t, proof "Nested" arrays2 t],
      [proof "Nested" arrays2 t, proof "Flat" (.arr .int) t]] do
    need "inapplicable shallow views do not make flattening ambiguous"
      (viewIs (some arrays2) ((context locals).arrayView p t 2 "Concatenate"))
  for locals in [[proof "Ints" arrays2 t, proof "Floats" (.arr (.arr .float)) t],
      [proof "Floats" (.arr (.arr .float)) t, proof "Ints" arrays2 t]] do
    need "unrelated nested array views remain ambiguous"
      (match (context locals).arrayView p t 2 "Concatenate" with | .error _ => true | _ => false)
  need "ordinary shallow arrays cannot be flattened without evidence"
    (viewIs none ((context []).arrayView p (.arr .int) 2 "Concatenate"))
  let u := Ty.param "u" false
  let v := Ty.param "v" false
  let paths := [proof "U" (.arr u) t, proof "V" (.arr v) t,
    proof "Marked" (.arr marked) u, proof "Plain" (.arr a) v]
  for locals in [paths, paths.reverse] do
    match (context locals).arrayView p t 2 "Concatenate" with
    | .ok (some (.arr (.arr (.param "a" comparable)))) =>
      need "converging array views intersect comparable guarantees" (!comparable)
    | _ => throw (IO.userError "lost the composed array view")
  IO.println "container view contracts passed (real evidence, specificity, equivalence, ambiguity and whole relations)"
