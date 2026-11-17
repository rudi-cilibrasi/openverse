import OpenVerse.Front.MetadataReceivers
import OpenVerse.Core.Bounded
import OpenVerse.Core.Check
import OpenVerse.Core.Control

open OpenVerse OpenVerse.Front MetadataReceivers

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def env : TyEnv := Id.run do
  let classes := ["$varcell", "Inner", "Outer", "Holder", "Reader", "Node", "BadNode", "Grow"]
  return {
    classes
    classIx := classes.zipIdx.foldl (fun map (name, index) => map.insert name index) {}
    belowReady := true
    belowMap := classes.foldl (fun map name => map.insert name [name]) {}
    supersMap := classes.foldl (fun map name => map.insert name [name]) {}
    structs := [
      ("$varcell", [("VCell", .param "t" false, none)]),
      ("Inner", [("Work", .int, none)]),
      ("Outer", [("Box", .struct "Inner" [], none)]),
      ("Holder", [("Value", .param "t" false, none)]),
      ("Reader", [("N", .int, none)]),
      ("Node", [("Next", .struct "Node" [], none), ("N", .int, none)]),
      ("BadNode", [("Next", .struct "BadNode" [], none), ("Cell", .struct "$varcell" [.int], none)]),
      ("Grow", [("Next", .struct "Grow" [.arr (.param "t" false)], none)])]
    sparams := [("$varcell", [("t", false)]), ("Holder", [("t", false)]), ("Grow", [("t", false)])] }

private def field (object : Expr) : Expr := .heap (.get 0) [object]
private def string (s : String) : Expr :=
  .lit (.arr (s.toList.map fun c => Value.char c.toNat).toArray)

private def run (slots : Nat) (body : Expr) : IO (Int × String) := do
  let p : Prog := { fns := [{ name := "Main", arity := 0, nslots := slots, decides := false, body }], main := 0 }
  expect (p.check && p.checkControl) "projected frame must retain Core scope/control/write certificates"
  match p.runB 1000000 10000 with
  | .res (.ok (.int result), output) => return (result, String.ofList (output.map Char.ofNat))
  | _ => throw <| IO.userError "expected complete integer result"

private def setup (tail : Expr) : Expr :=
  .seq (.assign 0 (.heap (.new 1) [.lit (.int 7)]))
    (.seq (.assign 1 (.heap (.new 2) [.local 0])) tail)

private def equivalent (tail : Expr) (expected : Int × String) : IO Unit := do
  let body := setup tail
  let projection := project env #[.struct "Inner" [], .struct "Outer" []] body
  let before ← run 2 body
  let after ← run (2 + projection.extraSlots.size) projection.body
  expect (before == expected && after == expected) "receiver projection changed values, order or rollback"
  expect (projection.extraSlots.size > 0 && projection.nonCellSlots == (List.range projection.extraSlots.size).map (2 + ·)) "expected a typed virtual receiver"

private def models : IO Unit := do
  let read := project env #[.struct "Outer" []] (field (field (.local 0)))
  expect (read.extraSlots == #[.struct "Inner" []] && read.nonCellSlots == [1])
    "H.Box receiver needs its resolved nominal certificate"
  let readWithReach := withReachability env #[.struct "Outer" []] read
  expect (read.noCellReachSlots.isEmpty && readWithReach.noCellReachSlots == [0,1]) "closed ordinary fields cannot reach a private cell"
  let direct := project env #[.struct "Inner" []] (field (.local 0))
  expect direct.extraSlots.isEmpty "direct locals already have source type certificates"
  for ty in [Ty.any, .dyn, .param "t" false] do
    let unknown := project env #[ty] (field (field (.local 0)))
    expect unknown.extraSlots.isEmpty "opaque receivers must not be certified"
  let privateReceiver := project env #[.tup [.struct "$varcell" [.int]]]
    (field (.prim (.tupGet 0) [.local 0]))
  expect privateReceiver.extraSlots.isEmpty "private cell receivers must keep payload checks"
  for (ty, receiver) in [
      (Ty.tup [.struct "Inner" []], Expr.prim (.tupGet 0) [.local 0]),
      (.arr (.struct "Inner" []), .prim .index [.local 0, .lit (.int 0)]),
      (.opt (.struct "Inner" []), .prim .query [.local 0]),
      (.struct "Holder" [.struct "Inner" []], field (.local 0))] do
    expect ((project env #[ty] (field receiver)).extraSlots == #[.struct "Inner" []])
      "tuple, array, option and instantiated field receivers retain their type"

  let mixed : TyEnv := { env with
    classes := env.classes ++ ["Iface", "A", "B"]
    classIx := {}, belowReady := false, belowMap := {}, supersMap := {}
    cinfo := [("Iface", { isIface := true }), ("A", { ifaces := ["Iface"] }), ("B", { ifaces := ["Iface"] })]
    structs := env.structs ++ [("Iface", [("Box", .struct "Inner" [], none)]),
      ("A", [("Box", .struct "Inner" [], none)]),
      ("B", [("Extra", .struct "$varcell" [.int], none), ("Box", .struct "Inner" [], none)])] }
  expect ((project mixed #[.struct "Iface" []] (field (field (.local 0)))).extraSlots.isEmpty)
    "incompatible physical interface positions must not create certificates"
  expect (noCellReach env (.struct "Reader" []) && noCellReach env (.struct "Node" []))
    "closed scalar readers and recursive data cycles contain no private cells"
  expect (!noCellReach env (.struct "BadNode" []) && !noCellReach env (.struct "Grow" [.int]))
    "private fields and growing instantiations remain possible private carriers"
  for ty in [Ty.any, .dyn, .param "t" false, .arr (.struct "$varcell" [.int]),
      .opt (.struct "$varcell" [.int]), .tup [.int, .struct "$varcell" [.int]]] do
    expect (!noCellReach env ty) "opaque or nested private carriers must retain references"

  equivalent (field (field (.local 1))) (7, "")
  let receiver := .seq (.print (string "receiver")) (field (.local 1))
  let rhs := .seq (.print (string "rhs")) (.lit (.int 9))
  equivalent (.seq (.heap (.set 0) [receiver, rhs]) (field (field (.local 1)))) (9, "receiver\nrhs\n")
  let failed := .seq (.print (string "rolled back"))
    (.seq (.prim .fail []) (field (.local 1)))
  equivalent (.ite (field failed) (.lit (.int 0)) (field (field (.local 1)))) (7, "")
  let rhs := .seq (.assign 0 (.heap (.new 1) [.lit (.int 99)])) (.lit (.int 9))
  equivalent (.seq (.heap (.set 0) [field (.local 1), rhs]) (field (field (.local 1)))) (9, "")
  IO.println "PASS typed metadata receivers, field layouts, reachability, evaluation order and rollback"

private def scale : IO Unit := do
  let count := 32000
  let names := (List.range count).map fun i => s!"Class{i}"
  let classes := env.classes ++ names
  let prepared : TyEnv := { env with
    classes
    classIx := classes.zipIdx.foldl (fun map (name, index) => map.insert name index) {} }
  -- An IO boundary prevents Lean's pure-let specialization from rebuilding
  -- this synthetic 32k class table inside every measured loop iteration.
  let preparedRef ← IO.mkRef prepared
  let large ← preparedRef.get
  let body := field (field (.local 0))
  let started ← IO.monoMsNow
  for _ in [:count] do
    expect ((project large #[.struct "Outer" []] body).extraSlots.size == 1) "large class table projection failed"
  let absentPrepared : TyEnv := { large with
    classes := names
    classIx := names.zipIdx.foldl (fun map (name, index) => map.insert name index) {} }
  let absentRef ← IO.mkRef absentPrepared
  let absent ← absentRef.get
  for _ in [:count] do
    expect ((project absent #[.struct "Outer" []] body).extraSlots.isEmpty) "no-private fast path must not project"
  IO.println s!"PASS {count} typed projections and no-private fast paths in a large class table ({(← IO.monoMsNow) - started}ms)"

def main (args : List String) : IO Unit :=
  if args.contains "--scale" then scale else models
