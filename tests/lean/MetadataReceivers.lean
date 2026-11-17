import OpenVerse.Front.MetadataReceivers
import OpenVerse.Core.Bounded
import OpenVerse.Core.Check
import OpenVerse.Core.Control

open OpenVerse OpenVerse.Front MetadataReceivers

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def env : TyEnv := Id.run do
  let classes := ["$varcell", "Inner", "Outer", "Holder"]
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
      ("Holder", [("Value", .param "t" false, none)])]
    sparams := [("$varcell", [("t", false)]), ("Holder", [("t", false)])] }

private def field (object : Expr) : Expr := .heap (.get 0) [object]
private def string (s : String) : Expr :=
  .lit (.arr (s.toList.map fun c => Value.char c.toNat).toArray)

private def run (slots : Nat) (body : Expr) (helpers : List Fn := []) : IO (Int × String) := do
  let p : Prog := { fns := [{ name := "Main", arity := 0, nslots := slots, decides := false, body }] ++ helpers, main := 0 }
  expect (p.check && p.checkControl) "projected frame must retain Core scope/control/write certificates"
  match p.runB 1000000 10000 with
  | .res (.ok (.int result), output) => return (result, String.ofList (output.map Char.ofNat))
  | _ => throw <| IO.userError "expected complete integer result"

private def setup (tail : Expr) : Expr :=
  .seq (.assign 0 (.heap (.new 1) [.lit (.int 7)]))
    (.seq (.assign 1 (.heap (.new 2) [.local 0])) tail)

private def equivalent (tail : Expr) (expected : Int × String)
    (fnReturns : Array (Option CallType) := #[]) (helpers : List Fn := []) : IO Unit := do
  let body := setup tail
  let projection := project env #[.struct "Inner" [], .struct "Outer" []] body fnReturns
  let before ← run 2 body helpers
  let after ← run (2 + projection.extraSlots.size) projection.body helpers
  expect (before == expected && after == expected) "receiver projection changed values, order or rollback"
  expect (projection.extraSlots.size > 0 && projection.nonCellSlots == (List.range projection.extraSlots.size).map (2 + ·)) "expected a typed virtual receiver"

private def models : IO Unit := do
  let read := project env #[.struct "Outer" []] (field (field (.local 0)))
  expect (read.extraSlots == #[.struct "Inner" []] && read.nonCellSlots == [1])
    "H.Box receiver needs its resolved nominal certificate"
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

  let callReceiver := field (.call 1 [.local 0])
  expect ((project env #[.struct "Outer" []] callReceiver
    #[none, some { ret := .struct "Inner" [] }]).extraSlots == #[.struct "Inner" []])
    "a resolved nominal call result retains its receiver type"
  for returns in [#[], #[none, none]] do
    expect ((project env #[.struct "Outer" []] callReceiver returns).extraSlots.isEmpty)
      "unknown call targets must not acquire return certificates"
  for ty in [Ty.any, .dyn, .param "t" false,
      .struct "Holder" [.param "t" false], .struct "$varcell" [.int]] do
    expect ((project env #[.struct "Outer" []] callReceiver #[none, some { ret := ty }]).extraSlots.isEmpty)
      "opaque, nested generic and private call returns must retain payload checks"
  let identity : CallType := {
    params := [.param "t" false], ret := .param "t" false, witnesses := [("t", 1)] }
  let genericReceiver := field (.call 1 [field (.local 0), .local 1])
  expect ((project env #[.struct "Outer" [], .struct "Inner" []] genericReceiver
    #[none, some identity]).extraSlots == #[.struct "Inner" []])
    "generic call results use the actual hidden witness's resolved type"
  expect ((project env #[.struct "Outer" [], .param "t" false] genericReceiver
    #[none, some identity]).extraSlots.isEmpty)
    "an opaque caller parameter with the same name cannot solve the callee's binder"
  expect ((project env #[.struct "Outer" [], .dyn] genericReceiver
    #[none, some identity]).extraSlots.isEmpty)
    "a wider selected witness must override a narrower explicit argument type"
  expect ((project env #[.struct "Outer" [], .struct "Inner" []] genericReceiver
    #[none, some { identity with witnesses := [("t", 2)] }]).extraSlots.isEmpty)
    "a missing actual witness must not create a certificate"
  expect ((project env #[.struct "Outer" [], .struct "Inner" []] genericReceiver
    #[none, some { identity with ret := .param "other" false }]).extraSlots.isEmpty)
    "an unsolved generic return parameter must not create a certificate"
  expect ((project env #[.struct "Outer" [], .struct "Inner" []] genericReceiver
    #[none, some { identity with witnesses := [("t", 1),("t", 0)] }]).extraSlots.isEmpty)
    "duplicate witness binders must not create a certificate"
  expect ((project env #[.struct "Outer" [], .struct "$varcell" [.int]] genericReceiver
    #[none, some identity]).extraSlots.isEmpty)
    "an instantiated private-cell return keeps its payload checks"
  expect ((project env #[.struct "Outer" [], .struct "Inner" []]
    (field (.prim .index [.call 1 [.prim .mkArr [field (.local 0)],
      .prim .mkArr [.local 1]], .lit (.int 0)]))
    #[none, some identity]).extraSlots == #[.struct "Inner" []])
    "the actual witness retains instantiated container element types"
  let callReturns := #[none, some ({ ret := Ty.struct "Inner" [] } : CallType)]
  let helper : Fn := {
    name := "MakeBox", arity := 1, nslots := 1, decides := false
    body := .seq (.print (string "call")) (field (.local 0)) }
  equivalent (field (.call 1 [.local 1])) (7, "call\n") callReturns [helper]
  equivalent (.seq (.heap (.set 0) [.call 1 [.local 1],
    .seq (.print (string "rhs")) (.lit (.int 9))]) (field (field (.local 1))))
    (9, "call\nrhs\n") callReturns [helper]
  equivalent (.ite (.seq (.call 1 [.local 1]) (.prim .fail []))
    (.lit (.int 0)) (field (.call 1 [.local 1]))) (7, "call\n") callReturns [helper]

  let mixed : TyEnv := { env with
    classes := env.classes ++ ["Iface", "A", "B"]
    classIx := {}, belowReady := false, belowMap := {}, supersMap := {}
    cinfo := [("Iface", { isIface := true }), ("A", { ifaces := ["Iface"] }), ("B", { ifaces := ["Iface"] })]
    structs := env.structs ++ [("Iface", [("Box", .struct "Inner" [], none)]),
      ("A", [("Box", .struct "Inner" [], none)]),
      ("B", [("Extra", .struct "$varcell" [.int], none), ("Box", .struct "Inner" [], none)])] }
  expect ((project mixed #[.struct "Iface" []] (field (field (.local 0)))).extraSlots.isEmpty)
    "incompatible physical interface positions must not create certificates"
  equivalent (field (field (.local 1))) (7, "")
  let receiver := .seq (.print (string "receiver")) (field (.local 1))
  let rhs := .seq (.print (string "rhs")) (.lit (.int 9))
  equivalent (.seq (.heap (.set 0) [receiver, rhs]) (field (field (.local 1)))) (9, "receiver\nrhs\n")
  let failed := .seq (.print (string "rolled back"))
    (.seq (.prim .fail []) (field (.local 1)))
  equivalent (.ite (field failed) (.lit (.int 0)) (field (field (.local 1)))) (7, "")
  let rhs := .seq (.assign 0 (.heap (.new 1) [.lit (.int 99)])) (.lit (.int 9))
  equivalent (.seq (.heap (.set 0) [field (.local 1), rhs]) (field (field (.local 1)))) (9, "")
  IO.println "PASS typed metadata receivers, field layouts, evaluation order and rollback"

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
  let returns := (Array.replicate count (none : Option CallType)).set! (count - 1)
    (some { ret := .struct "Inner" [] })
  let returnsRef ← IO.mkRef returns
  let indexedReturns ← returnsRef.get
  let callBody := field (.call (count - 1) [.local 0])
  for _ in [:count] do
    expect ((project large #[.struct "Outer" []] callBody indexedReturns).extraSlots.size == 1)
      "large function table must use indexed call return certificates"
  let genericReturns := indexedReturns.set! (count - 1)
    (some { params := [.param "t" false], ret := .param "t" false, witnesses := [("t", 1)] })
  let genericRef ← IO.mkRef genericReturns
  let generics ← genericRef.get
  let genericBody := field (.call (count - 1) [field (.local 0), .local 1])
  for _ in [:count] do
    expect ((project large #[.struct "Outer" [], .struct "Inner" []] genericBody generics).extraSlots.size == 1)
      "large indexed tables must support closed actual witness instantiation"
  let absentPrepared : TyEnv := { large with
    classes := names
    classIx := names.zipIdx.foldl (fun map (name, index) => map.insert name index) {} }
  let absentRef ← IO.mkRef absentPrepared
  let absent ← absentRef.get
  for _ in [:count] do
    expect ((project absent #[.struct "Outer" []] body).extraSlots.isEmpty) "no-private fast path must not project"
  IO.println s!"PASS {count} typed projections, indexed call returns and no-private fast paths in large tables ({(← IO.monoMsNow) - started}ms)"

def main (args : List String) : IO Unit :=
  if args.contains "--scale" then scale else models
