import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

/- Generated accessors must carry a hidden field's declared metadata role.
   Use prepareLowering's actual getters, with checked Core callers, rather
   than a source member wrapper that independently marks hidden reads. -/
private def checkGetter (hidden dummy : Bool) (mode : Nat) (other : Bool) : IO Unit := do
  let field := if hidden then "$w.proof" else "Proof"
  let reader : Ty := .struct "reader" []
  let env : TyEnv := {
    classes := ["box", "reader"]
    structs := [("box", [(field, reader, none), ("Real", reader, none)]), ("reader", [])]
    cinfo := [("box", {}), ("reader", {})]
    fieldAcc := [("box", field), ("box", "Real")] }
  let signatures : Signatures := {
    tops := [], generics := [], sigs := #[], gsigs := #[]
    prog := { fns := [], main := 0 } }
  let lowered := prepareLowering env signatures #[]
  let read := Expr.call (if other then 2 else 0) [.heap (.new 0) [.local 0, .local 1]]
  let caller : Fn := {
    name := "Caller", arity := 2, nslots := 2, decides := false, writes := true
    body := if mode == 0 then .call 5 [read] else read }
  let run : Fn := {
    name := "reader.Run", arity := 1, nslots := 1
    decides := false, writes := false, body := .lit (.int 7) }
  let wrapper : Fn := {
    name := "Wrapper", arity := 2, nslots := 2, decides := false, writes := true
    body := if mode == 2 then .call 5 [.call 4 [.local 0, .local 1]] else .lit (.int 0) }
  let main : Fn := {
    name := "Main", arity := 0, nslots := 0
    decides := false, writes := false, body := .lit .void }
  let fns := lowered.fns ++ #[caller, run, wrapper, main]
  let prog : Prog := { fns := fns.toList, main := 7 }
  let rty : VTy := .ref [1] []
  let ret := if mode == 0 then VTy.int else rty
  let sigs := { lowered.sigs with fns := lowered.sigs.fns ++
    [([rty, rty], ret), ([rty], .int), ([rty, rty], .int), ([], .void)] }
  let slots := lowered.slotTys ++ #[[rty, rty], [rty], [rty, rty], []]
  let label := s!"generated getter hidden={hidden}, dummy={dummy}, mode={mode}, other={other}"
  unless prog.check && prog.checkControl && prog.checkTypes sigs slots.toList do
    throw (IO.userError s!"{label}: Core checks")
  let input : MetadataFlow.Info := { inputs := if dummy then [0] else [] }
  let infos := lowered.metadata ++ #[input, { required := [0] }, {}, {}]
  let shouldReject := mode != 1 && (if other then dummy && !hidden else hidden || dummy)
  match MetadataFlow.check fns infos (metadataFields env) with
  | .ok _ =>
    if shouldReject then throw (IO.userError s!"{label}: metadata became a receiver")
  | .error message =>
    if !shouldReject || (message.splitOn "dummy type value cannot").length ≤ 1 then
      throw (IO.userError s!"{label}: {message}")

def main : IO Unit := do
  for hidden in [false, true] do
    for dummy in [false, true] do
      -- Execute the read value, forward it opaquely, or execute the
      -- forwarded value in another function.
      for mode in [0, 1, 2] do checkGetter hidden dummy mode false
  -- A hidden witness must not taint an unrelated ordinary field.
  for dummy in [false, true] do checkGetter true dummy 0 true
  IO.println "generated metadata getter contracts passed (14 checked controls)"
