/- Incoming identity, may-alias and closed-transfer policy regressions.
   Every program asserts all four Core validators before classifying roles.
   These are compiler API models, not a claim that Source exposes its cells. -/
import OpenVerse.Front.MetadataFlow
import OpenVerse.Front.MetadataValues
import OpenVerse.Core.Check
import OpenVerse.Core.Control
import OpenVerse.Core.TypeCheck
import OpenVerse.Core.Bounded

open OpenVerse OpenVerse.Front
namespace MetadataIncomingCells


namespace UnrelatedCellUnknownFormal
/- Extension of the grounded MixedRootCertificate model.
   A dead unrelated real private cell must not sanitize an unknown incoming
   private-cell payload. deadMetadata=true instead copies the unknown payload
   into that unrelated cell before the observer, providing a tainted companion.
   These are policy classifications, not a new Source escape claim.

   Compiler-policy boundary model, with valid Core programs. Tag0 represents
   the generic compiler cell and tag1 an opaque executable carrier. Execute
   and Reader are internal bridges, so only the two named root functions are
   independent entries. No forged objectFree certificate is supplied for a
   reference formal. The sequential Reader variant avoids the getter fast path.
   MetadataFlow validates every independent root, even if Main selects only
   ClosedRoot in this concrete program. No Source/runtime claim is made. -/
private def callable : VTy := .ref [1] []
private def cell : VTy := .ref [0] [callable]
private def realCell : Expr := .heap (.new 0) [.heap (.new 1) []]
private def readAndExecute (value : Expr) : Expr := .call 0 [.call 1 [value]]

private def program (reverse indirect : Bool) (mode : String) (deadMetadata : Bool) : Array Fn × Sigs × List (List VTy) × Array MetadataFlow.Info × Nat := Id.run do
  let readerBody := Expr.heap (.get 0) [.local 0]
  let readerBody := if indirect then Expr.seq (.lit .void) readerBody else readerBody
  let sink : Fn := { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void }
  let reader : Fn := { name := "$sourceLoopReturnReader", arity := 1, nslots := 1, decides := false, body := readerBody }
  let closed : Fn := { name := "ClosedRoot", arity := 0, nslots := 0, decides := false, body := readAndExecute realCell }
  let openReal := mode == "all-real-open"
  let opened : Fn := {
    name := "OpenRoot", arity := (if openReal then 0 else 1),
    nslots := (if openReal then 0 else 1), decides := false, writes := true,
    body := .seq
      (if deadMetadata && !openReal then .heap (.new 0) [.heap (.get 0) [.local 0]] else realCell)
      (readAndExecute (if openReal || mode == "known-real-open" then realCell else .local 0)) }
  let fns := #[sink,reader] ++ (if reverse then #[opened,closed] else #[closed,opened])
  let closedIndex := if reverse then 3 else 2
  let openedIndex := if reverse then 2 else 3
  let rootTypes := if reverse then [if openReal then [] else [cell], []] else [[], if openReal then [] else [cell]]
  let sigs : Sigs := {
    fns := [([callable],.void),([cell],callable)] ++ rootTypes.map (fun params => (params,.void))
    classes := [[.var 0],[]], pins := [[none],[]] }
  let slots := [[callable],[cell]] ++ rootTypes
  let infos := fns.mapIdx fun index fn => {
    body := some fn.body, cellTag := some 0
    cellHelper := index < 2 || (index == openedIndex && mode == "hidden-open")
    cellParams := if index == 1 || (index == openedIndex && !openReal) then [0] else []
    cellSlots := if index == 1 || (index == openedIndex && !openReal) then [0] else []
    inputs := if index == openedIndex && mode == "metadata-open" then [0] else []
    required := if index == 0 then [0] else [] }
  return (fns,sigs,slots,infos,closedIndex)

def main : IO Unit := do
  let mut bad := 0
  for reverse in [false,true] do
    for indirect in [false,true] do
      for deadMetadata in [false,true] do
        for mode in ["all-real-open","known-real-open","hidden-open","unknown-open","metadata-open"] do
          let (fns,sigs,slots,infos,entry) := program reverse indirect mode deadMetadata
          let prog : Prog := { fns := fns.toList, main := entry }
          let checked := prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs
          IO.println s!"reverse={reverse} indirect={indirect} deadMetadata={deadMetadata} mode={mode} check={prog.check} control={prog.checkControl} types={prog.checkTypes sigs slots} prelude={checkPrelude prog sigs}"
          unless checked do throw <| IO.userError "INVALID unrelated-cell unknown-formal model"
          let result := MetadataFlow.check fns infos #[[],[]]
          let admitted := match result with | .ok _ => true | .error _ => false
          let expected := mode == "all-real-open" || mode == "known-real-open" || mode == "hidden-open"
          IO.println s!"expected={expected} actual={repr result}"
          if admitted != expected then bad := bad + 1
  IO.println s!"40 policy classifications; {bad} mismatches"
  if bad > 0 then throw <| IO.userError "unrelated-cell unknown-formal boundary mismatch"
end UnrelatedCellUnknownFormal


namespace IncomingPrivateComponents
/- Incoming private cells hidden in typed data, not direct private formals.
   No Info.cellParams is supplied anywhere. Slot1 is typed as a private cell.
   The physical default prefix is Core-valid; the logical body omits that
   default exactly as the compiler's metadata-only body does. An unrelated
   fresh real cell is discarded AFTER extracting the incoming component.
   known=true observes a different fresh real cell while keeping the open
   carrier formal, so the positive control still uses the full alias state.
   inlineRead observes the component with NO typed local or cellSlots hint.
   Its paired controls also remove the unrelated allocation entirely.
   This is a Core/API policy test, not a Source escape claim. -/
private def callable : VTy := .ref [1] []
private def cell : VTy := .ref [0] [callable]
private def realCell : Expr := .heap (.new 0) [.heap (.new 1) []]

private def test (arrayCarrier known reverse inlineRead unrelated : Bool) : IO Bool := do
  let formalTy := if arrayCarrier then VTy.arr cell else .tup [cell,.int]
  let projection := if arrayCarrier then Expr.prim .index [.local 0,.lit (.int 0)]
    else .prim (.tupGet 0) [.local 0]
  let observed := if known then realCell else projection
  let logicalBody := if inlineRead then
      let read := Expr.call 0 [.heap (.get 0) [observed]]
      if unrelated then Expr.seq realCell read else read
    else Expr.seq (.assign 1 observed) (.seq realCell (.call 0 [.heap (.get 0) [.local 1]]))
  let sink : Fn := { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void }
  let closed : Fn := {
    name := "ClosedRoot", arity := 0, nslots := 0, decides := false,
    body := .call 0 [.heap (.get 0) [realCell]] }
  let caller : Fn := {
    name := "Caller", arity := 1, nslots := (if inlineRead then 1 else 2), decides := true, writes := true,
    body := if inlineRead then logicalBody else .seq (.assign 1 realCell) logicalBody }
  let fns := #[sink] ++ (if reverse then #[caller,closed] else #[closed,caller])
  let callerIndex := if reverse then 1 else 2
  let closedIndex := if reverse then 2 else 1
  let rootParams := if reverse then [[formalTy],[]] else [[],[formalTy]]
  let callerSlots := if inlineRead then [formalTy] else [formalTy,cell]
  let rootSlots := if reverse then [callerSlots,[]] else [[],callerSlots]
  let sigs : Sigs := {
    fns := [([callable],.void)] ++ rootParams.map (fun params => (params,.void))
    classes := [[.var 0],[]], pins := [[none],[]] }
  let slots := [[callable]] ++ rootSlots
  let prog : Prog := { fns := fns.toList, main := closedIndex }
  let valid := prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs
  IO.println s!"array={arrayCarrier} known={known} reverse={reverse} inline={inlineRead} check={prog.check} control={prog.checkControl} types={prog.checkTypes sigs slots} prelude={checkPrelude prog sigs}"
  unless valid do throw <| IO.userError "INVALID typed incoming-component model"
  let infos : Array MetadataFlow.Info := fns.mapIdx fun index fn => {
    body := some (if index == callerIndex then logicalBody else fn.body)
    cellTag := some 0
    cellHelper := index == 0
    cellSlots := if index == callerIndex && !inlineRead then [1] else []
    cellParams := []
    required := if index == 0 then [0] else [] }
  let results := sigs.fns.toArray.map fun (_, result) => MetadataValues.objectFree result
  let actual := MetadataFlow.check fns infos #[[],[]] false results
  let admitted := match actual with | .ok _ => true | .error _ => false
  IO.println s!"expected={known} actual={repr actual}"
  return admitted == known

def main : IO Unit := do
  let mut bad := 0
  -- Local and inline payloads with a discarded unrelated cell; then the
  -- exact inline program with that allocation removed.
  for (inlineRead, unrelated) in [(false,true),(true,true),(true,false)] do
    for arrayCarrier in [false,true] do
      for known in [false,true] do
        for reverse in [false,true] do
          unless (← test arrayCarrier known reverse inlineRead unrelated) do bad := bad + 1
  IO.println s!"24 typed incoming-component policy classifications; {bad} mismatches"
  if bad > 0 then throw <| IO.userError "typed incoming private component mismatch"
end IncomingPrivateComponents


namespace ExternalFormalFieldAliases
/- Ordinary external formals A/B have REAL identities and a mutable field
   containing a compiler private-cell identity. Stored metadata lives only
   inside that private cell: no ordinary shared-field metadata exemption is
   supplied. Param3 is explicitly metadata; Param2 is real. A/B may alias,
   while local4 is a MUST-alias copy of A. This tests field facts, not a new
   Source-level escape claim. Source-equivalent result certificates supplied.
 -/
private def callable : VTy := .ref [2] []
private def cell : VTy := .ref [0] [callable]
private def frame : VTy := .ref [1] []
private def newCell (metadata : Bool) : Expr := .heap (.new 0) [.local (if metadata then 3 else 2)]
private def write (receiver : Nat) (metadata : Bool) : Expr := .heap (.set 0) [.local receiver,newCell metadata]
private def observe (receiver : Nat) : Expr := .call 0 [.heap (.get 0) [.heap (.get 0) [.local receiver]]]

private def test (mode : String) (reverse : Bool) : IO Bool := do
  let after := match mode with
    | "same" => observe 0
    | "copy" => observe 4
    | "other" => observe 1
    | "invalidate-meta" => .seq (write 1 true) (observe 0)
    | "invalidate-real" => .seq (write 1 false) (observe 0)
    | "copy-meta" => .seq (write 4 true) (observe 0)
    | _ => .lit .void
  let logicalBody := Expr.seq (.assign 4 (.local 0)) (.seq (write 0 false) after)
  let sink : Fn := { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void }
  let caller : Fn := {
    name := "Caller", arity := 4, nslots := 5, decides := false, writes := true,
    body := .seq (.assign 4 (.local 0)) logicalBody }
  let closed : Fn := { name := "ClosedRoot", arity := 0, nslots := 0, decides := false, body := .lit .void }
  let fns := #[sink] ++ (if reverse then #[caller,closed] else #[closed,caller])
  let callerIndex := if reverse then 1 else 2
  let closedIndex := if reverse then 2 else 1
  let callerParams := [frame,frame,callable,callable]
  let callerSlots := callerParams ++ [frame]
  let rootParams := if reverse then [callerParams,[]] else [[],callerParams]
  let rootSlots := if reverse then [callerSlots,[]] else [[],callerSlots]
  let sigs : Sigs := {
    fns := [([callable],.void)] ++ rootParams.map (fun params => (params,.void))
    classes := [[.var 0],[cell],[]], pins := [[none],[],[]] }
  let slots := [[callable]] ++ rootSlots
  let prog : Prog := { fns := fns.toList, main := closedIndex }
  let valid := prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs
  IO.println s!"mode={mode} reverse={reverse} check={prog.check} control={prog.checkControl} types={prog.checkTypes sigs slots} prelude={checkPrelude prog sigs}"
  unless valid do throw <| IO.userError "INVALID external-formal field-alias model"
  let infos : Array MetadataFlow.Info := fns.mapIdx fun index fn => {
    body := some (if index == callerIndex then logicalBody else fn.body)
    cellTag := some 0
    cellHelper := index == 0
    nonCellSlots := if index == callerIndex then [0,1,2,3,4] else if index == 0 then [0] else []
    inputs := if index == callerIndex then [3] else []
    required := if index == 0 then [0] else [] }
  let results := sigs.fns.toArray.map fun (_, result) => MetadataValues.objectFree result
  let actual := MetadataFlow.check fns infos #[[],[],[]] false results
  let admitted := match actual with | .ok _ => true | .error _ => false
  let expected := ["same","copy","invalidate-real"].contains mode
  IO.println s!"expected={expected} actual={repr actual}"
  return admitted == expected

def main : IO Unit := do
  let mut bad := 0
  for reverse in [false,true] do
    for mode in ["same","copy","other","invalidate-meta","invalidate-real","copy-meta"] do
      unless (← test mode reverse) do bad := bad + 1
  IO.println s!"12 ordinary external-formal alias classifications; {bad} mismatches"
  if bad > 0 then throw <| IO.userError "external-formal field-alias mismatch"
end ExternalFormalFieldAliases


namespace ClosedScalarTransfers
/- API-policy tests with genuine object-free VTy certificates. Every call to
   MetadataFlow.check passes EXACTLY the result-type predicate used by Elab;
   no reference formal/result is asserted object-free. Bridges are excluded
   as independent roots, so the warm-all-certified-functions path must find
   Helper. Caller always has a metadata formal, including real-actual cases,
   ensuring the open action actually consumes the separate closed table.
   All programs are Core-validated; no runtime test of Never is attempted. -/

private def checked (label : String) (reverse : Bool) (sink helper closed caller : Fn)
    (helperParams : List VTy) (helperRet : VTy) (helperSlots : List VTy)
    (callerParams : List VTy) (callerSlots : List VTy) (expected debug : Bool) : IO Bool := do
  let fns := #[sink,helper] ++ (if reverse then #[caller,closed] else #[closed,caller])
  let callerIndex := if reverse then 2 else 3
  let closedIndex := if reverse then 3 else 2
  let rootParams := if reverse then [callerParams,[]] else [[],callerParams]
  let rootSlots := if reverse then [callerSlots,[]] else [[],callerSlots]
  let signatures : Sigs := {
    fns := [([.int],.void),(helperParams,helperRet)] ++ rootParams.map (fun params => (params,.void))
    classes := [[.var 0]], pins := [[none]] }
  let slots := [[.int],helperSlots] ++ rootSlots
  let prog : Prog := { fns := fns.toList, main := closedIndex }
  let valid := prog.check && prog.checkControl && prog.checkTypes signatures slots && checkPrelude prog signatures
  IO.println s!"{label} reverse={reverse} check={prog.check} control={prog.checkControl} types={prog.checkTypes signatures slots} prelude={checkPrelude prog signatures}"
  unless valid do throw <| IO.userError "INVALID closed-scalar policy model"
  let infos : Array MetadataFlow.Info := fns.mapIdx fun index fn => {
    body := some fn.body, cellTag := some 0
    cellHelper := index < 2
    objectFreeSlots := (signatures.fns[index]!.1.zipIdx).filterMap fun (ty, slot) =>
      if MetadataValues.objectFree ty then some slot else none
    inputs := if index == callerIndex then [0] else []
    required := if index == 0 then [0] else [] }
  let resultCertificates := signatures.fns.toArray.map fun (_, result) => MetadataValues.objectFree result
  let result := MetadataFlow.check fns infos #[[]] debug resultCertificates
  let admitted := match result with | .ok _ => true | .error _ => false
  IO.println s!"expected={expected} actual={repr result}"
  return admitted == expected

private def sink : Fn := { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void }

private def scalar (reverse passMetadata debug : Bool) : IO Bool := do
  let helper : Fn := {
    name := "CellClosedInt", arity := 1, nslots := 1, decides := false,
    body := .seq (.call 0 [.local 0]) (.local 0) }
  let closed : Fn := {
    name := "ClosedRoot", arity := 0, nslots := 0, decides := false,
    body := .seq (.call 1 [.lit (.int 7)]) (.lit .void) }
  let caller : Fn := {
    name := "Caller", arity := 2, nslots := 2, decides := false,
    body := .seq (.call 1 [.local (if passMetadata then 0 else 1)]) (.lit .void) }
  checked s!"scalar passMetadata={passMetadata}" reverse sink helper closed caller
    [.int] .int [.int] [.int,.int] [.int,.int] (!passMetadata) debug

private def tupleCase (reverse partialMetadata : Bool) (column : Nat) (debug : Bool) : IO Bool := do
  let tupleTy := VTy.tup [.int,.int]
  let helper : Fn := {
    name := "CellClosedTuple", arity := 1, nslots := 1, decides := false,
    body := .call 0 [.prim (.tupGet column) [.local 0]] }
  let closed : Fn := {
    name := "ClosedRoot", arity := 0, nslots := 0, decides := false,
    body := .call 1 [.prim .mkTup [.lit (.int 7),.lit (.int 8)]] }
  let caller : Fn := {
    name := "Caller", arity := 2, nslots := 2, decides := false,
    body := .call 1 [.prim .mkTup [.local (if partialMetadata then 0 else 1),.local 1]] }
  checked s!"tuple partialMetadata={partialMetadata} column={column}" reverse sink helper closed caller
    [tupleTy] .void [tupleTy] [.int,.int] [.int,.int] (!partialMetadata || column == 1) debug

private def neverCase (reverse diverges debug : Bool) : IO Bool := do
  let helper : Fn := {
    name := (if diverges then "CellClosedNever" else "CellClosedNormal"), arity := 0,
    nslots := 0, decides := false, body := (if diverges then .loop (.lit .void) else .lit .void) }
  let closed : Fn := {
    name := "ClosedRoot", arity := 0, nslots := 0, decides := false,
    body := .seq (.call 1 []) (.call 0 [.lit (.int 7)]) }
  let caller : Fn := {
    name := "Caller", arity := 1, nslots := 1, decides := false,
    body := .seq (.call 1 []) (.call 0 [.local 0]) }
  checked s!"never diverges={diverges}" reverse sink helper closed caller
    [] .void [] [.int] [.int] diverges debug

private def argumentEffects (reverse metadataWrite debug : Bool) : IO Bool := do
  let helper : Fn := {
    name := "CellClosedIntArgs", arity := 1, nslots := 1, decides := false,
    body := .seq (.call 0 [.local 0]) (.local 0) }
  let closed : Fn := {
    name := "ClosedRoot", arity := 0, nslots := 0, decides := false,
    body := .seq (.call 1 [.lit (.int 7)]) (.lit .void) }
  let cellTy := VTy.ref [0] [.int]
  let argument := Expr.seq (.heap (.set 0) [.local 2,.local (if metadataWrite then 0 else 1)]) (.lit (.int 7))
  let caller : Fn := {
    name := "Caller", arity := 2, nslots := 3, decides := false, writes := true,
    body := .seq (.assign 2 (.heap (.new 0) [.local 1]))
      (.seq (.call 1 [argument]) (.call 0 [.heap (.get 0) [.local 2]])) }
  checked s!"argument-sideeffect metadataWrite={metadataWrite}" reverse sink helper closed caller
    [.int] .int [.int] [.int,.int] [.int,.int,cellTy] (!metadataWrite) debug

def main (args : List String) : IO Unit := do
  let debug := args.contains "--debug"
  let mut bad := 0
  if args.contains "--args-only" then
    for reverse in [false,true] do
      for metadataWrite in [false,true] do
        unless (← argumentEffects reverse metadataWrite debug) do bad := bad + 1
    IO.println s!"4 argument-effect closed-transfer classifications; {bad} mismatches"
    if bad > 0 then throw <| IO.userError "argument effects lost by closed transfer"
    return
  for reverse in [false,true] do
    for metadata in [false,true] do
      unless (← scalar reverse metadata debug) do bad := bad + 1
      for column in [0,1] do
        unless (← tupleCase reverse metadata column debug) do bad := bad + 1
    for diverges in [false,true] do
      unless (← neverCase reverse diverges debug) do bad := bad + 1
    for metadataWrite in [false,true] do
      unless (← argumentEffects reverse metadataWrite debug) do bad := bad + 1
  IO.println s!"20 explicit-result-certificate classifications; {bad} mismatches"
  if bad > 0 then throw <| IO.userError "closed-scalar transfer policy mismatch"
end ClosedScalarTransfers


namespace IncomingArrayProtocols
/- Extra cellElements-path controls: the dynamic index is concretely 0+0,
   and the forE binds a typed private-cell item. Both incoming and known-fresh
   controls retain an ordinary array formal, so positives are full-open.
   No forged object-free or direct-private-formal certificate is supplied. -/
private def callable : VTy := .ref [1] []
private def cell : VTy := .ref [0] [callable]
private def fresh : Expr := .heap (.new 0) [.heap (.new 1) []]

private def test (forEach known reverse : Bool) : IO Bool := do
  let source := if known then Expr.prim .mkArr [fresh] else .local 0
  let observer := if forEach then
      Expr.seq (.forE 1 source (.lit .void) (.call 0 [.heap (.get 0) [.local 1]])) (.lit .void)
    else Expr.call 0 [.heap (.get 0) [.prim .index [source,.prim .add [.lit (.int 0),.lit (.int 0)]]]]
  let logicalBody := Expr.seq fresh observer
  let sink : Fn := { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void }
  let closed : Fn := {
    name := "ClosedRoot", arity := 0, nslots := 0, decides := false,
    body := .call 0 [.heap (.get 0) [fresh]] }
  let caller : Fn := {
    name := "Caller", arity := 1, nslots := (if forEach then 2 else 1), decides := true, writes := true,
    body := if forEach then .seq (.assign 1 fresh) logicalBody else logicalBody }
  let fns := #[sink] ++ (if reverse then #[caller,closed] else #[closed,caller])
  let callerIndex := if reverse then 1 else 2
  let entry := if reverse then 2 else 1
  let params := [VTy.arr cell]
  let cslots := if forEach then params ++ [cell] else params
  let sigs : Sigs := {
    fns := [([callable],.void)] ++ (if reverse then [(params,.void),([],.void)] else [([],.void),(params,.void)])
    classes := [[.var 0],[]], pins := [[none],[]] }
  let slots := [[callable]] ++ (if reverse then [cslots,[]] else [[],cslots])
  let prog : Prog := { fns := fns.toList, main := entry }
  let valid := prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs
  IO.println s!"forEach={forEach} known={known} reverse={reverse} check={prog.check} control={prog.checkControl} types={prog.checkTypes sigs slots} prelude={checkPrelude prog sigs}"
  unless valid do throw <| IO.userError "INVALID incoming-array protocol model"
  let infos : Array MetadataFlow.Info := fns.mapIdx fun index fn => {
    body := some (if index == callerIndex then logicalBody else fn.body)
    cellTag := some 0, cellHelper := index == 0
    cellSlots := if index == callerIndex && forEach then [1] else []
    nonCellSlots := if index == callerIndex then [0] else []
    required := if index == 0 then [0] else [] }
  let results := sigs.fns.toArray.map fun (_, result) => MetadataValues.objectFree result
  let actual := MetadataFlow.check fns infos #[[],[]] false results
  let admitted := match actual with | .ok _ => true | .error _ => false
  IO.println s!"expected={known} actual={repr actual}"
  return admitted == known

def main : IO Unit := do
  let mut bad := 0
  for forEach in [false,true] do
    for known in [false,true] do
      for reverse in [false,true] do
        unless (← test forEach known reverse) do bad := bad + 1
  IO.println s!"8 incoming-array protocol classifications; {bad} mismatches"
  if bad > 0 then throw <| IO.userError "incoming-array protocol mismatch"
end IncomingArrayProtocols


namespace UnknownAliasesTyped
private def callable : VTy := .ref [3] []
private def cell : VTy := .ref [0] [callable]
private def frame : VTy := .ref [1] []
private def outer : VTy := .ref [2] []
private def get (k : Nat) (e : Expr) : Expr := .heap (.get k) [e]
private def test (mode : String) (metadata : Bool) : IO Bool := do
 let indirect := mode != "direct"
 let borrowBody := Expr.call 0 [get 0 (get 1 (if indirect then get 0 (.local 0) else .local 0))]
 let tail := Expr.call 1 [if indirect then .local 1 else .local 0]
 let tail := if mode == "linked" then Expr.seq (.heap (.set 0) [.local 1,.local 0]) tail else tail
 let body := Expr.seq (.assign 3 (.heap (.new 0) [.local 2]))
   (.seq (.heap (.set 1) [.local 0,.local 3]) tail)
 let fns : Array Fn := #[
  { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void },
  { name := "Borrow", arity := 1, nslots := 1, decides := false, body := borrowBody },
  { name := "Caller", arity := 3, nslots := 4, decides := false, writes := true,
    body := .seq (.assign 3 (.heap (.new 0) [.local 2])) body },
  { name := "Root", arity := 0, nslots := 0, decides := false, body := .lit .void }]
 let sigs : Sigs := {
   fns := [([callable],.void),([if indirect then outer else frame],.void),([frame,outer,callable],.void),([],.void)],
   classes := [[.var 0],[.int,cell],[frame],[]], pins := [[none],[],[],[]] }
 let slots := [[callable],[if indirect then outer else frame],[frame,outer,callable,cell],[]]
 let prog : Prog := { fns := fns.toList, main := 3 }
 let valid := prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs
 IO.println s!"{mode} meta={metadata} check={prog.check} control={prog.checkControl} types={prog.checkTypes sigs slots} prelude={checkPrelude prog sigs}"
 unless valid do throw <| IO.userError "INVALID typed linked alias model"
 let infos : Array MetadataFlow.Info := fns.mapIdx fun i fn => {
   body := some (if i == 2 then body else fn.body), cellTag := some 0,
   cellHelper := i < 2, cellSlots := if i == 2 then [3] else [],
   required := if i == 0 then [0] else [], inputs := if i == 2 && metadata then [2] else [] }
 let actual := MetadataFlow.check fns infos #[[],[],[],[]]
 let admitted := match actual with | .ok _ => true | .error _ => false
 let expected := mode != "unlinked" && !metadata
 IO.println s!"expected={expected} actual={repr actual}"
 return admitted == expected
def main : IO Unit := do
 let mut bad := 0
 for mode in ["direct","linked","unlinked"] do
  for metadata in [false,true] do
   unless (← test mode metadata) do bad := bad + 1
 IO.println s!"6 typed direct/linked/unlinked classifications; {bad} mismatches"
 if bad > 0 then throw <| IO.userError "typed linked alias mismatch"
end UnknownAliasesTyped


namespace UnknownAliasesRuntime
private def callable : VTy := .ref [3] []
private def cell : VTy := .ref [0] [callable]
private def frame : VTy := .ref [1] []
private def outer : VTy := .ref [2] []
private def get (k : Nat) (e : Expr) : Expr := .heap (.get k) [e]
private def data (n : Int) : Expr := .heap (.new 3) [.lit (.int n)]
private def box (n : Int) : Expr := .heap (.new 0) [data n]
private def row (n : Int) : Expr := .heap (.new 1) [.lit (.int 0),box n]
private def test (mode : String) : IO Unit := do
 let indirect := mode != "direct"
 let tail := Expr.call 1 [if indirect then .local 1 else .local 0]
 let tail := if mode == "linked" then Expr.seq (.heap (.set 0) [.local 1,.local 0]) tail else tail
 let body := Expr.seq (.assign 3 (.heap (.new 0) [.local 2]))
   (.seq (.heap (.set 1) [.local 0,.local 3]) tail)
 let mainBody := Expr.seq (.assign 0 (row 1))
   (.seq (.assign 1 (.heap (.new 2) [row 9])) (.call 2 [.local 0,.local 1,data 7]))
 let fns : List Fn := [
  { name := "Execute", arity := 1, nslots := 1, decides := false, body := get 0 (.local 0) },
  { name := "Borrow", arity := 1, nslots := 1, decides := false,
    body := .call 0 [get 0 (get 1 (if indirect then get 0 (.local 0) else .local 0))] },
  { name := "Caller", arity := 3, nslots := 4, decides := false, writes := true, body },
  { name := "Main", arity := 0, nslots := 2, decides := false, writes := true, body := mainBody }]
 let sigs : Sigs := {
   fns := [([callable],.int),([if indirect then outer else frame],.int),([frame,outer,callable],.int),([],.int)]
   classes := [[.var 0],[.int,cell],[frame],[.int]], pins := [[none],[],[],[]] }
 let slots := [[callable],[if indirect then outer else frame],[frame,outer,callable,cell],[frame,outer]]
 let prog : Prog := { fns, main := 3 }
 let valid := prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs
 IO.println s!"{mode} check={prog.check} control={prog.checkControl} types={prog.checkTypes sigs slots} prelude={checkPrelude prog sigs}"
 unless valid do throw <| IO.userError "INVALID runtime alias witness"
 let expected := if mode == "unlinked" then 9 else 7
 match prog.runB 10000 10000 with
 | .res (.ok (.int result), output) =>
   IO.println s!"result={result} output={repr output} expected={expected}"
   unless result == expected && output.isEmpty do throw <| IO.userError "runtime alias mismatch"
 | _ => throw <| IO.userError "runtime alias witness failed"
def main : IO Unit := do
 for mode in ["direct","linked","unlinked"] do test mode
 IO.println "3 typed runtime alias witnesses PASS"
end UnknownAliasesRuntime


end MetadataIncomingCells

def main : IO Unit := do
  MetadataIncomingCells.UnrelatedCellUnknownFormal.main
  MetadataIncomingCells.IncomingPrivateComponents.main
  MetadataIncomingCells.ExternalFormalFieldAliases.main
  MetadataIncomingCells.ClosedScalarTransfers.main []
  MetadataIncomingCells.IncomingArrayProtocols.main
  MetadataIncomingCells.UnknownAliasesTyped.main
  MetadataIncomingCells.UnknownAliasesRuntime.main
