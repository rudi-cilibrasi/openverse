import OpenVerse.Front.MetadataFlow
import OpenVerse.Front.MetadataValues
import OpenVerse.Core.Check
import OpenVerse.Core.Control
import OpenVerse.Core.TypeCheck
open OpenVerse OpenVerse.Front
private def cell : VTy := .ref [0] [.int]
private def transport : VTy := .ref [1] []
private def get (field : Nat) (value : Expr) : Expr := .heap (.get field) [value]
private def box (value : Expr) : Expr := .heap (.new 0) [value]
private def execute (value : Expr) : Expr := .call 0 [value]
private def readTransport : Expr := execute (get 0 (get 0 (.local 5)))
private def test (mode : String) (reverse debug : Bool) : IO Bool := do
 let rewires := mode.startsWith "rewire"
 let optionalBody := Expr.ite (.assign 2 (.prim .query [.local 0]))
   (if rewires then .ite (.assign 3 (.prim .query [.local 1]))
      (.seq (.heap (.set 0) [.local 2,.local 3]) (.lit .void)) (.lit .void)
    else execute (get 0 (get 0 (.local 2)))) (.lit .void)
 let helperBody := if rewires then Expr.seq (.heap (.set 0) [.local 0,.local 1]) (.lit .void) else optionalBody
 let argument := if rewires then Expr.local 5 else if mode == "unknown" then Expr.local 0
   else if mode == "none" || mode.startsWith "argument" then .lit .none
   else .prim .mkSome [.local 5]
 let argument := if mode.startsWith "argument" then Expr.seq
   (.heap (.set 0) [.local 3,.local (if mode == "argument-meta" then 1 else 2)]) argument else argument
 let second := if rewires then Expr.local 4 else .lit .none
 let after := if mode.startsWith "argument" then execute (get 0 (.local 3))
   else if rewires then Expr.seq
     (.heap (.set 0) [.local (if mode == "rewire-B-meta" then 4 else 3),.local 1]) readTransport
   else .lit .void
 let body := Expr.seq (.assign 3 (box (.local (if mode == "some-meta" then 1 else 2))))
   (.seq (.assign 4 (box (.local 2)))
    (.seq (.assign 5 (.heap (.new 1) [.local 3]))
     (.seq (.call 1 [argument,second]) after)))
 let physical := Expr.seq (.assign 3 (box (.local 2)))
   (.seq (.assign 4 (box (.local 2)))
    (.seq (.assign 5 (.heap (.new 1) [box (.local 2)])) body))
 let sink : Fn := { name := "Execute", arity := 1, nslots := 1, decides := false, writes := false, body := .lit .void }
 let helper : Fn := {
   name := "PrivateOptionalTransport", arity := 2, nslots := 4,
   decides := false, writes := rewires,
   body := .seq (.assign 2 (.heap (.new 1) [box (.lit (.int 0))]))
     (.seq (.assign 3 (box (.lit (.int 0)))) helperBody) }
 let caller : Fn := {
   name := "Caller", arity := 3, nslots := 6, decides := false,
   writes := mode.startsWith "argument" || rewires, body := physical }
 let root : Fn := { name := "Root", arity := 0, nslots := 0, decides := false, writes := false, body := .lit .void }
 let fns := #[sink,helper] ++ if reverse then #[caller,root] else #[root,caller]
 let callerIx := if reverse then 2 else 3
 let rootIx := if reverse then 3 else 2
 let callerParams := [VTy.opt transport,.int,.int]
 let callerSlots := callerParams ++ [cell,cell,transport]
 let params := if reverse then [callerParams,[]] else [[],callerParams]
 let helperParams := if rewires then [transport,cell] else [VTy.opt transport,VTy.opt cell]
 let slots := [[VTy.int],helperParams ++ [transport,cell]] ++
   if reverse then [callerSlots,[]] else [[],callerSlots]
 let sigs : Sigs := {
   fns := [([VTy.int],.void),(helperParams,.void)] ++ params.map (fun ps => (ps,.void))
   classes := [[.var 0],[cell]], pins := [[none],[]] }
 let prog : Prog := { fns := fns.toList, main := rootIx }
 IO.println s!"{mode} reverse={reverse} check={prog.check} control={prog.checkControl} types={prog.checkTypes sigs slots} prelude={checkPrelude prog sigs}"
 unless prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs do
  throw <| IO.userError "INVALID empty-private-input certificate probe"
 let infos : Array MetadataFlow.Info := fns.mapIdx fun i fn => {
   body := some (if i == callerIx then body else if i == 1 then helperBody else fn.body)
   cellTag := some 0, cellTransportTag := some 1, cellHelper := i < 2
   cellParams := if i == 1 && rewires then [1] else []
   cellSlots := if i == callerIx then [3,4] else []
   objectFreeSlots := sigs.fns[i]!.1.zipIdx.filterMap fun (ty,slot) =>
     if MetadataValues.objectFree ty then some slot else none
   inputs := if i == callerIx then [1] else []
   required := if i == 0 then [0] else [] }
 let scalarReturns := sigs.fns.toArray.map fun (_,ty) => MetadataValues.objectFree ty
 let flags := MetadataValues.dataClassFlags sigs.classes.toArray #[[],[]] [0]
 let dataReturns := sigs.fns.toArray.map fun (_,ty) => MetadataValues.dataOnly flags ty
 let result := MetadataFlow.check fns infos #[[],[]] debug scalarReturns dataReturns #[]
 let admitted := match result with | .ok _ => true | .error _ => false
 let expected := ["none","some-real","argument-real","rewire-A-meta"].contains mode
 IO.println s!"expected={expected} actual={repr result}"
 return admitted == expected

private def emptyInputs (args : List String) : IO Unit := do
 let mut bad := 0
 for reverse in [false,true] do
  for mode in ["none","some-real","some-meta","unknown","argument-real","argument-meta","rewire-A-meta","rewire-B-meta"] do
   unless (← test mode reverse (args.contains "--debug")) do bad := bad + 1
 IO.println s!"16 empty-private-input classifications; {bad} mismatches"
 if bad > 0 then throw <| IO.userError "empty-private-input certificate mismatch"

/-- The strict data-formal premise comes only from the complete class graph,
    never from observing a currently real payload. Ordinary data mutations
    remain executable code; this policy view may omit only private aliases. -/
private def dataFormal (kind : String) (debug : Bool) : IO Bool := do
 let privatePayload := kind == "private"
 let boxTy := VTy.ref [1] []
 let payloadTy := if privatePayload then cell else VTy.int
 let read := Expr.heap (.get 0) [.local 0]
 -- Source lowers a metadata witness read through an explicitly seeded
 -- virtual slot (Functions.metadata.seeds = inputs ++ st.metadataSeeds).
 -- The metadata-fields class table alone supplies no value-role annotation.
 let observed := if privatePayload then get 0 read else read
 let tail := if kind == "metadata" then Expr.seq (.assign 2 observed) (execute (.local 2))
   else execute observed
 let body := Expr.seq (.heap (.set 0) [.local 0,.local 1]) tail
 let callerBody := Expr.seq (.assign 2 (.heap (.new 1)
     [if privatePayload then box (.local 0) else .local 0]))
   (.call 1 [.local 2,if privatePayload then box (.local 1) else .local (if kind == "metadata" then 1 else 0)])
 let fns : Array Fn := #[
  { name := "Execute", arity := 1, nslots := 1, decides := false, writes := false, body := .lit .void },
  { name := "MutateData", arity := 2, nslots := (if kind == "metadata" then 3 else 2),
    decides := false, writes := true,
    body := if kind == "metadata" then .seq (.assign 2 (.lit (.int 0))) body else body },
  { name := "Caller", arity := 2, nslots := 3, decides := false, writes := true,
    body := .seq (.assign 2 (.heap (.new 1) [if privatePayload then box (.local 0) else .local 0])) callerBody },
  { name := "Root", arity := 0, nslots := 0, decides := false, writes := false, body := .lit .void }]
 let sigs : Sigs := {
  fns := [([.int],.void),([boxTy,payloadTy],.void),([.int,.int],.void),([],.void)]
  classes := [[.var 0],[payloadTy]], pins := [[none],[]] }
 let slots := [[VTy.int],[boxTy,payloadTy] ++ (if kind == "metadata" then [.int] else []),[VTy.int,.int,boxTy],[]]
 let prog : Prog := { fns := fns.toList, main := 3 }
 IO.println s!"dataFormal={kind} check={prog.check} control={prog.checkControl} types={prog.checkTypes sigs slots} prelude={checkPrelude prog sigs}"
 unless prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs do
  throw <| IO.userError "INVALID strict-data formal model"
 let metadataFields := #[[],if kind == "metadata" then [0] else []]
 let flags := MetadataValues.dataClassFlags sigs.classes.toArray metadataFields [0]
 unless MetadataValues.dataOnly flags boxTy == (kind == "plain") do
  throw <| IO.userError "strict data certificate failed its reachable-class barrier"
 let infos : Array MetadataFlow.Info := fns.mapIdx fun i fn => {
  body := some (if i == 2 then callerBody else if i == 1 then body else fn.body), cellTag := some 0
  cellHelper := i < 2
  nonCellSlots := if i == 1 then [0] else []
  cellParams := if i == 1 && privatePayload then [1] else []
  objectFreeSlots := sigs.fns[i]!.1.zipIdx.filterMap fun (ty,slot) =>
    if MetadataValues.objectFree ty then some slot else none
  dataOnlySlots := sigs.fns[i]!.1.zipIdx.filterMap fun (ty,slot) =>
    if MetadataValues.dataOnly flags ty then some slot else none
  seeds := if i == 1 && kind == "metadata" then [2] else []
  metadataWrites := if i == 1 && kind == "metadata" then [(0,0)] else []
  inputs := if i == 2 then [1] else []
  required := if i == 0 then [0] else [] }
 let scalarReturns := sigs.fns.toArray.map fun (_,ty) => MetadataValues.objectFree ty
 let dataReturns := sigs.fns.toArray.map fun (_,ty) => MetadataValues.dataOnly flags ty
 let result := MetadataFlow.check fns infos metadataFields debug scalarReturns dataReturns #[]
 let admitted := match result with | .ok _ => true | .error _ => false
 IO.println s!"dataFormal={kind} expected={kind == "plain"} actual={repr result}"
 return admitted == (kind == "plain")

def main (args : List String) : IO Unit := do
 emptyInputs args
 for kind in ["plain","metadata","private"] do
  unless (← dataFormal kind (args.contains "--debug")) do
   throw <| IO.userError "strict data formal classification mismatch"
 IO.println "PASS 16 empty-private-input and 3 strict-data formal contracts"
