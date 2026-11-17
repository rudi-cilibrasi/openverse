/- Actual-call alias, return, rollback and scheduling contracts for compiler-private
   logical cells. These test metadata classifications; source/runtime equivalence
   has separate controls. Internal tags here stand for compiler annotations. -/
import OpenVerse.Front.MetadataFlow

open OpenVerse OpenVerse.Front

namespace MetadataCellFlow

namespace Calls


private def get (slot : Nat) : Expr := .heap (.get 0) [.local slot]
private def newCell (slot : Nat) : Expr := .heap (.new 0) [.local slot]
private def save (slot value : Nat) : Expr := .assign slot (newCell value)
private def execute (value : Expr) : Expr := .call 0 [value]
private def mutate (a b value : Nat) : Expr := .call 1 [.local a, .local b, .local value]

private def programs (name : String) : Array Fn := Id.run do
  let sink : Fn := {
    name := "Execute", arity := 1, nslots := 1, decides := false
    body := .lit (.int 0) }
  let mutator : Fn := {
    name := "$sourceLoopReturnMutate", arity := 3, nslots := 4, decides := false
    body := if name == "loop-return-writeback" then
        .loop (.seq (.heap (.set 0) [.local 0, .local 2]) (.ret (.lit (.int 0))))
      else if name == "for-return-writeback" then
        .seq (.forE 3 (.prim .mkArr [.lit (.int 0)]) (.lit .void)
          (.ret (.seq (.heap (.set 0) [.local 0, .local 2]) (.lit (.int 0))))) (get 1)
      else if name == "break-writeback" then
        .seq (.loop (.seq (.heap (.set 0) [.local 0, .local 2]) .brk)) (get 1)
      else .seq (.heap (.set 0) [.local 0, .local 2]) (get 1) }
  let identity : Fn := {
    name := "$sourceLoopReturnIdentity", arity := 1, nslots := 1, decides := false
    body := .local 0 }
  let maker : Fn := {
    name := "$sourceLoopReturnMake", arity := 1, nslots := 2, decides := false
    body := if name.startsWith "factory-loop-return" then .loop (.ret (newCell 0))
      else if name.startsWith "factory-for-return" then
        .seq (.forE 1 (.prim .mkArr [.lit (.int 0)]) (.lit .void) (.ret (newCell 0))) (newCell 0)
      else if name == "factory-break-return-real" then
        .seq (.assign 1 (newCell 0)) (.seq (.loop .brk) (.local 1))
      else newCell 0 }
  let body := match name with
    | "independent-target" => .seq (save 2 0) (.seq (save 3 0) (execute (mutate 2 3 1)))
    | "same-alias" => .seq (save 2 0) (execute (mutate 2 2 1))
    | "callee-real-overwrite" => .seq (save 2 1) (execute (mutate 2 2 0))
    | "for-return-writeback" | "break-writeback" => .seq (save 2 0) (.seq (mutate 2 2 1) (execute (get 2)))
    | "factory-for-return-real" | "factory-break-return-real" => .seq (.assign 2 (.call 3 [.local 0])) (execute (get 2))
    | "factory-for-return-meta" => .seq (.assign 2 (.call 3 [.local 1])) (execute (get 2))
    | "loop-return-writeback" => .seq (save 2 0) (.seq (mutate 2 2 1) (execute (get 2)))
    | "factory-loop-return-real" => .seq (.assign 2 (.call 3 [.local 0])) (execute (get 2))
    | "factory-loop-return-meta" => .seq (.assign 2 (.call 3 [.local 1])) (execute (get 2))
    | "ignored-call-writeback" => .seq (save 2 0) (.seq (mutate 2 2 1) (execute (get 2)))
    | "returned-cell-real-overwrite" => .seq (save 2 1)
        (.seq (.assign 3 (.call 2 [.local 2])) (.seq (mutate 3 3 0) (execute (get 2))))
    | "returned-cell-metadata-write" => .seq (save 2 0)
        (.seq (.assign 3 (.call 2 [.local 2])) (.seq (mutate 3 3 1) (execute (get 2))))
    | "two-maker-calls-real-first" => .seq (.assign 2 (.call 3 [.local 0]))
        (.seq (.assign 3 (.call 3 [.local 1])) (execute (get 2)))
    | _ => .seq (.assign 2 (.call 3 [.local 1]))
        (.seq (.assign 3 (.call 3 [.local 0])) (execute (get 2)))
  let caller : Fn := { name := "Caller", arity := 2, nslots := 4, decides := false, body }
  return #[sink, mutator, identity, maker, caller]

private def infos (fns : Array Fn) (metadata : Bool) : Array MetadataFlow.Info :=
  fns.mapIdx fun i fn => {
    body := some fn.body, cellTag := some 0
    cellParams := if i == 1 then [0,1] else if i == 2 then [0] else []
    cellSlots := if i == 1 then [0,1] else if i == 2 then [0] else if i == 4 then [2,3] else []
    cellHelper := i == 1 || i == 2 || i == 3
    required := if i == 0 then [0] else []
    inputs := if i == 4 && metadata then [1] else [] }

def main (args : List String) : IO Unit := do
  let cases := [
    ("independent-target", true), ("same-alias", false), ("callee-real-overwrite", true),
    ("ignored-call-writeback", false), ("returned-cell-real-overwrite", true),
    ("returned-cell-metadata-write", false), ("two-maker-calls-real-first", true),
    ("two-maker-calls-metadata-first", false), ("loop-return-writeback", false),
    ("factory-loop-return-real", true), ("factory-loop-return-meta", false),
    ("for-return-writeback", false), ("break-writeback", false),
    ("factory-for-return-real", true), ("factory-for-return-meta", false),
    ("factory-break-return-real", true)]
  let mut failures := 0
  for (name, expectedMetadata) in cases do
    let fns := programs name
    for metadata in [false,true] do
      let expected := !metadata || expectedMetadata
      let result := MetadataFlow.check fns (infos fns metadata) #[[]]
      let admitted := match result with | .ok _ => true | .error _ => false
      let diagnostic := match result with | .ok _ => "" | .error message => message
      IO.println s!"{name} metadata={metadata}: admitted={admitted}, expected={expected} {diagnostic}"
      if admitted != expected then failures := failures + 1
  IO.println s!"TOTAL {cases.length * 2} Core API classifications; {failures} failures (no runtime claim)"
  if failures > 0 && args.contains "--strict" then
    throw <| IO.userError "private-cell call contract failed"
end Calls

namespace Cleanup


private def getCell (e : Expr) : Expr := .heap (.get 0) [e]
private def get (slot : Nat) : Expr := getCell (.local slot)
private def setCell (value : Expr) : Expr := .heap (.set 0) [.local 0, value]
private def newCell (slot : Nat) : Expr := .heap (.new 0) [.local slot]
private def execute (value : Expr) : Expr := .call 0 [value]
private def withCleanup (cleanup body : Expr) : Expr :=
  .seq (.ite (.prim .fail []) cleanup (.lit .void)) body

/-- Source elaboration saves the operand, emits normal cleanup, then
    returns the saved slot. The marker alone describes cancellation only. -/
private def normalExit (cleanup value : Expr) : Expr :=
  .seq (.assign 4 value) (.seq cleanup (.ret (.local 4)))

private def deferredExit (cleanup value : Expr) : Expr :=
  withCleanup cleanup (normalExit cleanup value)

private def helperBody (name : String) : Expr :=
  let taint := setCell (.local 2)
  match name with
  | "cleanup-writeback" => deferredExit taint (.lit (.int 0))
  | "reset-after-operand" | "taint-after-saved-value" | "taint-after-saved-nextread" =>
    deferredExit taint (get 0)
  | "identity-cleanup-reset" | "identity-cleanup-taint" =>
    deferredExit taint (.local 0)
  | "saved-identity-realloc-real-first" | "saved-identity-realloc-meta-first" =>
    .seq (.assign 3 (.call 3 [.local 2]))
      (deferredExit (.call 3 [get 0]) (.local 3))
  | "cleanup-failure-rollback" =>
    deferredExit (.ite (.seq taint (.prim .fail [])) (.lit .void) (.lit .void)) (.lit (.int 0))
  | "nested-cleanup-meta-last" =>
    withCleanup taint (withCleanup (setCell (get 1))
      (normalExit (.seq (setCell (get 1)) taint) (.local 0)))
  | _ => withCleanup (setCell (get 1)) (withCleanup taint
      (normalExit (.seq taint (setCell (get 1))) (.local 0)))

private def programs (name : String) : Array Fn := Id.run do
  let sink : Fn := {
    name := "Execute", arity := 1, nslots := 1, decides := false
    body := .lit (.int 0) }
  let helper : Fn := {
    name := "$sourceLoopReturnCleanup", arity := 3, nslots := 5, decides := false
    body := helperBody name }
  let identity : Fn := {
    name := "$sourceLoopReturnIdentity", arity := 1, nslots := 1, decides := false
    body := .local 0 }
  let maker : Fn := {
    name := "$sourceLoopReturnMake", arity := 1, nslots := 1, decides := false
    body := newCell 0 }
  let initiallyMetadata := ["reset-after-operand", "identity-cleanup-reset",
    "saved-identity-realloc-real-first"].contains name
  let realArgument := ["reset-after-operand", "identity-cleanup-reset",
    "saved-identity-realloc-real-first"].contains name
  let call : Expr := .call 1 [.local 2, .local 3, .local (if realArgument then 0 else 1)]
  let use := if ["cleanup-writeback", "taint-after-saved-nextread", "cleanup-failure-rollback"].contains name then
      .seq call (execute (get 2))
    else if ["reset-after-operand", "taint-after-saved-value"].contains name then execute call
    else execute (getCell call)
  let body : Expr := .seq (.assign 2 (newCell (if initiallyMetadata then 1 else 0)))
    (.seq (.assign 3 (newCell 0)) use)
  let caller : Fn := {
    name := "Caller", arity := 2, nslots := 4, decides := false, body }
  return #[sink, helper, identity, maker, caller]

private def infos (fns : Array Fn) (metadata : Bool) : Array MetadataFlow.Info :=
  fns.mapIdx fun i fn => {
    body := some fn.body, cellTag := some 0
    cellParams := if i == 1 then [0,1] else if i == 2 then [0] else []
    cellSlots := if i == 1 then [0,1,3] else if i == 2 then [0] else if i == 4 then [2,3] else []
    cellHelper := i == 1 || i == 2 || i == 3
    required := if i == 0 then [0] else []
    inputs := if i == 4 && metadata then [1] else [] }

def main (args : List String) : IO Unit := do
  let cases := [
    ("cleanup-writeback", false), ("reset-after-operand", false),
    ("taint-after-saved-value", true), ("taint-after-saved-nextread", false),
    ("identity-cleanup-reset", true), ("identity-cleanup-taint", false),
    ("saved-identity-realloc-real-first", true), ("saved-identity-realloc-meta-first", false),
    ("cleanup-failure-rollback", true), ("nested-cleanup-meta-last", false),
    ("nested-cleanup-real-last", true)]
  let mut failures := 0
  for (name, expectedMetadata) in cases do
    let fns := programs name
    for metadata in [false,true] do
      let expected := !metadata || expectedMetadata
      let result := MetadataFlow.check fns (infos fns metadata) #[[]]
      let admitted := match result with | .ok _ => true | .error _ => false
      let diagnostic := match result with | .ok _ => "" | .error message => message
      IO.println s!"{name} metadata={metadata}: admitted={admitted}, expected={expected} {diagnostic}"
      if admitted != expected then failures := failures + 1
  IO.println s!"TOTAL {cases.length * 2} cleanup Core API classifications; {failures} failures (no runtime claim)"
  if failures > 0 && args.contains "--strict" then
    throw <| IO.userError "private-cell cleanup call contract failed"
end Cleanup

namespace PendingArguments
private def get (e : Expr) : Expr  :=  .heap (.get 0) [e]
private def make (i : Nat) : Expr  :=  .call 1 [.local i]
private def pair (a b : Expr) : Expr  :=  .call 2 [a,b]
private def first (e : Expr) : Expr  :=  .prim (.tupGet 0) [e]
private def write (cell value : Nat) : Expr  :=  .call 3 [.local cell,.local value]
private def exec (e : Expr) : Expr  :=  .call 0 [e,.lit (.int 0)]
private def programs (name : String) : Array Fn  :=  Id.run do
  let body  :=  match name with
    | "condition-failure-rolls-back" => .seq (.assign 2 (make 0))
        (.ite (.seq (write 2 1) (.prim .fail [])) (exec (get (.local 2))) (exec (get (.local 2))))
    | "condition-failure-cannot-hide-exec" => .seq (.assign 2 (make 0))
        (.ite (.seq (write 2 1) (.seq (exec (get (.local 2))) (.prim .fail [])))
          (.lit (.int 0)) (exec (get (.local 2))))
    | "pending-factory-real-first" => exec (get (first (pair (make 0) (make 1))))
    | "pending-factory-meta-first" => exec (get (first (pair (make 1) (make 0))))
    | "array-factory-real-first" => exec (get (.prim .index [.prim .mkArr [make 0,make 1],.lit (.int 0)]))
    | "array-factory-meta-first" => exec (get (.prim .index [.prim .mkArr [make 1,make 0],.lit (.int 0)]))
    | "pending-alias-sees-meta" => .seq (.assign 2 (make 0))
        (exec (get (first (pair (.local 2) (.seq (write 2 1) (.local 2))))))
    | "pending-alias-sees-real" => .seq (.assign 2 (make 1))
        (exec (get (first (pair (.local 2) (.seq (write 2 0) (.local 2))))))
    | "pending-independent-real" => .seq (.assign 2 (make 0)) (.seq (.assign 3 (make 0))
        (exec (get (first (pair (.local 2) (.seq (write 3 1) (.local 3)))))))
    | "pending-independent-meta" => .seq (.assign 2 (make 1)) (.seq (.assign 3 (make 1))
        (exec (get (first (pair (.local 2) (.seq (write 3 0) (.local 3)))))))
    | "value-snapshot-stays-real" => .seq (.assign 2 (make 0))
        (.call 0 [get (.local 2), .seq (write 2 1) (.lit (.int 0))])
    | _ => .seq (.assign 2 (make 1))
        (.call 0 [get (.local 2), .seq (write 2 0) (.lit (.int 0))])
  return #[
    {name := "Execute",arity := 2,nslots := 2,decides := false,body := .lit (.int 0)},
    {name := "$sourceLoopReturnMake",arity := 1,nslots := 1,decides := false,body := .heap (.new 0) [.local 0]},
    {name := "$sourceLoopReturnPair",arity := 2,nslots := 2,decides := false,body := .prim .mkTup [.local 0,.local 1]},
    {name := "$sourceLoopReturnWrite",arity := 2,nslots := 2,decides := false,body := .seq (.heap (.set 0) [.local 0,.local 1]) (.lit (.int 0))},
    {name := "Caller",arity := 2,nslots := 4,decides := false,body}]
private def infos (fns : Array Fn) (metadata : Bool) : Array MetadataFlow.Info  := 
 fns.mapIdx fun i fn => {
   body := some fn.body
   cellTag := some 0
   cellParams := if i == 2 then [0,1] else if i == 3 then [0] else []
   cellSlots := if i == 2 then [0,1] else if i == 3 then [0] else if i == 4 then [2,3] else []
   cellHelper :=  i == 1  ||  i == 2  ||  i == 3
   required := if i == 0 then [0] else []
   inputs := if i == 4  &&  metadata then [1] else []}
def main : IO Unit  :=  do
 let cases  :=  [("condition-failure-rolls-back",true),("condition-failure-cannot-hide-exec",false),("pending-factory-real-first",true),("pending-factory-meta-first",false),
  ("array-factory-real-first",true),("array-factory-meta-first",false),
  ("pending-alias-sees-meta",false),("pending-alias-sees-real",true),
  ("pending-independent-real",true),("pending-independent-meta",false),
  ("value-snapshot-stays-real",true),("value-snapshot-stays-meta",false)]
 let mut bad  :=  0
 for (name,expectedMeta) in cases do
  for metadata in [false,true] do
   let fns  :=  programs name
   let result  :=  MetadataFlow.check fns (infos fns metadata) #[[]]
   let admitted  :=  match result with | .ok _ => true | .error _ => false
   let expected  :=  !metadata  ||  expectedMeta
   IO.println s!"{name} metadata={metadata} admitted={admitted} expected={expected}"
   if admitted != expected then bad := bad+1
 IO.println s!"24 classifications; {bad} mismatches"
 if bad>0 then throw <| IO.userError "pending argument role mismatch"
end PendingArguments

namespace Carriers
private def get (e : Expr) : Expr := .heap (.get 0) [e]
def main : IO Unit := do
 let mut failures := 0
 for kind in ["direct","transport","tuple","array","external-field"] do
  let select : Expr := match kind with
   | "direct" => .local 0
   | "tuple" => .prim (.tupGet 0) [.local 0]
   | "array" => .prim .index [.local 0,.lit (.int 0)]
   | _ => get (.local 0)
  let carrier : Expr := match kind with
   | "direct" => .local 2
   | "tuple" => .prim .mkTup [.local 2]
   | "array" => .prim .mkArr [.local 2]
   | _ => .heap (.new 1) [.local 2]
  let fns : Array Fn := #[
   { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit (.int 0) },
   { name := "Borrow", arity := 1, nslots := 1, decides := false,
     body := .call 0 [get select] },
   { name := "Caller", arity := 2, nslots := 4, decides := false,
     body := .seq (.assign 2 (.heap (.new 0) [.local 1]))
       (if kind == "external-field" then
         .seq (.heap (.set 0) [.local 0,.local 2]) (.call 1 [.local 0])
        else .seq (.assign 3 carrier) (.call 1 [.local 3])) }]
  for metadata in [false,true] do
   let infos : Array MetadataFlow.Info := fns.mapIdx fun i fn => {
     body := some fn.body
     cellTag := some 0
     cellTransportTag := some 1
     cellSlots := if i == 2 then [2] else []
     required := if i == 0 then [0] else []
     inputs := if i == 2 && metadata then [1] else [] }
   let result := MetadataFlow.check fns infos #[[],[]]
   let admitted := match result with | .ok _ => true | .error _ => false
   if admitted != !metadata then failures := failures + 1
   IO.println s!"kind={kind} metadata={metadata}; expected admission={!metadata}; actual={repr result}"
 IO.println s!"{failures} mismatches"
 if failures > 0 then throw <| IO.userError "private-cell carrier borrower contract failed"
end Carriers

namespace UnknownAliases
private def get (field : Nat) (e : Expr) : Expr := .heap (.get field) [e]
def main : IO Unit := do
 let mut bad := 0
 for indirect in [false,true] do
  let fns : Array Fn := #[
    { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit (.int 0) },
    { name := "Borrow", arity := 1, nslots := 1, decides := false,
      body := .call 0 [get 0 (get 1 (if indirect then get 0 (.local 0) else .local 0))] },
    { name := "Caller", arity := 3, nslots := 4, decides := false,
      body := .seq (.assign 3 (.heap (.new 0) [.local 2]))
        (.seq (.heap (.set 1) [.local 0,.local 3])
          (.call 1 [if indirect then .local 1 else .local 0])) }]
  for metadata in [false,true] do
   let infos : Array MetadataFlow.Info := fns.mapIdx fun i fn => {
     body := some fn.body
     cellTag := some 0
     cellSlots := if i == 2 then [3] else []
     required := if i == 0 then [0] else []
     inputs := if i == 2 && metadata then [2] else [] }
   let result := MetadataFlow.check fns infos #[[],[]]
   let admitted := match result with | .ok _ => true | .error _ => false
   IO.println s!"indirect={indirect} metadata={metadata}; expected={!metadata}; actual={repr result}"
   if admitted != !metadata then bad := bad+1
 IO.println s!"4 classifications; {bad} mismatches"
 if bad>0 then throw <| IO.userError "unknown nested alias contract failed"
end UnknownAliases

namespace Cancellation
private def get (slot : Nat) : Expr := .heap (.get 0) [.local slot]
private def write : Expr := .heap (.set 0) [.local 0,.local 1]
private def child : Expr :=
 .seq (.ite (.prim .fail []) write (.lit .void))
  (.seq (.call 1 [.lit (.float 0x3ff0000000000000)])
   (.seq (.assign 2 (.lit .void)) (.seq write (.ret (.local 2)))))
def main : IO Unit := do
 let mut bad := 0
 for reset in [false,true] do
  let initial := if reset then 1 else 0
  let replacement := if reset then 0 else 1
  let fns : Array Fn := #[
   { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void },
   { name := "$Sleep", arity := 1, nslots := 1, decides := false, body := .lit .void },
   { name := "$sourceLoopReturnChild", arity := 2, nslots := 3, decides := false, body := child },
   { name := "$raceMark", arity := 1, nslots := 1, decides := false, body := .lit .void },
   { name := "Caller", arity := 2, nslots := 3, decides := false,
     body := .seq (.assign 2 (.heap (.new 0) [.local initial]))
      (.seq (.call 3 [.prim .mkArr [.call 2 [.local 2,.local replacement],.lit .void]])
       (.call 0 [get 2])) }]
  for metadata in [false,true] do
   let infos : Array MetadataFlow.Info := fns.mapIdx fun i fn => {
    body := some fn.body
    cellTag := some 0
    cellParams := if i == 2 then [0] else []
    cellSlots := if i == 2 then [0] else if i == 4 then [2] else []
    cellHelper := i == 2
    required := if i == 0 then [0] else []
    inputs := if i == 4 && metadata then [1] else [] }
   let result := MetadataFlow.check fns infos #[[]]
   let admitted := match result with | .ok _ => true | .error _ => false
   let expected := !metadata || reset
   IO.println s!"reset={reset} metadata={metadata}; expected={expected}; actual={repr result}"
   if admitted != expected then bad := bad+1
 IO.println s!"4 classifications; {bad} mismatches"
 if bad>0 then throw <| IO.userError "cancellation payload contract failed"
end Cancellation

namespace RecursiveArguments
private def get (e : Expr) : Expr  :=  .heap (.get 0) [e]
private def make (i : Nat) : Expr  :=  .call 1 [.local i,.lit (.int 2)]
private def pair (a b : Expr) : Expr  :=  .call 2 [a,b]
private def first (e : Expr) : Expr  :=  .prim (.tupGet 0) [e]
private def write (cell value : Nat) : Expr  :=  .call 3 [.local cell,.local value]
private def exec (e : Expr) : Expr  :=  .call 0 [e,.lit (.int 0)]
private def programs (name : String) : Array Fn  :=  Id.run do
  let body  :=  match name with
    | "condition-failure-rolls-back" => .seq (.assign 2 (make 0))
        (.ite (.seq (write 2 1) (.prim .fail [])) (exec (get (.local 2))) (exec (get (.local 2))))
    | "condition-failure-cannot-hide-exec" => .seq (.assign 2 (make 0))
        (.ite (.seq (write 2 1) (.seq (exec (get (.local 2))) (.prim .fail [])))
          (.lit (.int 0)) (exec (get (.local 2))))
    | "pending-factory-real-first" => exec (get (first (pair (make 0) (make 1))))
    | "pending-factory-meta-first" => exec (get (first (pair (make 1) (make 0))))
    | "array-factory-real-first" => exec (get (.prim .index [.prim .mkArr [make 0,make 1],.lit (.int 0)]))
    | "array-factory-meta-first" => exec (get (.prim .index [.prim .mkArr [make 1,make 0],.lit (.int 0)]))
    | "pending-alias-sees-meta" => .seq (.assign 2 (make 0))
        (exec (get (first (pair (.local 2) (.seq (write 2 1) (.local 2))))))
    | "pending-alias-sees-real" => .seq (.assign 2 (make 1))
        (exec (get (first (pair (.local 2) (.seq (write 2 0) (.local 2))))))
    | "pending-independent-real" => .seq (.assign 2 (make 0)) (.seq (.assign 3 (make 0))
        (exec (get (first (pair (.local 2) (.seq (write 3 1) (.local 3)))))))
    | "pending-independent-meta" => .seq (.assign 2 (make 1)) (.seq (.assign 3 (make 1))
        (exec (get (first (pair (.local 2) (.seq (write 3 0) (.local 3)))))))
    | "value-snapshot-stays-real" => .seq (.assign 2 (make 0))
        (.call 0 [get (.local 2), .seq (write 2 1) (.lit (.int 0))])
    | _ => .seq (.assign 2 (make 1))
        (.call 0 [get (.local 2), .seq (write 2 0) (.lit (.int 0))])
  return #[
    {name := "Execute",arity := 2,nslots := 2,decides := false,body := .lit (.int 0)},
    {name := "$sourceLoopReturnMake",arity := 2,nslots := 2,decides := false,
      body := .ite (.prim .gt [.local 1,.lit (.int 0)])
        (.call 1 [.local 0,.prim .sub [.local 1,.lit (.int 1)]])
        (.heap (.new 0) [.local 0])},
    {name := "$sourceLoopReturnPair",arity := 2,nslots := 2,decides := false,body := .prim .mkTup [.local 0,.local 1]},
    {name := "$sourceLoopReturnWrite",arity := 2,nslots := 2,decides := false,body := .seq (.heap (.set 0) [.local 0,.local 1]) (.lit (.int 0))},
    {name := "Caller",arity := 2,nslots := 4,decides := false,body}]
private def infos (fns : Array Fn) (metadata : Bool) : Array MetadataFlow.Info  := 
 fns.mapIdx fun i fn => {
   body := some fn.body
   cellTag := some 0
   cellParams := if i == 2 then [0,1] else if i == 3 then [0] else []
   cellSlots := if i == 2 then [0,1] else if i == 3 then [0] else if i == 4 then [2,3] else []
   cellHelper :=  i == 1  ||  i == 2  ||  i == 3
   required := if i == 0 then [0] else []
   inputs := if i == 4  &&  metadata then [1] else []}
def main : IO Unit  :=  do
 let cases  :=  [("condition-failure-rolls-back",true),("condition-failure-cannot-hide-exec",false),("pending-factory-real-first",true),("pending-factory-meta-first",false),
  ("array-factory-real-first",true),("array-factory-meta-first",false),
  ("pending-alias-sees-meta",false),("pending-alias-sees-real",true),
  ("pending-independent-real",true),("pending-independent-meta",false),
  ("value-snapshot-stays-real",true),("value-snapshot-stays-meta",false)]
 let mut bad  :=  0
 for (name,expectedMeta) in cases do
  for metadata in [false,true] do
   let fns  :=  programs name
   let result  :=  MetadataFlow.check fns (infos fns metadata) #[[]]
   let admitted  :=  match result with | .ok _ => true | .error _ => false
   let expected  :=  !metadata  ||  expectedMeta
   IO.println s!"{name} metadata={metadata} admitted={admitted} expected={expected}"
   if admitted != expected then bad := bad+1
 IO.println s!"24 classifications; {bad} mismatches"
 if bad>0 then throw <| IO.userError "pending argument role mismatch"
end RecursiveArguments

namespace RecursiveMutation
private def get (e : Expr) : Expr  :=  .heap (.get 0) [e]
private def make (i : Nat) : Expr  :=  .call 1 [.local i,.lit (.int 2)]
private def pair (a b : Expr) : Expr  :=  .call 2 [a,b]
private def first (e : Expr) : Expr  :=  .prim (.tupGet 0) [e]
private def write (cell value : Nat) : Expr  :=  .call 3 [.local cell,.local value,.lit (.int 2)]
private def exec (e : Expr) : Expr  :=  .call 0 [e,.lit (.int 0)]
private def programs (name : String) : Array Fn  :=  Id.run do
  let body  :=  match name with
    | "condition-failure-rolls-back" => .seq (.assign 2 (make 0))
        (.ite (.seq (write 2 1) (.prim .fail [])) (exec (get (.local 2))) (exec (get (.local 2))))
    | "condition-failure-cannot-hide-exec" => .seq (.assign 2 (make 0))
        (.ite (.seq (write 2 1) (.seq (exec (get (.local 2))) (.prim .fail [])))
          (.lit (.int 0)) (exec (get (.local 2))))
    | "pending-factory-real-first" => exec (get (first (pair (make 0) (make 1))))
    | "pending-factory-meta-first" => exec (get (first (pair (make 1) (make 0))))
    | "array-factory-real-first" => exec (get (.prim .index [.prim .mkArr [make 0,make 1],.lit (.int 0)]))
    | "array-factory-meta-first" => exec (get (.prim .index [.prim .mkArr [make 1,make 0],.lit (.int 0)]))
    | "pending-alias-sees-meta" => .seq (.assign 2 (make 0))
        (exec (get (first (pair (.local 2) (.seq (write 2 1) (.local 2))))))
    | "pending-alias-sees-real" => .seq (.assign 2 (make 1))
        (exec (get (first (pair (.local 2) (.seq (write 2 0) (.local 2))))))
    | "pending-independent-real" => .seq (.assign 2 (make 0)) (.seq (.assign 3 (make 0))
        (exec (get (first (pair (.local 2) (.seq (write 3 1) (.local 3)))))))
    | "pending-independent-meta" => .seq (.assign 2 (make 1)) (.seq (.assign 3 (make 1))
        (exec (get (first (pair (.local 2) (.seq (write 3 0) (.local 3)))))))
    | "value-snapshot-stays-real" => .seq (.assign 2 (make 0))
        (.call 0 [get (.local 2), .seq (write 2 1) (.lit (.int 0))])
    | _ => .seq (.assign 2 (make 1))
        (.call 0 [get (.local 2), .seq (write 2 0) (.lit (.int 0))])
  return #[
    {name := "Execute",arity := 2,nslots := 2,decides := false,body := .lit (.int 0)},
    {name := "$sourceLoopReturnMake",arity := 2,nslots := 2,decides := false,
      body := .ite (.prim .gt [.local 1,.lit (.int 0)])
        (.call 1 [.local 0,.prim .sub [.local 1,.lit (.int 1)]])
        (.heap (.new 0) [.local 0])},
    {name := "$sourceLoopReturnPair",arity := 2,nslots := 2,decides := false,body := .prim .mkTup [.local 0,.local 1]},
    {name := "$sourceLoopReturnWrite",arity := 3,nslots := 3,decides := false,
      body := .ite (.prim .gt [.local 2,.lit (.int 0)])
        (.call 3 [.local 0,.local 1,.prim .sub [.local 2,.lit (.int 1)]])
        (.seq (.heap (.set 0) [.local 0,.local 1]) (.lit (.int 0)))},
    {name := "Caller",arity := 2,nslots := 4,decides := false,body}]
private def infos (fns : Array Fn) (metadata : Bool) : Array MetadataFlow.Info  := 
 fns.mapIdx fun i fn => {
   body := some fn.body
   cellTag := some 0
   cellParams := if i == 2 then [0,1] else if i == 3 then [0] else []
   cellSlots := if i == 2 then [0,1] else if i == 3 then [0] else if i == 4 then [2,3] else []
   cellHelper :=  i == 1  ||  i == 2  ||  i == 3
   required := if i == 0 then [0] else []
   inputs := if i == 4  &&  metadata then [1] else []}
def main : IO Unit  :=  do
 let cases  :=  [("condition-failure-rolls-back",true),("condition-failure-cannot-hide-exec",false),("pending-factory-real-first",true),("pending-factory-meta-first",false),
  ("array-factory-real-first",true),("array-factory-meta-first",false),
  ("pending-alias-sees-meta",false),("pending-alias-sees-real",true),
  ("pending-independent-real",true),("pending-independent-meta",false),
  ("value-snapshot-stays-real",true),("value-snapshot-stays-meta",false)]
 let mut bad  :=  0
 for (name,expectedMeta) in cases do
  for metadata in [false,true] do
   let fns  :=  programs name
   let result  :=  MetadataFlow.check fns (infos fns metadata) #[[]]
   let admitted  :=  match result with | .ok _ => true | .error _ => false
   let expected  :=  !metadata  ||  expectedMeta
   IO.println s!"{name} metadata={metadata} admitted={admitted} expected={expected}"
   if admitted != expected then bad := bad+1
 IO.println s!"24 classifications; {bad} mismatches"
 if bad>0 then throw <| IO.userError "pending argument role mismatch"
end RecursiveMutation

namespace RecursiveWriteback
private def get : Expr := .heap (.get 0) [.local 0]
private def write (slot : Nat) : Expr := .heap (.set 0) [.local 0, .local slot]
private def runCase (reset metadata : Bool) : Except String Unit := do
  let helper : Fn := {
    name := "$sourceLoopReturnRecur", arity := 3, nslots := 3, decides := false,
    body := .ite (.lit .void)
      (.seq (.call 1 [.local 0, .local 1, .local 2])
        (.seq (write (if reset then 1 else 2)) (.lit (.int 0))))
      (.seq (write (if reset then 1 else 1)) (.lit (.int 0))) }
  let fs : Array Fn := #[
    {name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void}, helper,
    {name := "Caller", arity := 2, nslots := 3, decides := false, body :=
      .seq (.assign 2 (.heap (.new 0) [.local (if reset then 1 else 0)]))
        (.seq (.call 1 [.local 2, .local 0, .local 1]) (.call 0 [.heap (.get 0) [.local 2]]))}]
  let info : Array MetadataFlow.Info := fs.mapIdx fun i f => {
    body := some f.body, cellTag := some 0, cellHelper := i == 1,
    required := if i == 0 then [0] else [],
    inputs := if i == 2 && metadata then [1] else [],
    cellSlots := if i == 1 then [0] else if i == 2 then [2] else [] }
  MetadataFlow.check fs info #[[]]
def main : IO Unit := do
  for reset in [false,true] do
    for metadata in [false,true] do
      let result := runCase reset metadata
      let actual := match result with | .ok _ => true | _ => false
      let expected := reset || !metadata
      IO.println s!"reset={reset} metadata={metadata} actual={actual} expected={expected}"
      if actual != expected then throw (IO.userError s!"bad recursive transfer: {repr result}")
end RecursiveWriteback

namespace BackgroundMetadata

def main : IO Unit := do
  let fns : Array Fn := #[
    { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void },
    { name := "Metadata", arity := 0, nslots := 0, decides := false, body := .lit .void },
    { name := "$Sleep", arity := 1, nslots := 1, decides := false, body := .lit .void },
    { name := "$branchMark", arity := 1, nslots := 1, decides := false, body := .lit .void },
    { name := "Worker", arity := 1, nslots := 1, decides := false, body :=
        .seq (.heap (.set 0) [.local 0, .call 1 []])
          (.loop (.call 2 [.lit (.float 4607182418800017408)])) },
    { name := "Caller", arity := 0, nslots := 1, decides := false, body :=
        .seq (.assign 0 (.heap (.new 0) [.lit .void]))
          (.seq (.call 3 [.prim .mkArr [.call 4 [.local 0]]])
            (.call 0 [.heap (.get 0) [.local 0]])) }]
  for metadata in [false,true] do
    let infos : Array MetadataFlow.Info := fns.mapIdx fun i fn => {
      body := some fn.body, cellTag := some 0
      cellSlots := if i == 4 then [0] else if i == 5 then [0] else []
      cellHelper := i == 4
      required := if i == 0 then [0] else []
      metadataResult := i == 1 && metadata }
    let result := MetadataFlow.check fns infos #[[]]
    let actual := match result with | .ok _ => true | _ => false
    IO.println s!"metadata={metadata}; actual={actual}; expected={!metadata}; {repr result}"
    if actual != !metadata then throw <| IO.userError "hidden metadata from background worker"
end BackgroundMetadata

end MetadataCellFlow

def main : IO Unit := do
  MetadataCellFlow.Calls.main ["--strict"]
  MetadataCellFlow.Cleanup.main ["--strict"]
  MetadataCellFlow.PendingArguments.main
  MetadataCellFlow.Carriers.main
  MetadataCellFlow.UnknownAliases.main
  MetadataCellFlow.Cancellation.main
  MetadataCellFlow.RecursiveArguments.main
  MetadataCellFlow.RecursiveMutation.main
  MetadataCellFlow.RecursiveWriteback.main
  MetadataCellFlow.BackgroundMetadata.main
