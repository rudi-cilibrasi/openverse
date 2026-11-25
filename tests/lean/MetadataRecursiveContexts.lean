/- Private-cell calls of functions on a call cycle (#753). Such a function is
   not replayed once per caller heap: from the outermost call to its return it
   has one summary per ordinary key, whose input is the join of the contexts
   it is called in, solved as a fixed point. These Core models are the flows
   that summary must not lose: metadata that one level of a recursion puts in
   a private cell and a deeper level executes, through a fresh cell per level
   (the shape of a lazy loop's pending frames), through one cell written again,
   through the result, and through a second function on the cycle. Each has
   the control that unrolls the recursion into three functions, which are on no
   cycle and so keep their exact replay: the summary may refuse more than the
   replay, never less, and an all-real program is admitted by both.
   These are compiler API models with valid Core programs. -/
import OpenVerse

open OpenVerse OpenVerse.Front
namespace MetadataRecursiveContexts

-- Classes: 0 the private cell, 1 an executable carrier.
private def callable : VTy := .ref [1] []
private def cell : VTy := .ref [0] [callable]

private def execute (value : Expr) : Expr := .call 0 [value]
private def payload (cellSlot : Nat) : Expr := .heap (.get 0) [.local cellSlot]
private def freshCell (value : Expr) : Expr := .heap (.new 0) [value]

/-- One level `Walk(cell, value, count)`: what `shape` does with the cell, and
    `again`, the call of the next level, or nothing at the last one. It
    returns an executable value. -/
private def level (shape : String) (again : Option (List Expr → Expr)) : Expr :=
  let more : Expr := .prim .eq [.local 2, .lit (.int 0)]
  let next (cellValue : Expr) : Expr := match again with
    | some call => .seq (call [cellValue, .local 1, .local 2]) (.lit .void)
    | none => .lit .void
  match shape with
  -- a fresh cell per level holds the value; the level below executes it
  | "chain-execute" => .seq (.ite more (.seq (execute (payload 0)) (.lit .void))
      (next (freshCell (.local 1)))) (.local 1)
  -- the one cell is written with the value; the level below executes it
  | "store-execute" => .seq (.ite more (.seq (execute (payload 0)) (.lit .void))
      (.seq (.heap (.set 0) [.local 0, .local 1]) (next (.local 0)))) (.local 1)
  -- every level executes its cell before it passes a fresh one down
  | "execute-first" => .seq (execute (payload 0))
      (.seq (.ite more (.lit .void) (next (freshCell (.local 1)))) (.local 1))
  -- the last level returns its cell's payload, which the root executes
  | "result" => match again with
    | some call => .ite more (payload 0) (call [freshCell (.local 1), .local 1, .local 2])
    | none => payload 0
  -- the value only travels: every cell holds what the first one held
  | "carry-real" => .seq (execute (payload 0))
      (.seq (.ite more (.lit .void) (next (freshCell (payload 0)))) (.local 1))
  -- the value is stored at every level and never executed
  | _ => .seq (.ite more (.lit .void) (next (freshCell (.local 1)))) (.local 1)

/-- `recursive`: `Walk` calls itself, through `Step` when `viaStep`. Otherwise
    three levels call one another in a line. The functions are 0 `Execute`,
    1 to 3 the levels (`Walk`, `Step` or the second level, the third level),
    4 `Root(first, real, count)` with its cell in slot 3, 5 the closed entry. -/
private def classify (recursive viaStep : Bool) (shape : String) (metadata : Bool) : IO Bool := do
  let sink : Fn := { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void }
  let levelFn (name : String) (body : Expr) : Fn :=
    { name, arity := 3, nslots := 3, decides := true, writes := true, body }
  let forward (target : Nat) : Expr := .call target [.local 0, .local 1, .local 2]
  let levels : List Fn :=
    if recursive then
      [levelFn "Walk" (level shape (some fun args => .call (if viaStep then 2 else 1) args)),
        levelFn "Step" (forward 1), levelFn "Unused" (.local 1)]
    else
      [levelFn "Walk" (level shape (some fun args => .call 2 args)),
        levelFn "Walk2" (level shape (some fun args => .call 3 args)),
        levelFn "Walk3" (level shape none)]
  let walk : Expr := .call 1 [.local 3, .local 0, .local 2]
  let caller : Fn := {
    name := "Root", arity := 3, nslots := 4, decides := true, writes := true
    body := .seq (.assign 3 (freshCell (.local 1)))
      (.seq (if shape == "result" then execute walk else .seq walk (.lit .void)) (.lit .void)) }
  let closed : Fn := { name := "ClosedRoot", arity := 0, nslots := 0, decides := false, body := .lit .void }
  let fns := (sink :: levels ++ [caller, closed]).toArray
  let levelSig : List VTy × VTy := ([cell, callable, .int], callable)
  let sigs : Sigs := {
    fns := [([callable], .void), levelSig, levelSig, levelSig, ([callable, callable, .int], .void), ([], .void)]
    classes := [[.var 0], []], pins := [[none], []] }
  let slots := [[callable], [cell, callable, .int], [cell, callable, .int], [cell, callable, .int],
    [callable, callable, .int, cell], []]
  let prog : Prog := { fns := fns.toList, main := 5 }
  let valid := prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs
  unless valid do
    throw <| IO.userError s!"INVALID recursive-context model {shape}: check={prog.check} control={prog.checkControl} types={prog.checkTypes sigs slots} prelude={checkPrelude prog sigs}"
  let infos : Array MetadataFlow.Info := fns.mapIdx fun index fn => {
    body := some fn.body
    cellTag := some 0
    cellHelper := index ≤ 3
    cellParams := if 1 ≤ index && index ≤ 3 then [0] else []
    cellSlots := if 1 ≤ index && index ≤ 3 then [0] else if index == 4 then [3] else []
    inputs := if index == 4 && metadata then [0] else []
    required := if index == 0 then [0] else [] }
  let results := sigs.fns.toArray.map fun (_, result) => MetadataValues.objectFree result
  let actual := MetadataFlow.check fns infos #[[], []] false results
  let admitted := match actual with | .ok _ => true | .error _ => false
  IO.println s!"recursive={recursive} viaStep={viaStep} shape={shape} metadata={metadata} admitted={admitted}"
  return admitted

def main : IO Unit := do
  let mut bad := 0
  let mut count := 0
  -- (shape, whether metadata in the first parameter reaches Execute)
  for (shape, executes) in [("chain-execute", true), ("store-execute", true), ("execute-first", true),
      ("result", true), ("carry-real", false), ("keep", false)] do
    for metadata in [false, true] do
      let control ← classify false false shape metadata
      count := count + 1
      for viaStep in [false, true] do
        let summary ← classify true viaStep shape metadata
        count := count + 1
        -- Metadata that reaches Execute is refused, with one summary per key
        -- exactly as with a replay per heap.
        if metadata && executes && (control || summary) then bad := bad + 1
        -- The summary may refuse more than the replay, never less.
        if summary && !control then bad := bad + 1
        -- Metadata that is only kept, and every all-real program, is admitted.
        if !(metadata && executes) && !(control && summary) then bad := bad + 1
  IO.println s!"{count} recursive-context policy classifications; {bad} mismatches"
  if bad > 0 then throw <| IO.userError "recursive context policy mismatch"
end MetadataRecursiveContexts

def main : IO Unit := MetadataRecursiveContexts.main
