/- Reference-slot liveness for the compiler provenance scheduler. -/
import OpenVerse.Front.MetadataPlan

namespace OpenVerse.Front.MetadataLiveness
open OpenVerse

structure Analysis where
  entries : Array Nat := #[]
  cleanup : Nat := 0
  full : Nat := 0
  deriving Inhabited

def Analysis.get (a : Analysis) (pc : Nat) : Nat := a.entries[pc]?.getD a.full

private def mask (slots : Nat) (indices : List Nat) : Nat :=
  indices.foldl (fun bits i => if i < slots then bits ||| (1 <<< i) else bits) 0

private def groupEdges (plan : MetadataPlan.Plan) (g : Nat) : List Nat :=
  match plan.groups[g]? with
  | none => [plan.nodes.size]
  | some group => [group.advance, group.next] ++ group.children.toList.map (·.2)

private def edges (plan : MetadataPlan.Plan) : MetadataPlan.Node → List Nat
  | .jump n | .atom _ _ n _ | .passTest n | .enterCall _ _ _ n |
      .leaveCall _ n | .call _ _ _ _ n | .functionReturn _ _ _ n _ _ |
      .pushCleanup _ n | .popCleanup n | .enterLoop _ n | .backLoop _ n |
      .leaveLoop _ n | .accumulate _ _ n | .spawnCheck _ _ n => [n]
  | .test _ a b | .beginTest a b | .choose a b => [a,b]
  | .fork g | .advance g => groupEdges plan g
  | .finish _ | .finishTask _ =>
      (List.range plan.groups.size).flatMap (groupEdges plan)
  | .cleanupDone | .drained | .ret _ => []

private partial def visitOrder (successors : Array (List Nat)) (pc : Nat) :
    StateM (Array Bool × List Nat) Unit := do
  let (seen, _) ← get
  if pc ≥ seen.size || seen[pc]! then return
  modify fun (seen, order) => (seen.set! pc true, order)
  for next in successors[pc]! do visitOrder successors next
  modify fun (seen, order) => (seen, pc :: order)

/-- Reverse postorder of the finite scheduler graph. This changes only the
    order in which pending abstract configurations reach their fixed point. -/
def controlOrder (plan : MetadataPlan.Plan) : Array Nat := Id.run do
  let successors := plan.nodes.map (edges plan)
  let (_, order) := ((do
    visitOrder successors plan.entry
    for pc in [:plan.nodes.size] do visitOrder successors pc
    : StateM (Array Bool × List Nat) Unit).run
      (Array.replicate plan.nodes.size false, [])).2
  let mut ranks := Array.replicate plan.nodes.size plan.nodes.size
  for (pc, rank) in order.zipIdx do ranks := ranks.set! pc rank
  return ranks

private def usesDefs (fns : Array Fn) (plan : MetadataPlan.Plan)
    (node : MetadataPlan.Node) : Nat × Nat :=
  let bits := mask plan.slots
  match node with
  | .atom e dst _ _ => (bits (MetadataPlan.reads e), bits [dst])
  | .test e _ _ => (bits (MetadataPlan.reads e), 0)
  | .call _ args _ dst _ => (bits args, bits [dst])
  | .enterCall g offset args _ =>
    let n := (fns[g]?.map (·.nslots)).getD 0
    (bits args, bits ((List.range n).map (offset + ·)))
  | .functionReturn _ value dst _ _ _ => (bits [value], bits [dst])
  | .accumulate dst value _ => (bits [dst,value], bits [dst])
  | .fork g =>
    match plan.groups[g]? with
    | none => ((1 <<< plan.slots) - 1, 0)
    | some group => (bits (group.arguments ++ group.task.toList), 0)
  | .spawnCheck _ args _ => (bits args, 0)
  | .finishTask value | .finish value | .ret value => (bits [value], 0)
  | _ => (0,0)

/-- Backward may-liveness. Unknown graph destinations retain every slot.
    Rollback destinations are explicit edges; cleanup entry requirements are
    also retained independently of the actor's current control position. -/
def build (fns : Array Fn) (plan : MetadataPlan.Plan) : Analysis := Id.run do
  let full := (1 <<< plan.slots) - 1
  let transfers := plan.nodes.map (usesDefs fns plan)
  let successors := plan.nodes.map (edges plan)
  let mut live := Array.replicate plan.nodes.size 0
  -- Revisit only predecessors whose successor facts changed. The equations
  -- and least fixed point are unchanged; a full scan otherwise propagates
  -- one edge per pass through long generated waiting producers.
  let mut predecessors := Array.replicate plan.nodes.size (#[] : Array Nat)
  for i in [:successors.size] do
    for next in successors[i]! do
      if next < predecessors.size then
        predecessors := predecessors.modify next (·.push i)
  let mut work := Array.range plan.nodes.size
  let mut queued := Array.replicate plan.nodes.size true
  while !work.isEmpty do
    let i := work.back!
    work := work.pop
    queued := queued.set! i false
    let after := successors[i]!.foldl (fun bits pc => bits ||| live[pc]?.getD full) 0
    let (uses, defs) := transfers[i]!
    let before := uses ||| (after &&& (full ^^^ defs))
    if before != live[i]! then
      live := live.set! i before
      for previous in predecessors[i]! do
        if !queued[previous]! then
          queued := queued.set! previous true
          work := work.push previous
  let cleanup := plan.cleanupEntries.foldl (fun bits pc => bits ||| live[pc]?.getD full) 0
  return { entries := live, cleanup, full }

end OpenVerse.Front.MetadataLiveness
