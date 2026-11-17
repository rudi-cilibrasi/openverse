/- Physical heap effects introduced by compiler-owned storage. -/
import OpenVerse.Core.Writes
import OpenVerse.Front.MetadataPlan

namespace OpenVerse.Front.PhysicalWrites
open OpenVerse

/-- Source permissions are checked before this pass. Lowering a logical local
    to a cell can nevertheless introduce a physical heap write. Preserve each
    declared writer and mark every physical writer and its transitive callers,
    so the existing Core write-soundness check remains truthful.

    Calls are indexed once; each newly marked function enters the worklist once.
    Invalid callees are left for the unchanged Core scoping checks. -/
def annotate (fns : Array Fn) : Array Fn := Id.run do
  let empty : Prog := { fns := [], main := 0 }
  let mut writes := fns.map fun fn => fn.writes || fn.body.writesHeap empty
  let mut callers := Array.replicate fns.size ([] : List Nat)
  for caller in [:fns.size] do
    for callee in MetadataPlan.calls fns[caller]!.body do
      if callee < fns.size then
        callers := callers.modify callee (caller :: ·)
  let mut pending := (List.range fns.size).filter (fun index => writes[index]!) |>.toArray
  let mut next := 0
  while next < pending.size do
    let callee := pending[next]!
    next := next + 1
    for caller in callers[callee]! do
      if !writes[caller]! then
        writes := writes.set! caller true
        pending := pending.push caller
  return fns.mapIdx fun index fn => { fn with writes := writes[index]! }

end OpenVerse.Front.PhysicalWrites
