/- Core write requirements introduced by implementation lowering. -/
import OpenVerse.Core.Syntax

namespace OpenVerse.Front.CompilerWrites
open OpenVerse

private partial def callsMarked (marked : Array Bool) : Expr → Bool
  | .call f es => (marked[f]?.getD false) || es.any (callsMarked marked)
  | .assign _ e | .ret e | .print e | .loop e => callsMarked marked e
  | .seq a b => callsMarked marked a || callsMarked marked b
  | .prim _ es | .heap _ es => es.any (callsMarked marked)
  | .ite c t e => callsMarked marked c || callsMarked marked t || callsMarked marked e
  | .forE _ it f b => callsMarked marked it || callsMarked marked f || callsMarked marked b
  | _ => false

/-- Propagate only writes newly introduced by lowering. Existing source
    writers are not seeds: an unrelated read-only caller of one must still
    fail the independent Core check. Source effect permissions have already
    been checked, and are not changed by this implementation requirement. -/
def propagate (before after : Array Fn) : Array Fn := Id.run do
  let wasWriting (i : Nat) := (before[i]?.map (·.writes)).getD false
  let mut marked := after.mapIdx fun i fn => fn.writes && !wasWriting i
  if !marked.any id then return after
  let mut out := after
  for _ in [:after.size] do
    let mut changed := false
    for i in [:out.size] do
      let fn := out[i]!
      if !fn.writes && !wasWriting i && callsMarked marked fn.body then
        out := out.set! i { fn with writes := true }
        marked := marked.set! i true
        changed := true
    if !changed then break
  return out

end OpenVerse.Front.CompilerWrites
