import OpenVerse.Front.MetadataLiveness
import OpenVerse.Front.MetadataBits
import OpenVerse.Front.MetadataReferences

namespace Packed
open OpenVerse.Front.MetadataBits

private def decode (a : Bits) : Array Bool := Array.ofFn (n := a.size) fun i => a.get i.val
private def require (label : String) (a : Bits) (expected : Array Bool) : IO Unit := do
  unless decode a == expected && a.bits < (1 <<< a.size) do
    throw <| IO.userError s!"{label}: size {a.size}"

private def sample (width seed : Nat) : Array Bool := Array.ofFn (n := width) fun i =>
  (i.val * 17 + seed * 13) % 29 < seed % 30

def run : IO Unit := do
  let widths := #[0,1,2,7,31,63,64,65,127,128,129,1485]
  let mut checks := 0
  for width in widths do
    for seed in [:32] do
      let dense := sample width seed
      let packed := Bits.ofArray dense
      require "encoding" packed dense
      require "zero padding" (packed.appendZeros 3) (dense ++ #[false,false,false])
      for i in [0,width/2,width-1,width,width+1] do
        for value in [false,true] do
          let expected := if i < width then dense.set! i value else dense
          require "write" (packed.set! i value) expected
          require "persistent input" packed dense
      require "indexed map" (packed.mapIdx fun i b => b != (i % 3 == 0))
        (dense.mapIdx fun i b => b != (i % 3 == 0))
      for otherWidth in widths do
        let other := sample otherWidth (seed+7)
        require "union" (packed.union (Bits.ofArray other)) (dense.zipWith (· || ·) other)
      checks := checks + 35
  -- Exhaust every per-cell truth assignment, at small and multiword widths.
  -- Each of the four arrays may also have a different extent.
  for width in widths do
    for truth in [:16] do
      for delta in [:3] do
        let ai := Array.replicate (width+delta) (truth.testBit 0)
        let bi := Array.replicate (width-delta) (truth.testBit 1)
        let a := Array.replicate width (truth.testBit 2)
        let b := Array.replicate (width+1) (truth.testBit 3)
        let expected := a.mapIdx fun i role =>
          if !(ai[i]?.getD false) then b[i]?.getD false
          else if !(bi[i]?.getD false) then role
          else role && b[i]?.getD false
        require "initialized shared mode" ((Bits.ofArray a).joinModes (Bits.ofArray ai)
          (Bits.ofArray b) (Bits.ofArray bi)) expected
        checks := checks + 1
  IO.println s!"Packed/dense Boolean fact equivalence checks passed: {checks}"
end Packed

namespace References
open OpenVerse.Front.MetadataReferences

private def samples : Array Refs := #[[], [0], [1], [2], [9], [2, 9], [9, 2], [2, 2], [0, 9, 2, 9]]
private def dense (size seed : Nat) : Array Refs :=
  Array.ofFn (n := size) fun i => samples[(seed + i.val * 7) % samples.size]!
private def sparse (values : Array Refs) : Memory := initial values.size fun i => values[i]!
private def union (a b : Refs) : Refs := (a ++ b).mergeSort (· ≤ ·) |>.eraseDups
private def verify (label : String) (values : Array Refs) (memory : Memory) : IO Unit := do
  unless memory.nslots == values.size do throw <| IO.userError s!"{label}: slot count"
  for i in [:values.size + 2] do
    unless get? memory i == values[i]? do throw <| IO.userError s!"{label}: lookup {i}"
  unless memory.slots.size == (values.filter (fun refs => !refs.isEmpty)).size do
    throw <| IO.userError s!"{label}: sparse occupancy"

def run : IO Unit := do
  let mut checks := 0
  for n in [:9] do
    for seed in [:samples.size] do
      let a := dense n seed
      let ma := sparse a
      verify "initial" a ma
      checks := checks + 1
      for i in [:n] do
        for value in samples do
          verify "set" (a.set! i value) (set ma i value)
          checks := checks + 1
      for m in [:9] do
        for other in [:samples.size] do
          let b := dense m other
          let mb := sparse b
          let joined := join ma mb
          verify "join" (a.zipWith union b) joined
          verify "reverse join" (b.zipWith union a) (join mb ma)
          -- The same snapshots are reused after both joins; joining must
          -- preserve the incoming paths used by transactional rollback.
          verify "left snapshot" a ma
          verify "right snapshot" b mb
          for value in samples do
            if !b.isEmpty then
              let changed := b.set! 0 value
              verify "write then join" (a.zipWith union changed) (join ma (set mb 0 value))
          checks := checks + 4 + (if b.isEmpty then 0 else samples.size)
  IO.println s!"Dense-reference equivalence checks passed: {checks}"
end References

namespace Fields
open OpenVerse OpenVerse.Front.MetadataReferences

private def samples : Array Refs := #[[],[0],[1],[2],[9],[2,9],[9,2],[2,2],[0,9,2,9]]
private def union (a b : Refs) : Refs := (a ++ b).mergeSort (· ≤ ·) |>.eraseDups
private def fields (seed : Nat) : Std.HashMap (Nat × Nat) Refs := Id.run do
  let mut result : Std.HashMap (Nat × Nat) Refs := {}
  for i in [:6] do
    if (seed+i)%3 != 0 then
      result := result.insert (4294967296+i/2,i%2) samples[(seed+i)%samples.size]!
  return result

def run : IO Unit := do
  let mut checks := 0
  for left in [:32] do
    for right in [:32] do
      let a := { initial 1 (fun _ => [4294967296]) with
        fields := fields left, uncertain := samples[left%samples.size]! }
      let b := { initial 1 (fun _ => [4294967296]) with
        fields := fields right, uncertain := samples[right%samples.size]! }
      let expected := b.fields.fold (fun m key value =>
        m.insert key (union (m[key]?.getD []) value)) a.fields
      let actual := join a b
      unless actual.fields == expected && actual.uncertain == union a.uncertain b.uncertain do
        throw <| IO.userError s!"field/uncertain join {left},{right}"
      let value := (eval #[] 0 actual (.heap (.get 0) [.local 0])).1
      unless value == union [] (expected[(4294967296,0)]?.getD [0]) do
        throw <| IO.userError s!"empty-vs-missing field load {left},{right}"
      checks := checks + 2
  IO.println s!"Reference field equivalence checks passed: {checks}"
end Fields

namespace Intersection
open OpenVerse.Front.MetadataBits

def run : IO Unit := do
  let mut checks := 0
  for n in [0,1,2,7,63,64,65,127,128,129,1485] do
    for m in [0,1,2,7,63,64,65,127,128,129,1485] do
      for seed in [:7] do
        let a := (List.range n).map (fun i => (i + seed) % 3 == 0) |>.toArray
        let b := (List.range m).map (fun i => (i + seed * 2) % 5 == 0) |>.toArray
        let actual := (Bits.ofArray a).intersect (Bits.ofArray b)
        let expected := a.zipWith (· && ·) b
        unless actual.size == expected.size do throw <| IO.userError "intersection width"
        for i in [:max n m + 2] do
          unless actual.get i == expected[i]?.getD false do
            throw <| IO.userError s!"intersection {n} {m} {seed} {i}"
        checks := checks + 1
  IO.println s!"Packed/dense intersection checks passed: {checks}"
end Intersection

namespace ScalarResults
open OpenVerse OpenVerse.Front.MetadataReferences

def run : IO Unit := do
  let memory := { initial 2 (fun i => [i+2]) with fields := ({} : Std.HashMap (Nat × Nat) Refs).insert (2,0) [3] }
  let body := Expr.ite (.lit (.logic true))
    (.seq (.heap (.set 0) [.local 0,.local 1]) (.call 0 [.local 0,.local 1])) (.lit (.int 7))
  let f : Fn := {name := "RecursiveScalar", arity := 2, nslots := 2, decides := false, body, writes := true}
  let (unknown, old) := call #[f] 17 memory 0 [[2],[3]]
  let (scalar, refined) := call #[f] 17 memory 0 [[2],[3]] #[true]
  unless unknown == [0] && scalar.isEmpty do throw <| IO.userError "recursive result classification"
  unless old.fields == refined.fields && old.uncertain == refined.uncertain do
    throw <| IO.userError "scalar result must retain recursive writes"
  unless (refined.fields[(2,0)]?.getD []).contains 0 && (refined.fields[(2,0)]?.getD []).contains 3 do
    throw <| IO.userError "writable recursion must still widen reachable fields"
  unless refined.slots == memory.slots do throw <| IO.userError "callee local restoration"
  let reference := { f with name := "RecursiveReference", body := .ite (.lit (.logic true)) (.call 0 [.local 0,.local 1]) (.local 0) }
  let (aliases, _) := call #[reference] 23 memory 0 [[2],[3]] #[false]
  unless aliases.contains 0 && aliases.contains 2 do throw <| IO.userError "reference recursion must retain aliases"
  IO.println "Scalar recursive reference contracts passed (result, writable effects, locals, reference control)"
end ScalarResults

namespace Containers
open OpenVerse OpenVerse.Front.MetadataReferences

def run : IO Unit := do
  let memory := initial 2 (fun i => [i+2])
  let scalar := Expr.prim .mkArr [.lit (.int 7),.lit (.int 9)]
  let (refs, plain) := eval #[] 1 memory scalar
  unless refs.isEmpty && plain.fields.isEmpty do throw <| IO.userError "scalar array references"
  let object := Expr.heap (.new 0) [.lit (.int 7)]
  let (allocated, heap) := eval #[] 2 memory object
  unless !allocated.isEmpty && heap.fields.size == 1 do throw <| IO.userError "scalar-field heap allocation lost identity"
  let (again, repeated) := eval #[] 2 heap object
  unless again == allocated && allocated.any repeated.uncertain.contains do throw <| IO.userError "repeated heap allocation"
  let row := Expr.prim .mkArr [.local 0]
  let nested := Expr.prim .flatten [.prim .mkArr [row]]
  let nestedItem := Expr.prim .index [nested,.lit (.int 0)]
  unless (eval #[] 3 memory nestedItem).1 == [2] do throw <| IO.userError "nested object alias through flatten"
  let update := Expr.prim .arrSet [scalar,.lit (.int 0),.local 1]
  let updatedItem := Expr.prim .index [update,.lit (.int 0)]
  unless (eval #[] 4 memory updatedItem).1 == [3] do throw <| IO.userError "object insertion after scalar array"
  let concat := Expr.prim .concat [scalar,row]
  unless (eval #[] 5 memory (.prim .index [concat,.lit (.int 0)])).1 == [2] do
    throw <| IO.userError "object alias through concatenation"
  IO.println "Container reference contracts passed (scalar values, heap identity, repetition, flatten, update, concat)"
end Containers

open OpenVerse.Front.MetadataReferences

-- Structural-sharing shortcuts keep exactly the original equality.
example (a b : Memory) : (a == b) =
    ((a.slots == b.slots) && (a.nslots == b.nslots) &&
      (a.fields == b.fields) && (a.uncertain == b.uncertain)) := rfl

namespace Liveness
open OpenVerse OpenVerse.Front

def run : IO Unit := do
  -- A loop needs predecessor revisits; the assignment kills the incoming
  -- destination while the branch retains both paths. Invalid destinations
  -- and cleanup roots must conservatively keep all slots.
  let plan : MetadataPlan.Plan := {
    slots := 3
    nodes := #[.atom (.local 0) 1 1 none, .choose 2 4,
      .atom (.local 1) 0 3 none, .jump 1, .ret 0, .jump 99]
    cleanupEntries := #[2,99] }
  let live := MetadataLiveness.build #[] plan
  unless live.entries == #[1,3,2,3,1,7] && live.cleanup == 7 && live.get 99 == 7 do
    throw <| IO.userError "liveness loop/kill/cleanup/unknown-edge regression"
  -- Generated producers contain long backwards chains. Every entry must
  -- learn the terminal read, regardless of the node numbering.
  let nodes := (Array.range 4096).map fun i =>
    if i == 0 then MetadataPlan.Node.ret 2 else .jump (i-1)
  let chain := MetadataLiveness.build #[] { slots := 3, nodes }
  unless chain.entries.all (· == 4) do
    throw <| IO.userError "liveness long predecessor chain regression"
  IO.println "Metadata liveness predecessor contracts passed"
end Liveness

def main : IO Unit := do
  Packed.run
  References.run
  Fields.run
  Intersection.run
  ScalarResults.run
  Containers.run
  Liveness.run
