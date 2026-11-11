import OpenVerse.Core.Prims

open OpenVerse

-- Separate call sites prevent common-subexpression elimination from making
-- fresh wrappers appear shared when the cache is absent.
@[noinline] def directInt (i : Int) : Value := Value.ofInt i

@[noinline] def arithmeticInt (i : Int) : Value :=
  match Prim.apply .add [.int i, .int 0] with
  | .ok v => v
  | _ => .none

@[noinline] def rangeInt (i : Int) : Value :=
  (rangeVals i i).head!

@[noinline] def lengthInt (n : Nat) : Value :=
  match Prim.apply .len [.arr (Array.replicate n Value.void)] with
  | .ok v => v
  | _ => .none

unsafe def main : IO Unit := do
  for n in [:1026] do
    let i : Int := n
    let v := directInt i
    unless ptrEq v (arithmeticInt i) && ptrEq v (rangeInt i) do
      throw (IO.userError s!"integer {i} did not share its cached wrapper")
  for n in ([0, 1, 1025] : List Nat) do
    unless ptrEq (directInt n) (lengthInt n) do
      throw (IO.userError s!"length {n} did not use its cached wrapper")
  for i in [Int64.minV, -1, 0, 1025, 1026, Int64.maxV] do
    unless directInt i = .int i && arithmeticInt i = .int i && rangeInt i = .int i do
      throw (IO.userError s!"integer boundary {i} changed value")
  for i in [Int64.minV - 1, Int64.maxV + 1] do
    unless Res.ofInt i = .err .overflow do
      throw (IO.userError s!"integer overflow {i} was not preserved")
  IO.println "small integer cache: 0..1025 share wrappers; boundaries and overflow preserved"
