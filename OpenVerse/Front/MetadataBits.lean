/- Packed finite Boolean facts for compiler provenance analysis. -/
import Init

namespace OpenVerse.Front.MetadataBits

structure Bits where
  size : Nat := 0
  bits : Nat := 0
  deriving BEq, Inhabited

namespace Bits

private def mask (size : Nat) : Nat := (1 <<< size) - 1

def get (a : Bits) (i : Nat) : Bool := i < a.size && a.bits.testBit i

def set! (a : Bits) (i : Nat) (value : Bool) : Bits :=
  if i ≥ a.size || a.get i == value then a
  else { a with bits := a.bits ^^^ (1 <<< i) }

def replicate (size : Nat) (value : Bool) : Bits :=
  { size, bits := if value then mask size else 0 }

def ofArray (values : Array Bool) : Bits := Id.run do
  let mut result := replicate values.size false
  for i in [:values.size] do
    if values[i]! then result := result.set! i true
  return result

def mapIdx (a : Bits) (f : Nat → Bool → Bool) : Bits := Id.run do
  let mut result := replicate a.size false
  for i in [:a.size] do
    if f i (a.get i) then result := result.set! i true
  return result

def appendZeros (a : Bits) (extra : Nat) : Bits := { a with size := a.size + extra }

def union (a b : Bits) : Bits :=
  if a.size == b.size then { size := a.size, bits := a.bits ||| b.bits }
  else
    let size := min a.size b.size
    { size, bits := (a.bits ||| b.bits) &&& mask size }

def intersect (a b : Bits) : Bits :=
  { size := min a.size b.size, bits := a.bits &&& b.bits }

/-- A mode is meaningful only after its path initialized the cell. -/
def joinModes (a ai b bi : Bits) : Bits :=
  -- Most slots have no shared mode. Reuse the empty mask directly.
  if a.bits == 0 && b.bits == 0 then a else
  let all := mask a.size
  { size := a.size
    bits := ((b.bits &&& (all ^^^ ai.bits)) |||
      (a.bits &&& ai.bits &&& (all ^^^ bi.bits)) |||
      (a.bits &&& b.bits &&& ai.bits &&& bi.bits)) &&& all }

end Bits
end OpenVerse.Front.MetadataBits
