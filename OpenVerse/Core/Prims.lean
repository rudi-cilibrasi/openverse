/-
  OpenVerse — the meaning of each primitive operation.

  `Prim.apply` is total: any argument list of the wrong shape gives
  `err .type`, which the type checker rules out for elaborated programs but
  which the C runtime also reports, so that both implementations agree on
  every loaded program, typed or not.

  The integer operations are the seam with the C runtime: `runtime/src/arith.c`
  implements them and the QuickProof law `proofs/quickproof/arith` states the
  same conditions (see `docs/SEAMS.md`).
-/
import OpenVerse.Core.Syntax

namespace OpenVerse

/-- Floor division `⌊a / b⌋` for `b ≠ 0`. -/
def floorDivInt (a b : Int) : Int := Int.fdiv a b
/-- Ceiling division `⌈a / b⌉` for `b ≠ 0`. -/
def ceilDivInt (a b : Int) : Int := -Int.fdiv (-a) b

/-- The bytes of a Verse string (`[]char`), or `none` if it is not one. -/
def asBytes : List Value → Option (List Nat)
  | [] => some []
  | .char c :: vs => (asBytes vs).map (c :: ·)
  | _ :: _ => none

/-- `asBytes` with an accumulator, so that the compiled code is a loop: the
    definition above recurses once per character, natively, and a long
    `Print` overflowed the stack (#97). Proofs use `asBytes`; the compiler
    uses this (`asBytes_eq_asBytesTR`). -/
def asBytesTR (vs : List Value) : Option (List Nat) := go vs []
where
  go : List Value → List Nat → Option (List Nat)
    | [], acc => some acc.reverse
    | .char c :: vs, acc => go vs (c :: acc)
    | _ :: _, _ => none

theorem asBytesTR_go (vs : List Value) (acc : List Nat) :
    asBytesTR.go vs acc = (asBytes vs).map (acc.reverse ++ ·) := by
  induction vs generalizing acc with
  | nil => simp [asBytesTR.go, asBytes]
  | cons v vs ih =>
    cases v <;> simp [asBytesTR.go, asBytes, ih, Option.map_map, Function.comp_def]

@[csimp] theorem asBytes_eq_asBytesTR : @asBytes = @asBytesTR := by
  funext vs; simp [asBytesTR, asBytesTR_go]

/-- Decimal rendering of an int, as bytes (ASCII). -/
def intBytes (i : Int) : List Nat := (toString i).toUTF8.toList.map (·.toNat)

/-- A float to an int (#127): fails on NaN or an infinity; a result out of
    the int range is the overflow error (the API's integer-bounds error). -/
def VFloat.toIntRes (r : VFloat.Rounding) (b : UInt64) : Res :=
  if !VFloat.isFinite b then .fail
  else match VFloat.toInt? r b with
    | some i => .ok (.int i)
    | none => .err .overflow

/-- The string value of `ToString(v)`. -/
def toStrValue : Value → Res
  | .int i => .ok (.arr ((intBytes i).map Value.char).toArray)
  | .char c => .ok (.arr #[.char c])
  | .float b => .ok (Value.ofString (VFloat.render b))
  | .arr vs => match asBytes vs.toList with
    | some _ => .ok (.arr vs)
    | none => .err .type
  | _ => .err .type

/-- Concatenate a list of arrays (the result of nested `for` generators). -/
def flattenArrs : List Value → Option (List Value)
  | [] => some []
  | .arr xs :: rest => (flattenArrs rest).map (xs.toList ++ ·)
  | _ :: _ => none

/-- `flattenArrs` with an accumulator, compiled as a loop (#97): the definition
    above recurses once per outer `for` iteration. -/
def flattenArrsTR (vs : List Value) : Option (List Value) := go vs []
where
  go : List Value → List Value → Option (List Value)
    | [], acc => some acc.reverse
    | .arr xs :: rest, acc => go rest (xs.toList.reverse ++ acc)
    | _ :: _, _ => none

theorem flattenArrsTR_go (vs acc : List Value) :
    flattenArrsTR.go vs acc = (flattenArrs vs).map (acc.reverse ++ ·) := by
  induction vs generalizing acc with
  | nil => simp [flattenArrsTR.go, flattenArrs]
  | cons v vs ih =>
    cases v <;> simp [flattenArrsTR.go, flattenArrs, ih, Option.map_map, Function.comp_def]

@[csimp] theorem flattenArrs_eq_flattenArrsTR : @flattenArrs = @flattenArrsTR := by
  funext vs; simp [flattenArrsTR, flattenArrsTR_go]

/-- The elements of the inclusive range `a..b` (empty when `a > b`). -/
def rangeVals (a b : Int) : List Value :=
  (List.range (b + 1 - a).toNat).map fun (k : Nat) => Value.ofInt (a + (k : Int))

/-- Comparison helper: succeed with the left operand when `b` holds. -/
def cmpRes (b : Bool) (left : Value) : Res := if b then .ok left else .fail

/-- The meaning of each primitive. -/
def Prim.apply : Prim → List Value → Res
  | .add, [.int a, .int b] => Res.ofInt (a + b)
  | .sub, [.int a, .int b] => Res.ofInt (a - b)
  | .mul, [.int a, .int b] => Res.ofInt (a * b)
  | .neg, [.int a] => Res.ofInt (-a)
  | .abs, [.int a] => Res.ofInt (if a < 0 then -a else a)
  | .floorDiv, [.int a, .int b] => if b = 0 then .fail else Res.ofInt (floorDivInt a b)
  | .ceilDiv, [.int a, .int b] => if b = 0 then .fail else Res.ofInt (ceilDivInt a b)
  | .quotient, [.int a, .int b] => if b = 0 then .fail else Res.ofInt (Int.ediv a b)
  | .modulo, [.int a, .int b] => if b = 0 then .fail else Res.ofInt (Int.emod a b)
  | .lt, [.int a, .int b] => cmpRes (decide (a < b)) (Value.ofInt a)
  | .le, [.int a, .int b] => cmpRes (decide (a ≤ b)) (Value.ofInt a)
  | .gt, [.int a, .int b] => cmpRes (decide (a > b)) (Value.ofInt a)
  | .ge, [.int a, .int b] => cmpRes (decide (a ≥ b)) (Value.ofInt a)
  | .lt, [.char a, .char b] => cmpRes (decide (a < b)) (.char a)
  | .le, [.char a, .char b] => cmpRes (decide (a ≤ b)) (.char a)
  | .gt, [.char a, .char b] => cmpRes (decide (a > b)) (.char a)
  | .ge, [.char a, .char b] => cmpRes (decide (a ≥ b)) (.char a)
  | .eq, [a, b] => cmpRes (decide (a = b)) a
  | .ne, [a, b] => cmpRes (decide (a ≠ b)) a
  | .query, [.logic b] => if b then .ok (.logic true) else .fail
  | .query, [.none] => .fail
  | .query, [.some v] => .ok v
  | .mkArr, vs => .ok (.arr vs.toArray)
  | .mkTup, vs => .ok (.tup vs)
  | .mkSome, [v] => .ok (.some v)
  | .concat, [.arr xs, .arr ys] => .ok (.arr (xs ++ ys))
  | .flatten, [.arr xss] => match flattenArrs xss.toList with
    | some vs => .ok (.arr vs.toArray)
    | none => .err .type
  | .range, [.int a, .int b] => .ok (.arr (rangeVals a b).toArray)
  | .index, [.arr xs, .int i] =>
    if 0 ≤ i then match xs[i.toNat]? with
      | some v => .ok v
      | none => .fail
    else .fail
  | .len, [.arr xs] => .ok (Value.ofInt xs.size)
  | .arrSet, [.arr xs, .int i, v] =>
    if 0 ≤ i ∧ i.toNat < xs.size then .ok (.arr (xs.setIfInBounds i.toNat v)) else .fail
  | .tupGet k, [.tup vs] => match vs[k]? with
    | some v => .ok v
    | none => .err .type
  | .toStr, [v] => toStrValue v
  | .fadd, [.float a, .float b] => .ok (.float (VFloat.canon (VFloat.ofBits a + VFloat.ofBits b)))
  | .fsub, [.float a, .float b] => .ok (.float (VFloat.canon (VFloat.ofBits a - VFloat.ofBits b)))
  | .fmul, [.float a, .float b] => .ok (.float (VFloat.canon (VFloat.ofBits a * VFloat.ofBits b)))
  | .fdiv, [.float a, .float b] => .ok (.float (VFloat.canon (VFloat.ofBits a / VFloat.ofBits b)))
  | .fneg, [.float a] => .ok (.float (VFloat.canon (-VFloat.ofBits a)))
  | .fabs, [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).abs))
  | .fmin, [.float a, .float b] => .ok (.float (VFloat.fmin a b))
  | .fmax, [.float a, .float b] => .ok (.float (VFloat.fmax a b))
  | .flt, [.float a, .float b] => cmpRes (decide (VFloat.ofBits a < VFloat.ofBits b)) (.float a)
  -- (`NaN <= NaN` and `NaN >= NaN` succeed, as NaN equals itself, #132)
  | .fle, [.float a, .float b] => cmpRes (a == b || decide (VFloat.ofBits a ≤ VFloat.ofBits b)) (.float a)
  | .fgt, [.float a, .float b] => cmpRes (decide (VFloat.ofBits b < VFloat.ofBits a)) (.float a)
  | .fge, [.float a, .float b] => cmpRes (a == b || decide (VFloat.ofBits b ≤ VFloat.ofBits a)) (.float a)
  | .fofInt, [.int i] => .ok (.float (VFloat.canon (Float.ofInt i)))
  | .ffloor, [.float a] => VFloat.toIntRes .floor a
  | .fceil, [.float a] => VFloat.toIntRes .ceil a
  | .fround, [.float a] => VFloat.toIntRes .round a
  | .ftrunc, [.float a] => VFloat.toIntRes .trunc a
  | .fsqrt, [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).sqrt))
  | .fexp, [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).exp))
  | .fln, [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).log))
  | .fsin, [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).sin))
  | .fcos, [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).cos))
  | .ftan, [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).tan))
  | .fasin, [.float a] => .ok (.float (VFloat.canon (VFloat.clamp1 (VFloat.ofBits a)).asin))
  | .facos, [.float a] => .ok (.float (VFloat.canon (VFloat.clamp1 (VFloat.ofBits a)).acos))
  | .fatan, [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).atan))
  | .fpow, [.float a, .float b] => .ok (.float (VFloat.canon (Float.pow (VFloat.ofBits a) (VFloat.ofBits b))))
  | .fatan2, [.float a, .float b] => .ok (.float (VFloat.canon (Float.atan2 (VFloat.ofBits a) (VFloat.ofBits b))))
  | .fisFinite, [.float a] => if VFloat.isFinite a then .ok (.float a) else .fail
  | .fofBits, [.int i] => .ok (.float (VFloat.canon (VFloat.ofBits (UInt64.ofNat (i % (2 ^ 64 : Int)).toNat))))
  | .fail, [] => .fail
  | .userErr, [] => .err .user
  | _, _ => .err .type

/-- The primitives whose application can fail (be caught by a failure context). -/
def Prim.failable : Prim → Bool
  | .floorDiv | .ceilDiv | .quotient | .modulo => true
  | .lt | .le | .gt | .ge | .eq | .ne => true
  | .query | .index | .arrSet | .fail => true
  | .flt | .fle | .fgt | .fge | .ffloor | .fceil | .fround | .ftrunc | .fisFinite => true
  | _ => false

/-- A primitive that is not `failable` never fails, on any arguments. -/
theorem Prim.apply_ne_fail {p : Prim} (h : p.failable = false) (vs : List Value) :
    p.apply vs ≠ .fail := by
  have h1 : ∀ i, Res.ofInt i ≠ .fail := by intro i; unfold Res.ofInt; split <;> simp
  have h3 : ∀ v, toStrValue v ≠ .fail := by
    intro v; unfold toStrValue; split <;> (try split) <;> simp
  intro hf
  unfold Prim.apply at hf
  split at hf <;> first
    | (simp [Prim.failable] at h; done)
    | exact h1 _ hf
    | exact h3 _ hf
    | (split at hf <;> simp at hf)
    | simp at hf

end OpenVerse
