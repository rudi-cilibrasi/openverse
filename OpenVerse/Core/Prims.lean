/-
  OpenVerse — the meaning of each primitive operation.

  `Prim.apply` is total: any argument list of the wrong shape gives
  `err .type`, which the type checker rules out for elaborated programs but
  which the C runtime also reports, so that both implementations agree on
  every loaded program, typed or not.

  The two-int scalar operations are the seam with the C runtime: `runtime/src/arith.c`
  implements them and the QuickProof law `proofs/quickproof/arith` states the
  same conditions (see `docs/SEAMS.md`).
-/
import OpenVerse.Core.Syntax

namespace OpenVerse

/-- Floor division `⌊a / b⌋` for `b ≠ 0`. -/
def floorDivInt (a b : Int) : Int := Int.fdiv a b
/-- Ceiling division `⌈a / b⌉` for `b ≠ 0`. -/
def ceilDivInt (a b : Int) : Int := -Int.fdiv (-a) b

/-- Reduce before checking int64 bounds. A zero denominator denotes an
    unrepresentable result, hence overflow. Source rational operands have
    positive denominators; the guard in `ratArith` also defines raw Core. -/
def checkedRationalRes (p q : Int) : Res :=
  if 0 < q && Int64.inRange p && Int64.inRange q then
    .ok (.tup [.int p, .int q])
  else .err .overflow

def rationalRes (n d : Int) : Res :=
  let g : Int := Int.gcd n d
  let p := n / g
  let q := d / g
  let p := if q < 0 then -p else p
  let q := if q < 0 then -q else q
  checkedRationalRes p q

/-- Wide exact arithmetic, with bounds checked only after reduction.
    Nonpositive operand denominators are invalid rational representations;
    raw well-typed Core reports overflow rather than a type error. -/
def ratArith (op : Prim) (a b c d : Int) : Res :=
  if b ≤ 0 || d ≤ 0 then .err .overflow else
  match op with
  | .add => rationalRes (a * d + c * b) (b * d)
  | .sub => rationalRes (a * d - c * b) (b * d)
  | .mul => rationalRes (a * c) (b * d)
  | .quotient => if c = 0 then .fail else rationalRes (a * d) (b * c)
  | _ => .err .type

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
  | .int i => .ok (Value.ofArray ((intBytes i).map Value.char).toArray)
  | .char c => .ok (Value.ofArray #[.char c])
  | .float b => .ok (Value.ofString (VFloat.render b))
  | .arr vs => match asBytes vs.toList with
    | some _ => .ok (Value.ofArray vs)
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

/-- The meaning of each primitive. Select the operation first so a
    proof about one family does not expand other families' argument shapes. -/
def Prim.apply (op : Prim) (vs : List Value) : Res :=
  match op with
  | .add => match vs with
    | [.int a, .int b, .int c, .int d] => ratArith .add a b c d
    | [.int a, .int b] => Res.ofInt (a + b)
    | _ => .err .type
  | .sub => match vs with
    | [.int a, .int b, .int c, .int d] => ratArith .sub a b c d
    | [.int a, .int b] => Res.ofInt (a - b)
    | _ => .err .type
  | .mul => match vs with
    | [.int a, .int b, .int c, .int d] => ratArith .mul a b c d
    | [.int a, .int b] => Res.ofInt (a * b)
    | _ => .err .type
  | .quotient => match vs with
    | [.int a, .int b, .int c, .int d] => ratArith .quotient a b c d
    | [.int a, .int b] => if b = 0 then .fail else Res.ofInt (Int.ediv a b)
    | _ => .err .type
  | .neg => match vs with
    | [.int a] => Res.ofInt (-a)
    | _ => .err .type
  | .abs => match vs with
    | [.int a] => Res.ofInt (if a < 0 then -a else a)
    | _ => .err .type
  | .floorDiv => match vs with
    | [.int a, .int b] => if b = 0 then .fail else Res.ofInt (floorDivInt a b)
    | _ => .err .type
  | .ceilDiv => match vs with
    | [.int a, .int b] => if b = 0 then .fail else Res.ofInt (ceilDivInt a b)
    | _ => .err .type
  | .modulo => match vs with
    | [.int a, .int b] => if b = 0 then .fail else Res.ofInt (Int.emod a b)
    | _ => .err .type
  | .lt => match vs with
    | [.int a, .int b] => cmpRes (decide (a < b)) (Value.ofInt a)
    | [.char a, .char b] => cmpRes (decide (a < b)) (.char a)
    | _ => .err .type
  | .le => match vs with
    | [.int a, .int b] => cmpRes (decide (a ≤ b)) (Value.ofInt a)
    | [.char a, .char b] => cmpRes (decide (a ≤ b)) (.char a)
    | _ => .err .type
  | .gt => match vs with
    | [.int a, .int b] => cmpRes (decide (a > b)) (Value.ofInt a)
    | [.char a, .char b] => cmpRes (decide (a > b)) (.char a)
    | _ => .err .type
  | .ge => match vs with
    | [.int a, .int b] => cmpRes (decide (a ≥ b)) (Value.ofInt a)
    | [.char a, .char b] => cmpRes (decide (a ≥ b)) (.char a)
    | _ => .err .type
  -- Verse's equality of values (`Value.veq`): structural, but for the one
  -- empty value, which Verse Core holds four ways (Book of Verse ch. 2)
  | .eq => match vs with
    | [a, b] => cmpRes (Value.veq a b) a
    | _ => .err .type
  | .ne => match vs with
    | [a, b] => cmpRes (!Value.veq a b) a
    | _ => .err .type
  | .query => match vs with
    | [.logic b] => if b then .ok (.logic true) else .fail
    | [.none] => .fail
    | [.some v] => .ok v
    | _ => .err .type
  | .mkArr => .ok (Value.ofArray vs.toArray)
  | .mkTup => .ok (Value.ofTuple vs)
  | .mkSome => match vs with
    | [v] => .ok (.some v)
    | _ => .err .type
  | .concat => match vs with
    | [.arr xs, .arr ys] => .ok (Value.ofArray (xs ++ ys))
    | _ => .err .type
  | .flatten => match vs with
    | [.arr xss] => match flattenArrs xss.toList with
      | some vs => .ok (Value.ofArray vs.toArray)
      | none => .err .type
    | _ => .err .type
  | .range => match vs with
    | [.int a, .int b] => .ok (Value.ofArray (rangeVals a b).toArray)
    | _ => .err .type
  | .index => match vs with
    | [.arr xs, .int i] =>
      if 0 ≤ i then match xs[i.toNat]? with
        | some v => .ok v
        | none => .fail
      else .fail
    | _ => .err .type
  | .len => match vs with
    | [.arr xs] => .ok (Value.ofInt xs.size)
    | _ => .err .type
  | .arrSet => match vs with
    | [.arr xs, .int i, v] =>
      if 0 ≤ i ∧ i.toNat < xs.size then .ok (Value.ofArray (xs.setIfInBounds i.toNat v)) else .fail
    | _ => .err .type
  | .tupGet k => match vs with
    | [.tup vs] => match vs[k]? with
      | some v => .ok v
      | none => .err .type
    | _ => .err .type
  | .toStr => match vs with
    | [v] => toStrValue v
    | _ => .err .type
  | .fadd => match vs with
    | [.float a, .float b] => .ok (.float (VFloat.canon (VFloat.ofBits a + VFloat.ofBits b)))
    | _ => .err .type
  | .fsub => match vs with
    | [.float a, .float b] => .ok (.float (VFloat.canon (VFloat.ofBits a - VFloat.ofBits b)))
    | _ => .err .type
  | .fmul => match vs with
    | [.float a, .float b] => .ok (.float (VFloat.canon (VFloat.ofBits a * VFloat.ofBits b)))
    | _ => .err .type
  | .fdiv => match vs with
    | [.float a, .float b] => .ok (.float (VFloat.canon (VFloat.ofBits a / VFloat.ofBits b)))
    | _ => .err .type
  | .fneg => match vs with
    | [.float a] => .ok (.float (VFloat.canon (-VFloat.ofBits a)))
    | _ => .err .type
  | .fabs => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).abs))
    | _ => .err .type
  | .fmin => match vs with
    | [.float a, .float b] => .ok (.float (VFloat.fmin a b))
    | _ => .err .type
  | .fmax => match vs with
    | [.float a, .float b] => .ok (.float (VFloat.fmax a b))
    | _ => .err .type
  | .flt => match vs with
    | [.float a, .float b] => cmpRes (decide (VFloat.ofBits a < VFloat.ofBits b)) (.float a)
    -- (`NaN <= NaN` and `NaN >= NaN` succeed, as NaN equals itself, #132)
    | _ => .err .type
  | .fle => match vs with
    | [.float a, .float b] => cmpRes (a == b || decide (VFloat.ofBits a ≤ VFloat.ofBits b)) (.float a)
    | _ => .err .type
  | .fgt => match vs with
    | [.float a, .float b] => cmpRes (decide (VFloat.ofBits b < VFloat.ofBits a)) (.float a)
    | _ => .err .type
  | .fge => match vs with
    | [.float a, .float b] => cmpRes (a == b || decide (VFloat.ofBits b ≤ VFloat.ofBits a)) (.float a)
    | _ => .err .type
  | .fofInt => match vs with
    | [.int i] => .ok (.float (VFloat.canon (Float.ofInt i)))
    | _ => .err .type
  | .ffloor => match vs with
    | [.float a] => VFloat.toIntRes .floor a
    | _ => .err .type
  | .fceil => match vs with
    | [.float a] => VFloat.toIntRes .ceil a
    | _ => .err .type
  | .fround => match vs with
    | [.float a] => VFloat.toIntRes .round a
    | _ => .err .type
  | .ftrunc => match vs with
    | [.float a] => VFloat.toIntRes .trunc a
    | _ => .err .type
  | .fsqrt => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).sqrt))
    | _ => .err .type
  | .fexp => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).exp))
    | _ => .err .type
  | .fln => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).log))
    | _ => .err .type
  | .fsin => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).sin))
    | _ => .err .type
  | .fcos => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).cos))
    | _ => .err .type
  | .ftan => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).tan))
    | _ => .err .type
  | .fasin => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.clamp1 (VFloat.ofBits a)).asin))
    | _ => .err .type
  | .facos => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.clamp1 (VFloat.ofBits a)).acos))
    | _ => .err .type
  | .fatan => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).atan))
    | _ => .err .type
  | .fpow => match vs with
    | [.float a, .float b] => .ok (.float (VFloat.canon (Float.pow (VFloat.ofBits a) (VFloat.ofBits b))))
    | _ => .err .type
  | .fatan2 => match vs with
    | [.float a, .float b] => .ok (.float (VFloat.canon (Float.atan2 (VFloat.ofBits a) (VFloat.ofBits b))))
    | _ => .err .type
  | .fsinh => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).sinh))
    | _ => .err .type
  | .fcosh => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).cosh))
    | _ => .err .type
  | .ftanh => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).tanh))
    | _ => .err .type
  | .fasinh => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).asinh))
    | _ => .err .type
  | .facosh => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).acosh))
    | _ => .err .type
  | .fatanh => match vs with
    | [.float a] => .ok (.float (VFloat.canon (VFloat.ofBits a).atanh))
    | _ => .err .type
  | .fisFinite => match vs with
    | [.float a] => if VFloat.isFinite a then .ok (.float a) else .fail
    | _ => .err .type
  | .fofBits => match vs with
    | [.int i] => .ok (.float (VFloat.canon (VFloat.ofBits (UInt64.ofNat (i % (2 ^ 64 : Int)).toNat))))
    | _ => .err .type
  | .fail => match vs with
    | [] => .fail
    | _ => .err .type
  | .userErr => match vs with
    | [] => .err .user
    | _ => .err .type

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
  have hr : ∀ n d, rationalRes n d ≠ .fail := by
    have hc : ∀ p q, checkedRationalRes p q ≠ .fail := by
      intro p q; unfold checkedRationalRes; split <;> simp
    intro n d; unfold rationalRes; exact hc _ _
  cases p <;> simp [Prim.failable] at h
  all_goals
    simp only [Prim.apply, ratArith]
    repeat' split
    all_goals simp_all

end OpenVerse
