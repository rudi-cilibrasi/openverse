/-
  OpenVerse Core — floats (#127).

  A Verse `float` is an IEEE 64-bit float with one NaN, equal to itself, and
  no negative zero (Book of Verse ch. 2). A float value holds the bits of a
  canonical float (`canon`), so equality of values is Verse's equality.
  Arithmetic is IEEE (Lean's `Float`, as C's `double`); the conversions to
  `int` and the decimal rendering are computed exactly from the bits, here
  and in the C runtime alike.
-/
namespace OpenVerse

namespace VFloat

/-- The one NaN. -/
def nanBits : UInt64 := 0x7FF8000000000000

/-- The canonical bits of a float: one NaN, and `+0` for `-0`. -/
def canon (f : Float) : UInt64 :=
  if f.isNaN then nanBits else if f == 0.0 then 0 else f.toBits

def ofBits (b : UInt64) : Float := Float.ofBits b

/-- The parts of finite nonzero bits: sign, mantissa `m` and exponent `e`,
    the value being `±m · 2^e`. -/
def parts (b : UInt64) : Bool × Nat × Int :=
  let n : Nat := b.toNat
  let neg := n ≥ 2 ^ 63
  let ef : Nat := (n / 2 ^ 52) % 2048
  let mf : Nat := n % 2 ^ 52
  if ef == 0 then (neg, mf, -1074) else (neg, mf + 2 ^ 52, (ef : Int) - 1075)

def isFinite (b : UInt64) : Bool := (b.toNat / 2 ^ 52) % 2048 != 2047

/-- `⌊m · 2^e⌋` and whether the value was an integer, for `m ≥ 0`. -/
def floorParts (m : Nat) (e : Int) : Nat × Bool :=
  if e ≥ 0 then (m * 2 ^ e.toNat, true)
  else
    let s := (-e).toNat
    (m / 2 ^ s, m % 2 ^ s == 0)

/-- How a float becomes an int (`Floor`, `Ceil`, `Round` with ties to
    even, `Int` towards zero); none for NaN, an infinity or a result out of
    the int range. -/
inductive Rounding where
  | floor | ceil | round | trunc
  deriving Repr, DecidableEq, Inhabited

def toInt? (r : Rounding) (b : UInt64) : Option Int :=
  if !isFinite b then none else
  let (neg, m, e) := parts b
  let (q, exact) := floorParts m e
  -- the magnitude rounded, by the sign
  let up : Bool := match r with
    | .trunc => false
    | .floor => neg && !exact
    | .ceil => !neg && !exact
    | .round =>
      if exact || e ≥ 0 then false
      else
        let s := (-e).toNat
        let rem := m % 2 ^ s
        let half := 2 ^ (s - 1)
        rem > half || (rem == half && q % 2 == 1)
  let mag : Nat := if up then q + 1 else q
  let i : Int := if neg then -(mag : Int) else mag
  if decide (-(2 ^ 63 : Int) ≤ i) && decide (i < 2 ^ 63) then some i else none

/-- `Min` and `Max` (Book of Verse ch. 2): NaN when either is NaN. -/
def fmin (a b : UInt64) : UInt64 :=
  if a == nanBits || b == nanBits then nanBits
  else if ofBits b < ofBits a then b else a

/-- The argument of `ArcSin` and `ArcCos`, clamped to [-1, 1] (NaN stays). -/
def clamp1 (x : Float) : Float := if x < -1.0 then -1.0 else if 1.0 < x then 1.0 else x

def fmax (a b : UInt64) : UInt64 :=
  if a == nanBits || b == nanBits then nanBits
  else if ofBits a < ofBits b then b else a

/-! ### Rendering: the shortest decimal that reads back as the float -/

/-- `n` rounded to the nearest integer, ties to even, of `a / d` (`d > 0`). -/
def divRound (a d : Nat) : Nat :=
  let q := a / d
  let r := a % d
  if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q

/-- The decimal digits of `n`. -/
def digits (n : Nat) : String := toString n

/-- The float `m · 2^e` (`m > 0`) as `(D, q)` with `D · 10^q` the shortest
    decimal that rounds to it (round half to even), the closest of the
    shortest. -/
def shortest (m : Nat) (e : Int) : Nat × Int := Id.run do
  -- the value and its rounding interval, all scaled by 2^(2 - e) (exact):
  -- v = m · 4, the gap up 2, the gap down 2 (or 1 below a power of two)
  let scale : Int := 2 - e
  let v4 : Nat := m * 4
  let lowPow := m == 2 ^ 52 && e > -1074
  let lo : Nat := v4 - (if lowPow then 1 else 2)
  let hi : Nat := v4 + 2
  let inclusive := m % 2 == 0
  -- a decimal `D · 10^q` (as a rational `num / den` in the same scale)
  let scaled (D : Nat) (q : Int) : Nat × Nat :=
    -- D · 10^q · 2^scale
    let num1 : Nat := D * (if q ≥ 0 then 10 ^ q.toNat else 1)
    let den1 : Nat := if q ≥ 0 then 1 else 10 ^ (-q).toNat
    let num2 : Nat := num1 * (if scale ≥ 0 then 2 ^ scale.toNat else 1)
    let den2 : Nat := den1 * (if scale ≥ 0 then 1 else 2 ^ (-scale).toNat)
    (num2, den2)
  let inside (D : Nat) (q : Int) : Bool :=
    let (n, d) := scaled D q
    if inclusive then lo * d ≤ n && n ≤ hi * d else lo * d < n && n < hi * d
  -- the value m · 2^e as a rational a / b
  let a : Nat := m * (if e ≥ 0 then 2 ^ e.toNat else 1)
  let b : Nat := if e ≥ 0 then 1 else 2 ^ (-e).toNat
  -- k = ⌊log10 (a / b)⌋
  let mut k : Int := 0
  -- (an estimate from the binary exponent, then corrected)
  let bits : Int := (Nat.log2 m : Int) + e
  k := (bits * 30103) / 100000
  for _ in [0:4] do
    let p10 (j : Int) : Nat × Nat := if j ≥ 0 then (10 ^ j.toNat, 1) else (1, 10 ^ (-j).toNat)
    let (pn, pd) := p10 k
    if a * pd < pn * b then k := k - 1
    else
      let (qn, qd) := p10 (k + 1)
      if a * qd ≥ qn * b then k := k + 1
  for p in [1:18] do
    let q : Int := k - (p : Int) + 1
    -- D = a / b / 10^q, rounded half to even
    let (num, den) : Nat × Nat :=
      if q ≥ 0 then (a, b * 10 ^ q.toNat) else (a * 10 ^ (-q).toNat, b)
    let D := divRound num den
    if inside D q then return (D, q)
    -- the neighbour on the other side of the value
    let below := D * den < num
    let D' := if below then D + 1 else D - 1
    if D' > 0 && inside D' q then return (D', q)
  -- (17 digits always suffice)
  let q : Int := k - 16
  let (num, den) : Nat × Nat :=
    if q ≥ 0 then (a, b * 10 ^ q.toNat) else (a * 10 ^ (-q).toNat, b)
  return (divRound num den, q)

/-- Python's `repr` layout of the digits `ds` (no trailing zeros) with the
    point after `decpt` of them. -/
def layout (ds : String) (decpt : Int) : String :=
  let n : Int := ds.length
  if decpt ≤ -4 || decpt > 16 then
    let x := decpt - 1
    let mant := if ds.length > 1 then s!"{ds.take 1}.{ds.drop 1}" else ds
    let es := toString x.natAbs
    let es := if es.length < 2 then "0" ++ es else es
    s!"{mant}e{if x < 0 then "-" else "+"}{es}"
  else if decpt ≤ 0 then
    "0." ++ String.ofList (List.replicate (-decpt).toNat '0') ++ ds
  else if decpt ≥ n then
    ds ++ String.ofList (List.replicate (decpt - n).toNat '0') ++ ".0"
  else
    s!"{ds.take decpt.toNat}.{ds.drop decpt.toNat}"

/-- The shortest decimal that reads back as a float, laid out as Python's
    `repr` does; `NaN`, `Inf`, `-Inf`. The compiler's messages name float
    literals so; `ToString` is `fixed6`. -/
def render (b : UInt64) : String :=
  if b == nanBits then "NaN"
  else if !isFinite b then (if b.toNat ≥ 2 ^ 63 then "-Inf" else "Inf")
  else if b == 0 then "0.0"
  else
    let (neg, m, e) := parts b
    let (D, q) := shortest m e
    -- strip the trailing zeros
    let rec strip (D : Nat) (q : Int) (fuel : Nat) : Nat × Int :=
      match fuel with
      | 0 => (D, q)
      | f + 1 => if D % 10 == 0 && D > 0 then strip (D / 10) (q + 1) f else (D, q)
    let (D, q) := strip D q 20
    let ds := digits D
    let decpt : Int := ds.length + q
    (if neg then "-" else "") ++ layout ds decpt

/-! ### `ToString`: fixed point with six digits after the point -/

/-- `ToString` of a float (the Book's API, `ToString(Val:float)`: "Fixed
    point with exactly six digits after the decimal point, always"): `NaN`,
    `Inf`, `-Inf`, or the float's exact value rounded to a multiple of
    10^-6, a tie to the even last digit, with every digit before the point
    and a `-` whenever the float is negative, also when every digit is zero.
    This is C's `%.6f` in the default rounding mode. -/
def fixed6 (b : UInt64) : String :=
  if b == nanBits then "NaN"
  else if !isFinite b then (if b.toNat ≥ 2 ^ 63 then "-Inf" else "Inf")
  else
    -- (zero's parts are `(false, 0, -1074)`)
    let (neg, m, e) := parts b
    -- the magnitude in millionths: m · 2^e · 10^6, rounded half to even
    let n : Nat :=
      if e ≥ 0 then m * 2 ^ e.toNat * 10 ^ 6 else divRound (m * 10 ^ 6) (2 ^ (-e).toNat)
    let ds := (toString n).toList
    -- (at least one digit before the point)
    let ds := List.replicate (7 - ds.length) '0' ++ ds
    let k := ds.length - 6
    (if neg then "-" else "") ++ String.ofList (ds.take k) ++ "." ++ String.ofList (ds.drop k)

end VFloat

end OpenVerse
