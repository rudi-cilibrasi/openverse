/-
  OpenVerse — the arithmetic seam between Lean and the C runtime.

  The C runtime implements Verse's `int` operations in `runtime/src/arith.c`.
  The QuickProof law `proofs/quickproof/arith` proves, under CompCert's C
  semantics, that each C function returns exactly what a reference formula
  says. Those formulas are written in C with C99's truncating `/` and `%`
  (C99 §6.5.5), which are Lean's `Int.tdiv` and `Int.tmod`.

  This file restates each formula in Lean, symbol for symbol (`cFloorDiv`,
  `cAddFits`, …), and proves that it is the Lean semantics of the
  primitive (`floorDiv_seam`, `add_seam`, …). The only step of the seam that
  no tool checks is that the C text of the law and the Lean text here are
  the same formula; they are printed side by side in `docs/SEAMS.md`.
-/
import OpenVerse.Core.Prims
namespace OpenVerse

/-- `a / b` and `a % b` in C99 (§6.5.5): truncation toward zero. -/
def cDiv (a b : Int) : Int := a.tdiv b
def cRem (a b : Int) : Int := a.tmod b

def cFloorDiv (a b : Int) : Int :=
  if cRem a b ≠ 0 ∧ ((cRem a b < 0) ≠ (b < 0)) then cDiv a b - 1 else cDiv a b
def cCeilDiv (a b : Int) : Int :=
  if cRem a b ≠ 0 ∧ ((cRem a b < 0) = (b < 0)) then cDiv a b + 1 else cDiv a b
def cQuotient (a b : Int) : Int :=
  if cRem a b < 0 then (if b > 0 then cDiv a b - 1 else cDiv a b + 1) else cDiv a b
def cModulo (a b : Int) : Int :=
  if cRem a b < 0 then (if b > 0 then cRem a b + b else cRem a b - b) else cRem a b

theorem tmod_sign (a b : Int) : (a.tmod b < 0) ↔ (a < 0 ∧ a.tmod b ≠ 0) := by
  constructor
  · intro h
    refine ⟨?_, by omega⟩
    rcases Int.lt_or_le a 0 with ha | ha
    · exact ha
    · have := Int.tmod_nonneg b ha; omega
  · rintro ⟨ha, hne⟩
    have := Int.tmod_nonneg b (show 0 ≤ -a by omega)
    rw [Int.neg_tmod] at this; omega

theorem dvd_iff_tmod (a b : Int) : b ∣ a ↔ a.tmod b = 0 :=
  ⟨Int.tmod_eq_zero_of_dvd, Int.dvd_of_tmod_eq_zero⟩

theorem quotient_seam (a b : Int) (hb : b ≠ 0) : Int.ediv a b = cQuotient a b := by
  have h := @Int.ediv_eq_tdiv a b
  simp only [HDiv.hDiv, Div.div] at h
  rw [h]
  unfold cQuotient cDiv cRem
  have hs := tmod_sign a b
  have hd := dvd_iff_tmod a b
  by_cases h1 : a.tmod b < 0
  · have ⟨ha, hne⟩ := hs.mp h1
    have hnd : ¬ b ∣ a := fun h => hne (hd.mp h)
    have : ¬ (0 ≤ a ∨ b ∣ a) := by omega
    simp only [this, ite_false, h1, ite_true]
    rcases Int.lt_or_gt_of_ne hb with hb' | hb'
    · simp [Int.sign_eq_neg_one_of_neg hb', show ¬ b > 0 by omega]
    · simp [Int.sign_eq_one_of_pos hb', hb']
  · simp only [h1, ite_false]
    have : 0 ≤ a ∨ b ∣ a := by
      rcases Int.lt_or_le a 0 with ha | ha
      · right; apply hd.mpr; have := hs; omega
      · left; exact ha
    simp [this]

theorem modulo_seam (a b : Int) (hb : b ≠ 0) : Int.emod a b = cModulo a b := by
  have h := @Int.emod_eq_tmod a b
  simp only [HMod.hMod, Mod.mod] at h
  rw [h]
  unfold cModulo cRem
  have hs := tmod_sign a b
  have hd := dvd_iff_tmod a b
  by_cases h1 : a.tmod b < 0
  · have ⟨ha, hne⟩ := hs.mp h1
    have hnd : ¬ b ∣ a := fun h => hne (hd.mp h)
    have : ¬ (0 ≤ a ∨ b ∣ a) := by omega
    simp only [this, ite_false, h1, ite_true]
    rcases Int.lt_or_gt_of_ne hb with hb' | hb'
    · simp [show ¬ b > 0 by omega]; omega
    · simp [hb']; omega
  · simp only [h1, ite_false]
    have : 0 ≤ a ∨ b ∣ a := by
      rcases Int.lt_or_le a 0 with ha | ha
      · right; apply hd.mpr; have := hs; omega
      · left; exact ha
    simp [this]

theorem floorDiv_seam (a b : Int) (hb : b ≠ 0) : floorDivInt a b = cFloorDiv a b := by
  unfold floorDivInt cFloorDiv cDiv cRem
  rw [Int.fdiv_eq_tdiv]
  have hs := tmod_sign a b
  have hd := dvd_iff_tmod a b
  by_cases hz : a.tmod b = 0
  · have : b ∣ a := hd.mpr hz
    simp [this, hz]
  · have hnd : ¬ b ∣ a := fun h => hz (hd.mp h)
    simp only [hnd, ite_false, ne_eq, hz, not_false_eq_true, true_and]
    rcases Int.lt_or_le a 0 with ha | ha <;> rcases Int.lt_or_gt_of_ne hb with hb' | hb'
    · have : a.tmod b < 0 := hs.mpr ⟨ha, hz⟩
      simp [this, hb', show ¬ 0 ≤ a by omega, show ¬ 0 ≤ b by omega, Int.sign_eq_neg_one_of_neg hb']
    · have : a.tmod b < 0 := hs.mpr ⟨ha, hz⟩
      simp [this, show ¬ b < 0 by omega, show ¬ 0 ≤ a by omega, show 0 ≤ b by omega,
        Int.sign_eq_one_of_pos hb']
    · have : ¬ a.tmod b < 0 := fun h => by have := (hs.mp h).1; omega
      simp [this, hb', ha, show ¬ 0 ≤ b by omega]
    · have : ¬ a.tmod b < 0 := fun h => by have := (hs.mp h).1; omega
      simp [this, show ¬ b < 0 by omega, ha, show 0 ≤ b by omega]

theorem floorDiv_seam' (a b : Int) (hb : b ≠ 0) : Int.fdiv a b = cFloorDiv a b :=
  floorDiv_seam a b hb

theorem ceilDiv_seam (a b : Int) (hb : b ≠ 0) : ceilDivInt a b = cCeilDiv a b := by
  unfold ceilDivInt
  rw [floorDiv_seam' (-a) b hb]
  unfold cFloorDiv cCeilDiv cDiv cRem
  simp only [Int.neg_tdiv, Int.neg_tmod]
  by_cases hz : a.tmod b = 0
  · simp [hz]
  · have hnz : -a.tmod b ≠ 0 := by omega
    by_cases hr : a.tmod b < 0
    · have hr' : ¬ (-a.tmod b < 0) := by omega
      by_cases hb' : b < 0
      · simp [hz, hr, hb', show a.tmod b ≤ 0 by omega]; omega
      · simp [hz, hr, hb']; omega
    · have hr' : -a.tmod b < 0 := by omega
      by_cases hb' : b < 0
      · simp [hz, hr, hb']; omega
      · simp [hz, hr, hb', show 0 < a.tmod b by omega]; omega

/-! ### Overflow conditions, as the C law writes them -/

def cAddFits (a b : Int) : Bool := if 0 ≤ b then decide (a ≤ Int64.maxV - b) else decide (Int64.minV - b ≤ a)
def cSubFits (a b : Int) : Bool := if 0 ≤ b then decide (Int64.minV + b ≤ a) else decide (a ≤ Int64.maxV + b)
def cNegFits (a : Int) : Bool := a != Int64.minV
def cMulFits (a b : Int) : Bool :=
  if b = 0 then true
  else if b = -1 then a != Int64.minV
  else if 0 < b then decide (cDiv Int64.minV b ≤ a) && decide (a ≤ cDiv Int64.maxV b)
  else decide (cDiv Int64.maxV b ≤ a) && decide (a ≤ cDiv Int64.minV b)

abbrev InR (a : Int) : Prop := Int64.minV ≤ a ∧ a ≤ Int64.maxV

theorem inRange_iff (i : Int) : Int64.inRange i = true ↔ InR i := by
  simp [Int64.inRange]

theorem add_seam {a b : Int} (ha : InR a) (hb : InR b) : Int64.inRange (a + b) = cAddFits a b := by
  obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
  rw [Bool.eq_iff_iff]
  by_cases h : 0 ≤ b <;>
    simp only [Int64.inRange, cAddFits, h, ite_true, ite_false, Bool.and_eq_true, decide_eq_true_eq] <;>
    simp only [Int64.minV, Int64.maxV] at * <;> omega

theorem sub_seam {a b : Int} (ha : InR a) (hb : InR b) : Int64.inRange (a - b) = cSubFits a b := by
  obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
  rw [Bool.eq_iff_iff]
  by_cases h : 0 ≤ b <;>
    simp only [Int64.inRange, cSubFits, h, ite_true, ite_false, Bool.and_eq_true, decide_eq_true_eq] <;>
    simp only [Int64.minV, Int64.maxV] at * <;> omega

theorem neg_seam {a : Int} (ha : InR a) : Int64.inRange (-a) = cNegFits a := by
  obtain ⟨ha1, ha2⟩ := ha
  rw [Bool.eq_iff_iff]
  simp only [Int64.inRange, cNegFits, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  simp only [Int64.minV, Int64.maxV] at *; omega

theorem mul_seam {a b : Int} (ha : InR a) (_hb : InR b) : Int64.inRange (a * b) = cMulFits a b := by
  apply Bool.eq_iff_iff.mpr
  rw [inRange_iff]
  unfold cMulFits cDiv
  have hmin : Int64.minV = -9223372036854775808 := rfl
  have hmax : Int64.maxV = 9223372036854775807 := rfl
  by_cases h0 : b = 0
  · subst h0; simp [InR, hmin, hmax]
  by_cases h1 : b = -1
  · subst h1; simp [InR, hmin, hmax] at ha ⊢; omega
  simp only [h0, h1, ite_false]
  by_cases hp : 0 < b
  · simp only [hp, ite_true, Bool.and_eq_true, decide_eq_true_eq]
    -- MIN / b (truncating) = -((-MIN) / b), and (-MIN) / b is Euclidean (nonnegative dividend)
    have e1 : Int.tdiv Int64.minV b = -((-Int64.minV) / b) := by
      rw [show Int64.minV = -(-Int64.minV) by omega, Int.neg_tdiv, Int.neg_neg,
        Int.tdiv_eq_ediv_of_nonneg (by rw [hmin]; decide)]
    have e2 : Int.tdiv Int64.maxV b = Int64.maxV / b :=
      Int.tdiv_eq_ediv_of_nonneg (by rw [hmax]; decide)
    rw [e1, e2]
    have k1 : -a ≤ (-Int64.minV) / b ↔ (-a) * b ≤ -Int64.minV := Int.le_ediv_iff_mul_le hp
    have k2 : a ≤ Int64.maxV / b ↔ a * b ≤ Int64.maxV := Int.le_ediv_iff_mul_le hp
    rw [Int.neg_mul] at k1
    constructor
    · rintro ⟨l, r⟩; exact ⟨by omega, k2.mpr r⟩
    · rintro ⟨l, r⟩; exact ⟨by omega, k2.mp r⟩
  · have hn : b < 0 := by omega
    simp only [hp, ite_false, Bool.and_eq_true, decide_eq_true_eq]
    have hnb : 0 < -b := by omega
    have e1 : Int.tdiv Int64.maxV b = -(Int64.maxV / (-b)) := by
      rw [show b = -(-b) by omega, Int.tdiv_neg, Int.neg_neg,
        Int.tdiv_eq_ediv_of_nonneg (by rw [hmax]; decide)]
    have e2 : Int.tdiv Int64.minV b = (-Int64.minV) / (-b) := by
      rw [← Int.neg_tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by rw [hmin]; decide)]
    rw [e1, e2]
    have k1 : -a ≤ Int64.maxV / (-b) ↔ (-a) * (-b) ≤ Int64.maxV := Int.le_ediv_iff_mul_le hnb
    have k2 : a ≤ (-Int64.minV) / (-b) ↔ a * (-b) ≤ -Int64.minV := Int.le_ediv_iff_mul_le hnb
    rw [Int.neg_mul_neg] at k1
    rw [Int.mul_neg] at k2
    constructor
    · rintro ⟨l, r⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨l, r⟩; exact ⟨by omega, by omega⟩

/-! ### The primitives, in the terms of the C law -/

theorem apply_add {a b : Int} (ha : InR a) (hb : InR b) :
    Prim.apply .add [.int a, .int b] = if cAddFits a b then .ok (.int (a + b)) else .err .overflow := by
  simp only [Prim.apply, Res.ofInt, Value.ofInt, add_seam ha hb]

theorem apply_sub {a b : Int} (ha : InR a) (hb : InR b) :
    Prim.apply .sub [.int a, .int b] = if cSubFits a b then .ok (.int (a - b)) else .err .overflow := by
  simp only [Prim.apply, Res.ofInt, Value.ofInt, sub_seam ha hb]

theorem apply_mul {a b : Int} (ha : InR a) (hb : InR b) :
    Prim.apply .mul [.int a, .int b] = if cMulFits a b then .ok (.int (a * b)) else .err .overflow := by
  simp only [Prim.apply, Res.ofInt, Value.ofInt, mul_seam ha hb]

theorem apply_neg {a : Int} (ha : InR a) :
    Prim.apply .neg [.int a] = if cNegFits a then .ok (.int (-a)) else .err .overflow := by
  simp only [Prim.apply, Res.ofInt, Value.ofInt, neg_seam ha]

theorem apply_floorDiv {a b : Int} (hb : b ≠ 0) :
    Prim.apply .floorDiv [.int a, .int b] = Res.ofInt (cFloorDiv a b) := by
  simp [Prim.apply, hb, floorDiv_seam a b hb]

theorem apply_ceilDiv {a b : Int} (hb : b ≠ 0) :
    Prim.apply .ceilDiv [.int a, .int b] = Res.ofInt (cCeilDiv a b) := by
  simp [Prim.apply, hb, ceilDiv_seam a b hb]

theorem apply_quotient {a b : Int} (hb : b ≠ 0) :
    Prim.apply .quotient [.int a, .int b] = Res.ofInt (cQuotient a b) := by
  simp [Prim.apply, hb, quotient_seam a b hb]

theorem apply_modulo {a b : Int} (hb : b ≠ 0) :
    Prim.apply .modulo [.int a, .int b] = Res.ofInt (cModulo a b) := by
  simp [Prim.apply, hb, modulo_seam a b hb]

/-- Division by zero is a Verse failure (not an error) for all four. -/
theorem apply_div_zero (a : Int) :
    Prim.apply .floorDiv [.int a, .int 0] = .fail ∧ Prim.apply .ceilDiv [.int a, .int 0] = .fail ∧
    Prim.apply .quotient [.int a, .int 0] = .fail ∧ Prim.apply .modulo [.int a, .int 0] = .fail := by
  simp [Prim.apply]

/-- The one pair where C's `/` and `%` are undefined, `(INT64_MIN, -1)`: floor,
    ceiling and Euclidean quotient overflow (the exact result is 2^63); the
    Euclidean remainder is 0. -/
theorem apply_min_neg_one :
    Prim.apply .floorDiv [.int Int64.minV, .int (-1)] = .err .overflow ∧
    Prim.apply .ceilDiv [.int Int64.minV, .int (-1)] = .err .overflow ∧
    Prim.apply .quotient [.int Int64.minV, .int (-1)] = .err .overflow ∧
    Prim.apply .modulo [.int Int64.minV, .int (-1)] = .ok (.int 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end OpenVerse
