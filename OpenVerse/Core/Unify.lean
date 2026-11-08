/-
  OpenVerse — first-order unification of Verse Core types (#209).

  `unify eqs` is Robinson's algorithm on a list of equations between types
  (`VTy`, whose variables are `var j`). It is sound (its result makes both
  sides of every equation equal), most general (every unifier factors
  through it: `(σ j).subst R = R j`), and complete (it finds a unifier
  whenever there is one). The refinement by pins that relate type
  arguments to each other (a class that repeats its parent's type
  arguments, `dup(t) := class(pair(t, t))`) is to be such a most general
  unifier (#171).

  `unify` composes its result as a chain of substitutions, each applied
  lazily: fine for the few short equations of pins, though a long chain
  of eliminations can make the types it gives large.
-/
import OpenVerse.Core.Subst

namespace OpenVerse

/-! ### Sizes, variables, substitution of one variable -/

mutual
/-- The number of constructors in a type. -/
def VTy.usize : VTy → Nat
  | .arr t | .opt t => VTy.usize t + 1
  | .tup ts | .ref _ ts => VTy.usizeL ts + 1
  | _ => 1
def VTy.usizeL : List VTy → Nat
  | [] => 0
  | t :: ts => VTy.usize t + VTy.usizeL ts
end

theorem VTy.usize_pos : ∀ t : VTy, 0 < t.usize
  | .int | .logic | .char | .float | .var _ => by simp [VTy.usize]
  | .arr _ | .opt _ | .tup _ | .ref _ _ => by simp [VTy.usize]

mutual
/-- One more than the largest type variable of `t` (none: 0). -/
def VTy.nvars : VTy → Nat
  | .var j => j + 1
  | .arr t | .opt t => VTy.nvars t
  | .tup ts | .ref _ ts => VTy.nvarsL ts
  | _ => 0
def VTy.nvarsL : List VTy → Nat
  | [] => 0
  | t :: ts => max (VTy.nvars t) (VTy.nvarsL ts)
end

/-- A list of equations between types. -/
abbrev Eqs := List (VTy × VTy)

/-- The total size of the equations. -/
def Eqs.size : Eqs → Nat
  | [] => 0
  | (a, b) :: r => a.usize + b.usize + Eqs.size r

/-- Whether type variable `j` occurs in the equations. -/
def Eqs.has (j : Nat) : Eqs → Bool
  | [] => false
  | (a, b) :: r => a.hasVar j || b.hasVar j || Eqs.has j r

/-- One more than the largest variable of the equations. -/
def Eqs.nvars : Eqs → Nat
  | [] => 0
  | (a, b) :: r => max (max a.nvars b.nvars) (Eqs.nvars r)

/-- The number of variables the equations mention. -/
def Eqs.count (eqs : Eqs) : Nat := (List.range eqs.nvars).countP (Eqs.has · eqs)

/-- Both sides of every equation under `σ`. -/
def Eqs.subst (σ : Nat → VTy) (eqs : Eqs) : Eqs := eqs.map fun p => (p.1.subst σ, p.2.subst σ)

/-- `σ` makes both sides of every equation equal. -/
def Eqs.Unifies (σ : Nat → VTy) (eqs : Eqs) : Prop := ∀ p ∈ eqs, p.1.subst σ = p.2.subst σ

/-- `t` for variable `x`, every other variable kept. -/
def Unify.single (x : Nat) (t : VTy) : Nat → VTy := fun j => if j = x then t else .var j

/-! ### Variables and bounds -/

mutual
theorem VTy.lt_nvars : ∀ (t : VTy) (j : Nat), t.hasVar j = true → j < t.nvars
  | .int, _, h | .logic, _, h | .char, _, h | .float, _, h => by simp [VTy.hasVar] at h
  | .var i, j, h => by simp [VTy.hasVar] at h; subst h; simp [VTy.nvars]
  | .arr t, j, h | .opt t, j, h => by
    simp only [VTy.hasVar] at h; simpa [VTy.nvars] using VTy.lt_nvars t j h
  | .tup ts, j, h | .ref _ ts, j, h => by
    simp only [VTy.hasVar] at h; simpa [VTy.nvars] using VTy.lt_nvarsL ts j h
theorem VTy.lt_nvarsL : ∀ (ts : List VTy) (j : Nat), VTy.hasVarL j ts = true → j < VTy.nvarsL ts
  | [], _, h => by simp [VTy.hasVarL] at h
  | t :: ts, j, h => by
    simp only [VTy.hasVarL, Bool.or_eq_true] at h
    simp only [VTy.nvarsL]
    rcases h with h | h
    · exact Nat.lt_of_lt_of_le (VTy.lt_nvars t j h) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (VTy.lt_nvarsL ts j h) (Nat.le_max_right _ _)
end

mutual
theorem VTy.nvars_le : ∀ (t : VTy) (n : Nat), (∀ j, t.hasVar j = true → j < n) → t.nvars ≤ n
  | .int, _, _ | .logic, _, _ | .char, _, _ | .float, _, _ => by simp [VTy.nvars]
  | .var i, n, h => by simp only [VTy.nvars]; exact h i (by simp [VTy.hasVar])
  | .arr t, n, h | .opt t, n, h => by
    simpa [VTy.nvars] using VTy.nvars_le t n (fun j hj => h j (by simpa [VTy.hasVar] using hj))
  | .tup ts, n, h | .ref _ ts, n, h => by
    simpa [VTy.nvars] using VTy.nvarsL_le ts n (fun j hj => h j (by simpa [VTy.hasVar] using hj))
theorem VTy.nvarsL_le : ∀ (ts : List VTy) (n : Nat), (∀ j, VTy.hasVarL j ts = true → j < n) → VTy.nvarsL ts ≤ n
  | [], _, _ => by simp [VTy.nvarsL]
  | t :: ts, n, h => by
    simp only [VTy.nvarsL]
    exact Nat.max_le.mpr ⟨VTy.nvars_le t n (fun j hj => h j (by simp [VTy.hasVarL, hj])),
      VTy.nvarsL_le ts n (fun j hj => h j (by simp [VTy.hasVarL, hj]))⟩
end

theorem Eqs.lt_nvars : ∀ (eqs : Eqs) (j : Nat), eqs.has j = true → j < eqs.nvars
  | [], _, h => by simp [Eqs.has] at h
  | (a, b) :: r, j, h => by
    simp only [Eqs.has, Bool.or_eq_true] at h
    simp only [Eqs.nvars]
    rcases h with (h | h) | h
    · exact Nat.lt_of_lt_of_le (VTy.lt_nvars a j h)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    · exact Nat.lt_of_lt_of_le (VTy.lt_nvars b j h)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
    · exact Nat.lt_of_lt_of_le (Eqs.lt_nvars r j h) (Nat.le_max_right _ _)

theorem Eqs.nvars_le : ∀ (eqs : Eqs) (n : Nat), (∀ j, eqs.has j = true → j < n) → eqs.nvars ≤ n
  | [], _, _ => by simp [Eqs.nvars]
  | (a, b) :: r, n, h => by
    simp only [Eqs.nvars]
    refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨?_, ?_⟩, ?_⟩
    · exact VTy.nvars_le a n (fun j hj => h j (by simp [Eqs.has, hj]))
    · exact VTy.nvars_le b n (fun j hj => h j (by simp [Eqs.has, hj]))
    · exact Eqs.nvars_le r n (fun j hj => h j (by simp [Eqs.has, hj]))

/-! ### Counting -/

/-- Counting over a longer range adds nothing a predicate does not hold of. -/
theorem Unify.countP_range_extend (p : Nat → Bool) {m n : Nat} (hmn : m ≤ n) (hp : ∀ j, p j = true → j < m) :
    (List.range n).countP p = (List.range m).countP p := by
  induction n with
  | zero => simp [Nat.le_zero.mp hmn]
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hmn with h | h
    · rw [List.range_succ, List.countP_append, ih (Nat.le_of_lt_succ h)]
      have : p k = false := by
        cases hk : p k
        · rfl
        · exact absurd (hp k hk) (by omega)
      simp [this]
    · rw [h]

/-- A predicate that implies another, and fails where the other holds, counts fewer. -/
theorem Unify.countP_lt_of_imp {α} (p q : α → Bool) : ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
    ∀ y ∈ l, q y = true → p y = false → l.countP p < l.countP q
  | [], _, y, hy, _, _ => by simp at hy
  | x :: xs, himp, y, hy, hq, hp => by
    have hrest := fun z (hz : z ∈ xs) => himp z (List.mem_cons_of_mem _ hz)
    have hle : xs.countP p ≤ xs.countP q := List.countP_mono_left hrest
    rcases List.mem_cons.mp hy with rfl | hy'
    · simp [hq, hp]; omega
    · have ih := Unify.countP_lt_of_imp p q xs hrest y hy' hq hp
      simp only [List.countP_cons]
      have hx : (if p x = true then 1 else 0) ≤ (if q x = true then 1 else 0) := by
        by_cases hpx : p x = true
        · simp [hpx, himp x (List.mem_cons_self) hpx]
        · simp [hpx]
      omega

/-! ### Variables of a substituted type -/

mutual
theorem VTy.hasVar_subst {σ : Nat → VTy} {j : Nat} :
    ∀ u : VTy, (u.subst σ).hasVar j = true → ∃ k, u.hasVar k = true ∧ (σ k).hasVar j = true
  | .int, h | .logic, h | .char, h | .float, h => by simp [VTy.hasVar] at h
  | .var k, h => ⟨k, by simp [VTy.hasVar], by simpa using h⟩
  | .arr u, h | .opt u, h => by
    obtain ⟨k, hk, hj⟩ := VTy.hasVar_subst u (by simpa [VTy.hasVar] using h)
    exact ⟨k, by simpa [VTy.hasVar] using hk, hj⟩
  | .tup us, h => by
    obtain ⟨k, hk, hj⟩ := VTy.hasVarL_subst us (by simpa [VTy.hasVar] using h)
    exact ⟨k, by simpa [VTy.hasVar] using hk, hj⟩
  | .ref _ us, h => by
    obtain ⟨k, hk, hj⟩ := VTy.hasVarL_subst us (by simpa [VTy.hasVar, VTy.subst, VTy.substL_eq_map] using h)
    exact ⟨k, by simpa [VTy.hasVar] using hk, hj⟩
theorem VTy.hasVarL_subst {σ : Nat → VTy} {j : Nat} :
    ∀ us : List VTy, VTy.hasVarL j (us.map (VTy.subst σ)) = true →
      ∃ k, VTy.hasVarL k us = true ∧ (σ k).hasVar j = true
  | [], h => by simp [VTy.hasVarL] at h
  | u :: us, h => by
    simp only [List.map_cons, VTy.hasVarL, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨k, hk, hj⟩ := VTy.hasVar_subst u h
      exact ⟨k, by simp [VTy.hasVarL, hk], hj⟩
    · obtain ⟨k, hk, hj⟩ := VTy.hasVarL_subst us h
      exact ⟨k, by simp [VTy.hasVarL, hk], hj⟩
end

theorem Eqs.has_subst {σ : Nat → VTy} {j : Nat} :
    ∀ eqs : Eqs, (eqs.subst σ).has j = true → ∃ k, eqs.has k = true ∧ (σ k).hasVar j = true
  | [], h => by simp [Eqs.subst, Eqs.has] at h
  | (a, b) :: r, h => by
    simp only [Eqs.subst, List.map_cons, Eqs.has, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · obtain ⟨k, hk, hj⟩ := VTy.hasVar_subst a h; exact ⟨k, by simp [Eqs.has, hk], hj⟩
    · obtain ⟨k, hk, hj⟩ := VTy.hasVar_subst b h; exact ⟨k, by simp [Eqs.has, hk], hj⟩
    · obtain ⟨k, hk, hj⟩ := Eqs.has_subst r h; exact ⟨k, by simp [Eqs.has, hk], hj⟩

/-! ### The measure -/

/-- Equations whose variables are among another's count no more. -/
theorem Eqs.count_le {new old : Eqs} (h : ∀ j, new.has j = true → old.has j = true) :
    new.count ≤ old.count := by
  unfold Eqs.count
  have hn : new.nvars ≤ old.nvars := Eqs.nvars_le new old.nvars fun j hj => Eqs.lt_nvars old j (h j hj)
  rw [← Unify.countP_range_extend (Eqs.has · new) hn (fun j hj => Eqs.lt_nvars new j hj)]
  exact List.countP_mono_left fun j _ hj => h j hj

/-- ... and fewer when one of the other's is not among them. -/
theorem Eqs.count_lt {new old : Eqs} (h : ∀ j, new.has j = true → old.has j = true) {x : Nat}
    (hx : old.has x = true) (hnx : new.has x = false) : new.count < old.count := by
  unfold Eqs.count
  have hn : new.nvars ≤ old.nvars := Eqs.nvars_le new old.nvars fun j hj => Eqs.lt_nvars old j (h j hj)
  rw [← Unify.countP_range_extend (Eqs.has · new) hn (fun j hj => Eqs.lt_nvars new j hj)]
  exact Unify.countP_lt_of_imp _ _ _ (fun j _ hj => h j hj) x
    (List.mem_range.mpr (Eqs.lt_nvars old x hx)) hx hnx

/-- Eliminating a variable `x` for a type `t` without it: the variables of
    the rest, under the substitution, are among the equations', but `x`. -/
theorem Eqs.count_elim {x : Nat} {t : VTy} {old r : Eqs} (htx : t.hasVar x = false)
    (hx : old.has x = true) (ht : ∀ j, t.hasVar j = true → old.has j = true)
    (hr : ∀ j, r.has j = true → old.has j = true) : (r.subst (Unify.single x t)).count < old.count := by
  refine Eqs.count_lt (x := x) ?_ hx ?_
  · intro j hj
    obtain ⟨k, hk, hkj⟩ := Eqs.has_subst r hj
    by_cases hkx : k = x
    · subst hkx; simp only [Unify.single, ite_true] at hkj; exact ht j hkj
    · simp only [Unify.single, hkx, ite_false, VTy.hasVar, beq_iff_eq] at hkj; subst hkj; exact hr k hk
  · cases h : (r.subst (Unify.single x t)).has x
    · rfl
    · obtain ⟨k, _, hkx⟩ := Eqs.has_subst r h
      by_cases hk : k = x
      · subst hk; simp [Unify.single, htx] at hkx
      · simp [Unify.single, hk, VTy.hasVar] at hkx

/-! ### Sizes of decompositions -/

theorem Eqs.size_append : ∀ (a b : Eqs), Eqs.size (a ++ b) = a.size + b.size
  | [], b => by simp [Eqs.size]
  | (x, y) :: a, b => by simp [Eqs.size, Eqs.size_append a b]; omega

theorem Eqs.size_zip : ∀ (as bs : List VTy), Eqs.size (as.zip bs) ≤ VTy.usizeL as + VTy.usizeL bs
  | [], _ => by simp [Eqs.size, VTy.usizeL]
  | _ :: _, [] => by simp [Eqs.size, VTy.usizeL]
  | a :: as, b :: bs => by
    simp only [List.zip_cons_cons, Eqs.size, VTy.usizeL]
    have := Eqs.size_zip as bs
    omega

theorem Eqs.has_zip {j : Nat} : ∀ (as bs : List VTy), Eqs.has j (as.zip bs) = true →
    VTy.hasVarL j as = true ∨ VTy.hasVarL j bs = true
  | [], _, h => by simp [Eqs.has] at h
  | _ :: _, [], h => by simp [Eqs.has] at h
  | a :: as, b :: bs, h => by
    simp only [List.zip_cons_cons, Eqs.has, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · left; simp [VTy.hasVarL, h]
    · right; simp [VTy.hasVarL, h]
    · rcases Eqs.has_zip as bs h with h | h
      · left; simp [VTy.hasVarL, h]
      · right; simp [VTy.hasVarL, h]

theorem Eqs.has_append {j : Nat} : ∀ (a b : Eqs), Eqs.has j (a ++ b) = (a.has j || b.has j)
  | [], b => by simp [Eqs.has]
  | (x, y) :: a, b => by simp [Eqs.has, Eqs.has_append a b, Bool.or_assoc]

/-- A lexicographic decrease of the measure. -/
theorem Unify.lex_lt {a b c d : Nat} (h : a < b ∨ (a ≤ b ∧ c < d)) :
    Prod.Lex (· < ·) (· < ·) (a, c) (b, d) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Prod.Lex.left _ _ h
  · rcases Nat.lt_or_eq_of_le h1 with h1 | h1
    · exact Prod.Lex.left _ _ h1
    · rw [h1]; exact Prod.Lex.right _ h2

/-! ### The algorithm -/

/-- The substitution `σ` after `t` for `x`: `x` to `t` under `σ`, every
    other variable as `σ` gives it. -/
def Unify.thenSubst (x : Nat) (t : VTy) (σ : Nat → VTy) : Nat → VTy := fun j => (Unify.single x t j).subst σ

/-- Robinson's unification of the equations: a most general unifier, if
    any. -/
def unify : Eqs → Option (Nat → VTy)
  | [] => some VTy.var
  | (.var x, b) :: r =>
    if b = .var x then unify r
    else if b.hasVar x then none
    else (unify (Eqs.subst (Unify.single x b) r)).map (Unify.thenSubst x b)
  | (a, .var y) :: r =>
    if a.hasVar y then none
    else (unify (Eqs.subst (Unify.single y a) r)).map (Unify.thenSubst y a)
  | (.int, .int) :: r | (.logic, .logic) :: r | (.char, .char) :: r | (.float, .float) :: r => unify r
  | (.arr a, .arr b) :: r | (.opt a, .opt b) :: r => unify ((a, b) :: r)
  | (.tup as, .tup bs) :: r =>
    if as.length = bs.length then unify (as.zip bs ++ r) else none
  | (.ref ts as, .ref us bs) :: r =>
    if ts = us ∧ as.length = bs.length then unify (as.zip bs ++ r) else none
  | _ :: _ => none
termination_by eqs => (Eqs.count eqs, Eqs.size eqs)
decreasing_by
  all_goals apply Unify.lex_lt
  · exact Or.inr ⟨Eqs.count_le (fun j hj => by simp [Eqs.has, hj]),
      by have := VTy.usize_pos b; simp [Eqs.size, VTy.usize]; omega⟩
  · rename_i _ h2
    exact Or.inl (Eqs.count_elim (by simpa using h2) (by simp [Eqs.has, VTy.hasVar])
      (fun j hj => by simp [Eqs.has, hj]) (fun j hj => by simp [Eqs.has, hj]))
  · rename_i h1
    exact Or.inl (Eqs.count_elim (by simpa using h1) (by simp [Eqs.has, VTy.hasVar])
      (fun j hj => by simp [Eqs.has, hj]) (fun j hj => by simp [Eqs.has, hj]))
  -- (the four scalar types)
  · refine Or.inr ⟨Eqs.count_le (fun j hj => ?_), ?_⟩
    · simp [Eqs.has, hj]
    · simp [Eqs.size, VTy.usize]
  · refine Or.inr ⟨Eqs.count_le (fun j hj => ?_), ?_⟩
    · simp [Eqs.has, hj]
    · simp [Eqs.size, VTy.usize]
  · refine Or.inr ⟨Eqs.count_le (fun j hj => ?_), ?_⟩
    · simp [Eqs.has, hj]
    · simp [Eqs.size, VTy.usize]
  · refine Or.inr ⟨Eqs.count_le (fun j hj => ?_), ?_⟩
    · simp [Eqs.has, hj]
    · simp [Eqs.size, VTy.usize]
  -- (arrays and options)
  · refine Or.inr ⟨Eqs.count_le (fun j hj => ?_), by simp [Eqs.size, VTy.usize]; omega⟩
    simp only [Eqs.has, VTy.hasVar, Bool.or_eq_true] at hj ⊢; exact hj
  · refine Or.inr ⟨Eqs.count_le (fun j hj => ?_), by simp [Eqs.size, VTy.usize]; omega⟩
    simp only [Eqs.has, VTy.hasVar, Bool.or_eq_true] at hj ⊢; exact hj
  -- (tuples and references)
  all_goals
    refine Or.inr ⟨Eqs.count_le (fun j hj => ?_), ?_⟩
    · rw [Eqs.has_append] at hj
      simp only [Eqs.has, VTy.hasVar, Bool.or_eq_true] at hj ⊢
      rcases hj with hj | hj
      · rcases Eqs.has_zip _ _ hj with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
      · exact Or.inr hj
    · rw [Eqs.size_append]
      have := Eqs.size_zip as bs
      simp only [Eqs.size, VTy.usize]
      omega

/-! ### Facts about substitutions -/

theorem VTy.subst_single_of_not {x : Nat} {t u : VTy} (h : u.hasVar x = false) : u.subst (Unify.single x t) = u := by
  calc u.subst (Unify.single x t) = u.subst VTy.var := VTy.subst_congr_vars u fun j hj => by
        have : j ≠ x := fun hjx => by subst hjx; rw [h] at hj; exact absurd hj (by simp)
        simp [Unify.single, this]
    _ = u := VTy.subst_id u

theorem VTy.subst_thenSubst (x : Nat) (t : VTy) (σ : Nat → VTy) (u : VTy) :
    u.subst (Unify.thenSubst x t σ) = (u.subst (Unify.single x t)).subst σ := (VTy.subst_comp _ _ u).symm

theorem VTy.subst_single_unifier {R : Nat → VTy} {x : Nat} {t : VTy} (hR : R x = t.subst R) (u : VTy) :
    (u.subst (Unify.single x t)).subst R = u.subst R := by
  rw [VTy.subst_comp]
  exact VTy.subst_congr_vars u fun k _ => by
    by_cases hk : k = x
    · subst hk; simp [Unify.single, hR]
    · simp [Unify.single, hk]

theorem Eqs.unifies_nil (σ : Nat → VTy) : Eqs.Unifies σ [] := by simp [Eqs.Unifies]

theorem Eqs.unifies_cons {σ : Nat → VTy} {a b : VTy} {r : Eqs} :
    Eqs.Unifies σ ((a, b) :: r) ↔ a.subst σ = b.subst σ ∧ Eqs.Unifies σ r := by
  simp [Eqs.Unifies]

theorem Eqs.unifies_subst {σ τ : Nat → VTy} {r : Eqs} :
    Eqs.Unifies σ (Eqs.subst τ r) ↔ Eqs.Unifies (fun j => (τ j).subst σ) r := by
  simp only [Eqs.Unifies, Eqs.subst, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h p hp
    have := h _ p hp rfl
    simpa [VTy.subst_comp] using this
  · intro h q p hp hq
    subst hq
    simpa [VTy.subst_comp] using h p hp

theorem Eqs.unifies_append {σ : Nat → VTy} {a b : Eqs} :
    Eqs.Unifies σ (a ++ b) ↔ Eqs.Unifies σ a ∧ Eqs.Unifies σ b := by
  simp only [Eqs.Unifies, List.mem_append]
  exact ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
    fun h p hp => hp.elim (h.1 p) (h.2 p)⟩

theorem Eqs.unifies_zip {σ : Nat → VTy} : ∀ {as bs : List VTy}, as.length = bs.length →
    (Eqs.Unifies σ (as.zip bs) ↔ as.map (VTy.subst σ) = bs.map (VTy.subst σ))
  | [], [], _ => by simp [Eqs.Unifies]
  | _ :: _, [], h | [], _ :: _, h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zip_cons_cons, Eqs.unifies_cons, List.map_cons, List.cons.injEq, Eqs.unifies_zip h]

/-! ### The occurs check -/

theorem VTy.usize_le_usizeL {t : VTy} : ∀ {ts : List VTy}, t ∈ ts → t.usize ≤ VTy.usizeL ts
  | [], h => by simp at h
  | u :: us, h => by
    simp only [VTy.usizeL]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := VTy.usize_le_usizeL h; omega

mutual
theorem VTy.usize_le_subst {R : Nat → VTy} {x : Nat} :
    ∀ u : VTy, u.hasVar x = true → (R x).usize ≤ (u.subst R).usize
  | .int, h | .logic, h | .char, h | .float, h => by simp [VTy.hasVar] at h
  | .var k, h => by simp [VTy.hasVar] at h; subst h; simp
  | .arr u, h | .opt u, h => by
    have := VTy.usize_le_subst (R := R) u (by simpa [VTy.hasVar] using h)
    simp [VTy.usize]; omega
  | .tup us, h => by
    have := VTy.usize_le_substL (R := R) us (by simpa [VTy.hasVar] using h)
    simp [VTy.usize]; omega
  | .ref _ us, h => by
    have := VTy.usize_le_substL (R := R) us (by simpa [VTy.hasVar] using h)
    simp [VTy.subst, VTy.substL_eq_map, VTy.usize]; omega
theorem VTy.usize_le_substL {R : Nat → VTy} {x : Nat} :
    ∀ us : List VTy, VTy.hasVarL x us = true → (R x).usize ≤ VTy.usizeL (us.map (VTy.subst R))
  | [], h => by simp [VTy.hasVarL] at h
  | u :: us, h => by
    simp only [VTy.hasVarL, Bool.or_eq_true] at h
    simp only [List.map_cons, VTy.usizeL]
    rcases h with h | h
    · have := VTy.usize_le_subst (R := R) u h; omega
    · have := VTy.usize_le_substL (R := R) us h; omega
end

/-- A variable inside a type that is not the variable itself: no
    substitution makes them equal. -/
theorem VTy.occurs_no_unifier {R : Nat → VTy} {x : Nat} {t : VTy} (hx : t.hasVar x = true)
    (ht : t ≠ .var x) : R x ≠ t.subst R := by
  intro he
  have hlt : (R x).usize < (t.subst R).usize := by
    cases t with
    | var k => simp [VTy.hasVar] at hx; subst hx; exact absurd rfl ht
    | int | logic | char | float => simp [VTy.hasVar] at hx
    | arr u | opt u =>
      have := VTy.usize_le_subst u (R := R) (by simpa [VTy.hasVar] using hx)
      simp [VTy.usize]; omega
    | tup us =>
      have := VTy.usize_le_substL us (R := R) (by simpa [VTy.hasVar] using hx)
      simp [VTy.usize]; omega
    | ref _ us =>
      have := VTy.usize_le_substL us (R := R) (by simpa [VTy.hasVar] using hx)
      simp [VTy.subst, VTy.substL_eq_map, VTy.usize]; omega
  rw [he] at hlt; exact Nat.lt_irrefl _ hlt

/-! ### Correctness -/

/-- What `unify` gives is a unifier through which every unifier factors,
    and it gives one whenever there is one. -/
def UnifySpec (eqs : Eqs) : Prop :=
  (∀ σ, unify eqs = some σ → Eqs.Unifies σ eqs ∧ ∀ R, Eqs.Unifies R eqs → ∀ j, (σ j).subst R = R j) ∧
  (∀ R, Eqs.Unifies R eqs → (unify eqs).isSome)

theorem UnifySpec.of_equiv {old new : Eqs} (hu : unify old = unify new)
    (hiff : ∀ R, Eqs.Unifies R old ↔ Eqs.Unifies R new) (ih : UnifySpec new) : UnifySpec old := by
  refine ⟨fun σ h => ?_, fun R hR => ?_⟩
  · rw [hu] at h
    obtain ⟨h1, h2⟩ := ih.1 σ h
    exact ⟨(hiff σ).mpr h1, fun R hR => h2 R ((hiff R).mp hR)⟩
  · rw [hu]; exact ih.2 R ((hiff R).mp hR)

theorem UnifySpec.of_none {old : Eqs} (hu : unify old = none) (hno : ∀ R, ¬ Eqs.Unifies R old) :
    UnifySpec old := by
  refine ⟨fun σ h => ?_, fun R hR => absurd hR (hno R)⟩
  rw [hu] at h; exact absurd h (by simp)

theorem UnifySpec.of_elim {x : Nat} {b : VTy} {r old : Eqs} (hbx : b.hasVar x = false)
    (hu : unify old = (unify (Eqs.subst (Unify.single x b) r)).map (Unify.thenSubst x b))
    (hiff : ∀ R, Eqs.Unifies R old ↔ R x = b.subst R ∧ Eqs.Unifies R r)
    (ih : UnifySpec (Eqs.subst (Unify.single x b) r)) : UnifySpec old := by
  -- (a unifier of the equations unifies the rest under the substitution)
  have hrest : ∀ R, R x = b.subst R → Eqs.Unifies R r → Eqs.Unifies R (Eqs.subst (Unify.single x b) r) := by
    intro R hx hr
    rw [Eqs.unifies_subst]
    have : (fun j => (Unify.single x b j).subst R) = R := funext fun j => by
      by_cases hj : j = x
      · subst hj; simp [Unify.single, hx]
      · simp [Unify.single, hj]
    rw [this]; exact hr
  refine ⟨fun σ h => ?_, fun R hR => ?_⟩
  · rw [hu] at h
    obtain ⟨σ', h', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨h1, h2⟩ := ih.1 σ' h'
    refine ⟨(hiff _).mpr ⟨?_, Eqs.unifies_subst.mp h1⟩, fun R hR j => ?_⟩
    · show (Unify.single x b x).subst σ' = b.subst (Unify.thenSubst x b σ')
      rw [VTy.subst_thenSubst, VTy.subst_single_of_not hbx]; simp [Unify.single]
    · obtain ⟨hx, hr⟩ := (hiff R).mp hR
      have hσ' := h2 R (hrest R hx hr)
      show ((Unify.single x b j).subst σ').subst R = R j
      rw [VTy.subst_comp, show (fun k => (σ' k).subst R) = R from funext hσ']
      by_cases hj : j = x
      · subst hj; simp [Unify.single, hx]
      · simp [Unify.single, hj]
  · obtain ⟨hx, hr⟩ := (hiff R).mp hR
    rw [hu]
    simpa using ih.2 R (hrest R hx hr)

theorem unify_spec (eqs : Eqs) : UnifySpec eqs := by
  induction eqs using unify.induct with
  | case1 =>
    refine ⟨fun σ h => ?_, fun _ _ => by simp [unify]⟩
    simp [unify] at h; subst h
    exact ⟨Eqs.unifies_nil _, fun R _ j => by simp⟩
  | case2 x r ih =>
    exact UnifySpec.of_equiv (by simp [unify]) (fun R => by simp [Eqs.unifies_cons]) ih
  | case3 x b r hne hocc =>
    exact UnifySpec.of_none (by simp [unify, hne, hocc]) fun R hR =>
      VTy.occurs_no_unifier hocc hne (by simpa using (Eqs.unifies_cons.mp hR).1)
  | case4 x b r hne hocc ih =>
    exact UnifySpec.of_elim (by simpa using hocc) (by simp [unify, hne, hocc])
      (fun R => by simp [Eqs.unifies_cons]) ih
  | case5 a y r hnv hocc =>
    have hu : unify ((a, VTy.var y) :: r) = none := by
      cases a <;> simp_all [unify]
    exact UnifySpec.of_none hu fun R hR =>
      VTy.occurs_no_unifier hocc (fun h => hnv y h) (by simpa using (Eqs.unifies_cons.mp hR).1.symm)
  | case6 a y r hnv hocc ih =>
    have hu : unify ((a, VTy.var y) :: r) = (unify (Eqs.subst (Unify.single y a) r)).map (Unify.thenSubst y a) := by
      cases a <;> simp_all [unify]
    exact UnifySpec.of_elim (by simpa using hocc) hu
      (fun R => by simp [Eqs.unifies_cons, eq_comm]) ih
  | case7 r ih | case8 r ih | case9 r ih | case10 r ih =>
    exact UnifySpec.of_equiv (by simp [unify]) (fun R => by simp [Eqs.unifies_cons]) ih
  | case11 a b r ih | case12 a b r ih =>
    exact UnifySpec.of_equiv (by simp [unify]) (fun R => by simp [Eqs.unifies_cons]) ih
  | case13 as bs r hlen ih =>
    exact UnifySpec.of_equiv (by simp [unify, hlen])
      (fun R => by simp [Eqs.unifies_cons, Eqs.unifies_append, Eqs.unifies_zip hlen]) ih
  | case14 as bs r hlen =>
    exact UnifySpec.of_none (by simp [unify, hlen]) fun R hR => by
      have h := (Eqs.unifies_cons.mp hR).1
      simp at h
      exact hlen (by simpa using congrArg List.length h)
  | case15 ts as us bs r h ih =>
    obtain ⟨rfl, hlen⟩ := h
    exact UnifySpec.of_equiv (by simp [unify, hlen])
      (fun R => by simp [Eqs.unifies_cons, Eqs.unifies_append, Eqs.unifies_zip hlen, VTy.subst,
        VTy.substL_eq_map]) ih
  | case16 ts as us bs r h =>
    exact UnifySpec.of_none (by simp [unify, h]) fun R hR => by
      have he := (Eqs.unifies_cons.mp hR).1
      simp [VTy.subst, VTy.substL_eq_map] at he
      exact h ⟨he.1, by simpa using congrArg List.length he.2⟩
  | case17 head tail h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    refine UnifySpec.of_none (by rw [unify.eq_12 head tail h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]) fun R hR => ?_
    rcases head with ⟨a, b⟩
    have he := (Eqs.unifies_cons.mp hR).1
    cases a <;> cases b <;> first
      | exact h1 _ _ rfl | exact h2 _ _ rfl | exact h3 rfl | exact h4 rfl | exact h5 rfl | exact h6 rfl
      | exact h7 _ _ rfl | exact h8 _ _ rfl | exact h9 _ _ rfl | exact h10 _ _ _ _ rfl
      | (simp only [VTy.subst] at he; cases he)

/-- `unify` gives a unifier. -/
theorem unify_sound {eqs : Eqs} {σ : Nat → VTy} (h : unify eqs = some σ) : Eqs.Unifies σ eqs :=
  ((unify_spec eqs).1 σ h).1

/-- Every unifier factors through what `unify` gives: it is a most general
    unifier. -/
theorem unify_mgu {eqs : Eqs} {σ R : Nat → VTy} (h : unify eqs = some σ) (hR : Eqs.Unifies R eqs) (j : Nat) :
    (σ j).subst R = R j :=
  ((unify_spec eqs).1 σ h).2 R hR j

/-- `unify` finds a unifier whenever there is one. -/
theorem unify_complete {eqs : Eqs} {R : Nat → VTy} (hR : Eqs.Unifies R eqs) : ∃ σ, unify eqs = some σ :=
  Option.isSome_iff_exists.mp ((unify_spec eqs).2 R hR)

/-- What `unify` gives is idempotent: it is a unifier, so it factors through itself. -/
theorem unify_idem {eqs : Eqs} {σ : Nat → VTy} (h : unify eqs = some σ) (j : Nat) :
    (σ j).subst σ = σ j :=
  unify_mgu h (unify_sound h) j

/-- `unify` fails exactly when nothing unifies the equations. -/
theorem unify_eq_none_iff {eqs : Eqs} : unify eqs = none ↔ ∀ R, ¬ Eqs.Unifies R eqs := by
  constructor
  · intro h R hR
    obtain ⟨σ, hσ⟩ := unify_complete hR
    rw [h] at hσ; cases hσ
  · intro h
    cases hu : unify eqs with
    | none => rfl
    | some σ => exact absurd (unify_sound hu) (h σ)

/-! ### Examples -/

/-- The first `n` variables' images under what `unify` gives. -/
private def unifyAt (n : Nat) (eqs : Eqs) : Option (List VTy) :=
  (unify eqs).map fun σ => (List.range n).map σ

-- `dup(t) := class(pair(t, t))`: the second argument is the first, twice over
example : unifyAt 2 [(.var 1, .tup [.var 0, .var 0])] = some [.var 0, .tup [.var 0, .var 0]] := by
  native_decide
-- a chain of variables ends at the type it is equal to
example : unifyAt 3 [(.var 0, .var 1), (.var 1, .var 2), (.var 2, .int)] = some [.int, .int, .int] := by
  native_decide
-- the occurs check, either way round
example : unifyAt 1 [(.var 0, .arr (.var 0))] = none := by native_decide
example : unifyAt 1 [(.opt (.var 0), .var 0)] = none := by native_decide
-- tuples of different lengths
example : unifyAt 1 [(.tup [.var 0], .tup [.int, .int])] = none := by native_decide

end OpenVerse
