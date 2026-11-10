/-
  OpenVerse — substitution of type variables in Verse Core types.

  Lemmas about `VTy.subst` alone: composition, the identity, congruence on
  the variables a type mentions, closed types, and class instantiation
  (`VTy.inst`). `Core/Unify.lean` and the type safety proof build on them.
-/
import OpenVerse.Core.Typing

namespace OpenVerse

mutual
theorem VTy.closed_subst (θ : Nat → VTy) : ∀ t : VTy, t.closed = true → t.subst θ = t
  | .int, _ | .logic, _ | .char, _ | .float, _ => by simp
  | .ref _ args, h => by simp only [VTy.closed] at h; simpa using VTy.closedL_subst θ args h
  | .vref _ args, h => by simp only [VTy.closed] at h; simpa using VTy.closedL_subst θ args h
  | .var _, h => by simp [VTy.closed] at h
  | .arr t, h => by simp only [VTy.closed] at h; simp [VTy.closed_subst θ t h]
  | .opt t, h => by simp only [VTy.closed] at h; simp [VTy.closed_subst θ t h]
  | .tup ts, h => by simp only [VTy.closed] at h; simpa using VTy.closedL_subst θ ts h
theorem VTy.closedL_subst (θ : Nat → VTy) : ∀ ts : List VTy, VTy.closedL ts = true → ts.map (VTy.subst θ) = ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [VTy.closedL, Bool.and_eq_true] at h
    simp [VTy.closed_subst θ t h.1, VTy.closedL_subst θ ts h.2]
end

mutual
/-- A type is closed once closed types are substituted for its variables. -/
theorem VTy.subst_closed {σ : Nat → VTy} (hσ : ∀ j, (σ j).closed = true) :
    ∀ t : VTy, (t.subst σ).closed = true
  | .int | .logic | .char | .float => by simp [VTy.closed]
  | .var j => by simpa using hσ j
  | .arr t | .opt t => by simpa [VTy.closed] using VTy.subst_closed hσ t
  | .tup ts | .ref _ ts | .vref _ ts => by simpa [VTy.closed] using VTy.substL_closed hσ ts
theorem VTy.substL_closed {σ : Nat → VTy} (hσ : ∀ j, (σ j).closed = true) :
    ∀ ts : List VTy, VTy.closedL (ts.map (VTy.subst σ)) = true
  | [] => rfl
  | t :: ts => by simp [VTy.closedL, VTy.subst_closed hσ t, VTy.substL_closed hσ ts]
end

theorem VTy.closedL_iff : ∀ {ts : List VTy}, VTy.closedL ts = true ↔ ∀ t ∈ ts, t.closed = true
  | [] => by simp [VTy.closedL]
  | t :: ts => by rw [VTy.closedL, Bool.and_eq_true, VTy.closedL_iff]; simp

mutual
theorem VTy.subst_comp (θ₁ θ₂ : Nat → VTy) : ∀ t : VTy,
    (t.subst θ₁).subst θ₂ = t.subst (fun j => (θ₁ j).subst θ₂)
  | .int | .logic | .char | .float | .var _ => by simp
  | .ref _ args => by simpa using VTy.substL_comp θ₁ θ₂ args
  | .vref _ args => by simpa using VTy.substL_comp θ₁ θ₂ args
  | .arr t => by simp [VTy.subst_comp θ₁ θ₂ t]
  | .opt t => by simp [VTy.subst_comp θ₁ θ₂ t]
  | .tup ts => by simpa using VTy.substL_comp θ₁ θ₂ ts
theorem VTy.substL_comp (θ₁ θ₂ : Nat → VTy) : ∀ ts : List VTy,
    ts.map (fun t => (t.subst θ₁).subst θ₂) = ts.map (VTy.subst fun j => (θ₁ j).subst θ₂)
  | [] => rfl
  | t :: ts => by simp only [List.map_cons, VTy.subst_comp θ₁ θ₂ t, VTy.substL_comp θ₁ θ₂ ts]
end

mutual
theorem VTy.subst_id : ∀ t : VTy, t.subst VTy.var = t
  | .int | .logic | .char | .float | .var _ => by simp
  | .ref _ args => by simpa using VTy.substL_id args
  | .vref _ args => by simpa using VTy.substL_id args
  | .arr t => by simp [VTy.subst_id t]
  | .opt t => by simp [VTy.subst_id t]
  | .tup ts => by simpa using VTy.substL_id ts
theorem VTy.substL_id : ∀ ts : List VTy, ts.map (VTy.subst VTy.var) = ts
  | [] => rfl
  | t :: ts => by simp only [List.map_cons, VTy.subst_id t, VTy.substL_id ts]
end

/-- Instantiating a class's field type commutes with substitution. -/
theorem VTy.inst_subst (θ : Nat → VTy) (args : List VTy) (t : VTy) :
    (t.inst args).subst θ = t.inst (args.map (VTy.subst θ)) := by
  simp only [VTy.inst, VTy.subst_comp]
  congr 1
  funext j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases args[j]? <;> simp

theorem VTy.map_inst_subst (θ : Nat → VTy) (args fs : List VTy) :
    (fs.map (VTy.inst args)).map (VTy.subst θ) = fs.map (VTy.inst (args.map (VTy.subst θ))) := by
  simp [List.map_map, Function.comp_def, VTy.inst_subst]

mutual
/-- Substitutions that agree below `n` agree on a type whose variables are below `n`. -/
theorem VTy.subst_congr {σ σ' : Nat → VTy} {n : Nat} (hσ : ∀ j < n, σ j = σ' j) :
    ∀ t : VTy, t.varsBelow n = true → t.subst σ = t.subst σ'
  | .int, _ | .logic, _ | .char, _ | .float, _ => by simp
  | .var j, h => by simp only [VTy.varsBelow, decide_eq_true_eq] at h; simp [hσ j h]
  | .arr t, h => by simp only [VTy.varsBelow] at h; simp [VTy.subst_congr hσ t h]
  | .opt t, h => by simp only [VTy.varsBelow] at h; simp [VTy.subst_congr hσ t h]
  | .tup ts, h => by simp only [VTy.varsBelow] at h; simp [VTy.substL_congr hσ ts h]
  | .ref _ ts, h => by simp only [VTy.varsBelow] at h; simp [VTy.substL_congr hσ ts h]
  | .vref _ ts, h => by simp only [VTy.varsBelow] at h; simp [VTy.substL_congr hσ ts h]
theorem VTy.substL_congr {σ σ' : Nat → VTy} {n : Nat} (hσ : ∀ j < n, σ j = σ' j) :
    ∀ ts : List VTy, VTy.varsBelowL n ts = true → ts.map (VTy.subst σ) = ts.map (VTy.subst σ')
  | [], _ => rfl
  | t :: ts, h => by
    simp only [VTy.varsBelowL, Bool.and_eq_true] at h
    simp [VTy.subst_congr hσ t h.1, VTy.substL_congr hσ ts h.2]
end


mutual
/-- Substitutions that agree on a type's variables agree on it. -/
theorem VTy.subst_congr_vars {σ σ' : Nat → VTy} :
    ∀ t : VTy, (∀ j, t.hasVar j = true → σ j = σ' j) → t.subst σ = t.subst σ'
  | .int, _ | .logic, _ | .char, _ | .float, _ => by simp
  | .var j, h => by simpa using h j (by simp [VTy.hasVar])
  | .arr t, h => by simp [VTy.subst_congr_vars t (fun j hj => h j (by simpa [VTy.hasVar] using hj))]
  | .opt t, h => by simp [VTy.subst_congr_vars t (fun j hj => h j (by simpa [VTy.hasVar] using hj))]
  | .tup ts, h => by simp [VTy.substL_congr_vars ts (fun j hj => h j (by simpa [VTy.hasVar] using hj))]
  | .ref _ ts, h => by simp [VTy.substL_congr_vars ts (fun j hj => h j (by simpa [VTy.hasVar] using hj))]
  | .vref _ ts, h => by simp [VTy.substL_congr_vars ts (fun j hj => h j (by simpa [VTy.hasVar] using hj))]
theorem VTy.substL_congr_vars {σ σ' : Nat → VTy} :
    ∀ ts : List VTy, (∀ j, VTy.hasVarL j ts = true → σ j = σ' j) → ts.map (VTy.subst σ) = ts.map (VTy.subst σ')
  | [], _ => rfl
  | t :: ts, h => by
    simp [VTy.subst_congr_vars t (fun j hj => h j (by simp [VTy.hasVarL, hj])),
      VTy.substL_congr_vars ts (fun j hj => h j (by simp [VTy.hasVarL, hj]))]
end

mutual
/-- Two substitutions that agree on a type agree on its variables. -/
theorem VTy.vars_of_subst_eq {σ σ' : Nat → VTy} :
    ∀ t : VTy, t.subst σ = t.subst σ' → ∀ j, t.hasVar j = true → σ j = σ' j
  | .int, _, _, h | .logic, _, _, h | .char, _, _, h | .float, _, _, h => by simp [VTy.hasVar] at h
  | .var i, he, j, h => by simp [VTy.hasVar] at h; subst h; simpa using he
  | .arr t, he, j, h => VTy.vars_of_subst_eq t (by simpa using he) j (by simpa [VTy.hasVar] using h)
  | .opt t, he, j, h => VTy.vars_of_subst_eq t (by simpa using he) j (by simpa [VTy.hasVar] using h)
  | .tup ts, he, j, h => VTy.varsL_of_subst_eq ts (by simpa using he) j (by simpa [VTy.hasVar] using h)
  | .ref _ ts, he, j, h => VTy.varsL_of_subst_eq ts (by simpa using he) j (by simpa [VTy.hasVar] using h)
  | .vref _ ts, he, j, h => VTy.varsL_of_subst_eq ts (by simpa using he) j (by simpa [VTy.hasVar] using h)
theorem VTy.varsL_of_subst_eq {σ σ' : Nat → VTy} :
    ∀ ts : List VTy, ts.map (VTy.subst σ) = ts.map (VTy.subst σ') → ∀ j, VTy.hasVarL j ts = true → σ j = σ' j
  | [], _, _, h => by simp [VTy.hasVarL] at h
  | t :: ts, he, j, h => by
    simp only [List.map_cons, List.cons.injEq] at he
    simp only [VTy.hasVarL, Bool.or_eq_true] at h
    rcases h with h | h
    · exact VTy.vars_of_subst_eq t he.1 j h
    · exact VTy.varsL_of_subst_eq ts he.2 j h
end

mutual
/-- A variable of a type whose instance is closed is instantiated by a closed type. -/
theorem VTy.closed_of_subst {σ : Nat → VTy} :
    ∀ t : VTy, (t.subst σ).closed = true → ∀ j, t.hasVar j = true → (σ j).closed = true
  | .int, _, _, h | .logic, _, _, h | .char, _, _, h | .float, _, _, h => by simp [VTy.hasVar] at h
  | .var i, hc, j, h => by simp [VTy.hasVar] at h; subst h; simpa using hc
  | .arr t, hc, j, h => VTy.closed_of_subst t (by simpa [VTy.closed] using hc) j (by simpa [VTy.hasVar] using h)
  | .opt t, hc, j, h => VTy.closed_of_subst t (by simpa [VTy.closed] using hc) j (by simpa [VTy.hasVar] using h)
  | .tup ts, hc, j, h => VTy.closedL_of_subst ts (by simpa [VTy.closed] using hc) j (by simpa [VTy.hasVar] using h)
  | .ref _ ts, hc, j, h => VTy.closedL_of_subst ts (by simpa [VTy.closed] using hc) j (by simpa [VTy.hasVar] using h)
  | .vref _ ts, hc, j, h => VTy.closedL_of_subst ts (by simpa [VTy.closed] using hc) j (by simpa [VTy.hasVar] using h)
theorem VTy.closedL_of_subst {σ : Nat → VTy} :
    ∀ ts : List VTy, VTy.closedL (ts.map (VTy.subst σ)) = true → ∀ j, VTy.hasVarL j ts = true → (σ j).closed = true
  | [], _, _, h => by simp [VTy.hasVarL] at h
  | t :: ts, hc, j, h => by
    simp only [List.map_cons, VTy.closedL, Bool.and_eq_true] at hc
    simp only [VTy.hasVarL, Bool.or_eq_true] at h
    rcases h with h | h
    · exact VTy.closed_of_subst t hc.1 j h
    · exact VTy.closedL_of_subst ts hc.2 j h
end

mutual
/-- A closed type has no variables. -/
theorem VTy.hasVar_closed : ∀ t : VTy, t.closed = true → ∀ j, t.hasVar j = false
  | .int, _, _ | .logic, _, _ | .char, _, _ | .float, _, _ => by simp [VTy.hasVar]
  | .var _, h, _ => by simp [VTy.closed] at h
  | .arr t, h, j => by simp only [VTy.closed] at h; simpa [VTy.hasVar] using VTy.hasVar_closed t h j
  | .opt t, h, j => by simp only [VTy.closed] at h; simpa [VTy.hasVar] using VTy.hasVar_closed t h j
  | .tup ts, h, j => by simp only [VTy.closed] at h; simpa [VTy.hasVar] using VTy.hasVarL_closed ts h j
  | .ref _ ts, h, j => by simp only [VTy.closed] at h; simpa [VTy.hasVar] using VTy.hasVarL_closed ts h j
  | .vref _ ts, h, j => by simp only [VTy.closed] at h; simpa [VTy.hasVar] using VTy.hasVarL_closed ts h j
theorem VTy.hasVarL_closed : ∀ ts : List VTy, VTy.closedL ts = true → ∀ j, VTy.hasVarL j ts = false
  | [], _, _ => rfl
  | t :: ts, h, j => by
    simp only [VTy.closedL, Bool.and_eq_true] at h
    simp [VTy.hasVarL, VTy.hasVar_closed t h.1 j, VTy.hasVarL_closed ts h.2 j]
end

end OpenVerse
