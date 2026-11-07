/-
  OpenVerse — type safety of Verse Core.

  `Runs.no_type_error`: in a typed program (`ProgTyped`), no run raises a
  type error, and `Main`'s result has its declared type. With
  `Eval.scoped_ok` and `Eval.no_fail`, this leaves `overflow`, `Err()` and
  an escaped `break` as the only runtime errors a checked program can have.

  The proof is by strong induction on the fuel of the interpreter
  (`eval_typed`), transported to the big-step relation by `eval_iff`.
-/
import OpenVerse.Core.Typing
import OpenVerse.Core.Adequacy

namespace OpenVerse

-- the typing of the heap objects (their classes and type arguments), for
-- the typing of references (#29, #39)
variable {Ξ : HeapTy}

/-! ### Values -/

theorem allTy_iff {vs : List Value} {t : VTy} : allTy Ξ vs t = true ↔ ∀ v ∈ vs, hasTy Ξ v t = true := by
  induction vs with
  | nil => simp [allTy]
  | cons v vs ih => simp [allTy, ih]

theorem allTys_length : ∀ {vs : List Value} {ts : List VTy}, allTys Ξ vs ts = true → vs.length = ts.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [allTys, Bool.and_eq_true] at h
    simp [allTys_length h.2]
  | [], _ :: _, h => by simp [allTys] at h
  | _ :: _, [], h => by simp [allTys] at h

theorem allTys_get : ∀ {vs : List Value} {ts : List VTy} {i : Nat} {t : VTy}, allTys Ξ vs ts = true → ts[i]? = some t →
    ∃ v, vs[i]? = some v ∧ hasTy Ξ v t = true
  | [], [], _, _, _, h => by simp at h
  | v :: vs, t' :: ts, 0, t, h, hi => by
    simp only [allTys, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi ⊢
    subst hi; exact ⟨v, rfl, h.1⟩
  | v :: vs, t' :: ts, i+1, t, h, hi => by
    simp only [allTys, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_succ] at hi ⊢
    exact allTys_get h.2 hi
  | [], _ :: _, _, _, h, _ => by simp [allTys] at h
  | _ :: _, [], _, _, h, _ => by simp [allTys] at h

theorem allTys_set : ∀ {vs : List Value} {ts : List VTy} {i : Nat} {t : VTy} {v : Value}, allTys Ξ vs ts = true → ts[i]? = some t →
    hasTy Ξ v t = true → allTys Ξ (vs.set i v) ts = true
  | [], [], _, _, _, _, h, _ => by simp at h
  | w :: vs, t' :: ts, 0, t, v, h, hi, hv => by
    simp only [allTys, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi; simp [allTys, hv, h.2]
  | w :: vs, t' :: ts, i+1, t, v, h, hi, hv => by
    simp only [allTys, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_succ] at hi
    simp [allTys, h.1, allTys_set h.2 hi hv]
  | [], _ :: _, _, _, _, h, _, _ => by simp [allTys] at h
  | _ :: _, [], _, _, _, h, _, _ => by simp [allTys] at h

theorem allTys_append : ∀ {a : List Value} {c : List VTy} {b d}, allTys Ξ a c = true → allTys Ξ b d = true →
    allTys Ξ (a ++ b) (c ++ d) = true
  | [], [], _, _, _, h => by simpa using h
  | _ :: _, _ :: _, _, _, h, h' => by
    simp only [allTys, Bool.and_eq_true] at h
    simp [allTys, h.1, allTys_append h.2 h']
  | [], _ :: _, _, _, h, _ => by simp [allTys] at h
  | _ :: _, [], _, _, h, _ => by simp [allTys] at h

theorem allTy_of_allTys : ∀ {vs : List Value} {ts : List VTy} {t}, (∀ u ∈ ts, u = t) →
    allTys Ξ vs ts = true → allTy Ξ vs t = true
  | [], [], _, _, _ => rfl
  | _ :: _, u :: _, t, hu, h => by
    simp only [allTys, Bool.and_eq_true] at h
    have : u = t := hu u (by simp)
    subst this
    simp [allTy, h.1, allTy_of_allTys (fun w hw => hu w (by simp [hw])) h.2]
  | [], _ :: _, _, _, h => by simp [allTys] at h
  | _ :: _, [], _, _, h => by simp [allTys] at h

theorem allTy_append {a b : List Value} {t} (ha : allTy Ξ a t = true) (hb : allTy Ξ b t = true) :
    allTy Ξ (a ++ b) t = true := by
  rw [allTy_iff] at *; intro v hv; rcases List.mem_append.mp hv with h | h; exact ha v h; exact hb v h

theorem allTy_get {xs : List Value} {t : VTy} {n : Nat} {v : Value} (h : allTy Ξ xs t = true) (hv : xs[n]? = some v) :
    hasTy Ξ v t = true :=
  allTy_iff.mp h v (List.mem_of_getElem? hv)

theorem allTy_set {xs : List Value} {t : VTy} {n : Nat} {v : Value} (h : allTy Ξ xs t = true) (hv : hasTy Ξ v t = true) :
    allTy Ξ (xs.set n v) t = true := by
  rw [allTy_iff] at *
  intro w hw
  rcases List.mem_or_eq_of_mem_set hw with h' | h'
  · exact h w h'
  · subst h'; exact hv

theorem allTy_reverse {xs : List Value} {t} (h : allTy Ξ xs t = true) : allTy Ξ xs.reverse t = true := by
  rw [allTy_iff] at *; intro v hv; exact h v (List.mem_reverse.mp hv)

/-! ### Substitution of type variables -/

mutual
theorem VTy.closed_subst (θ : Nat → VTy) : ∀ t : VTy, t.closed = true → t.subst θ = t
  | .int, _ | .logic, _ | .char, _ | .float, _ => by simp
  | .ref _ args, h => by simp only [VTy.closed] at h; simpa using VTy.closedL_subst θ args h
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

theorem VTy.closedL_iff : ∀ {ts : List VTy}, VTy.closedL ts = true ↔ ∀ t ∈ ts, t.closed = true
  | [] => by simp [VTy.closedL]
  | t :: ts => by rw [VTy.closedL, Bool.and_eq_true, VTy.closedL_iff]; simp

mutual
/-- Values keep their types under any substitution, in a heap typing
    without type variables: a type variable has no values, so it only
    occurs where the value is `[]` or the empty option. -/
theorem hasTy_subst (hΞ : ∀ p ∈ Ξ, VTy.closedL p.2 = true) (θ : Nat → VTy) :
    ∀ (t : VTy) (v : Value), hasTy Ξ v t = true → hasTy Ξ v (t.subst θ) = true
  | .int, _, h | .logic, _, h | .char, _, h | .float, _, h => by simpa using h
  | .ref ts args, v, h => by
    cases v
    case ref a =>
      simp only [hasTy, VTy.subst_ref] at h ⊢
      rcases ha : Ξ[a]? with _ | ⟨t, args'⟩
      · simp [ha] at h
      · simp only [ha, Bool.and_eq_true, List.isPrefixOf_iff_prefix] at h ⊢
        obtain ⟨h1, hp⟩ := h
        have hc : VTy.closedL args = true := VTy.closedL_iff.mpr fun x hx =>
          VTy.closedL_iff.mp (hΞ _ (List.mem_of_getElem? ha)) x (hp.subset hx)
        rw [VTy.closedL_subst θ args hc]
        exact ⟨h1, hp⟩
    all_goals simp [hasTy] at h
  | .var _, v, h => by cases v <;> simp [hasTy] at h
  | .arr t, v, h => by
    cases v
    case arr vs =>
      simp only [hasTy, VTy.subst_arr] at h ⊢
      rw [allTy_iff] at h ⊢
      exact fun w hw => hasTy_subst hΞ θ t w (h w hw)
    all_goals simp [hasTy] at h
  | .opt t, v, h => by
    cases v
    case none => simp [hasTy]
    case some w => simp only [hasTy, VTy.subst_opt] at h ⊢; exact hasTy_subst hΞ θ t w h
    all_goals simp [hasTy] at h
  | .tup ts, v, h => by
    cases v
    case tup vs => simp only [hasTy, VTy.subst_tup] at h ⊢; exact allTys_subst hΞ θ ts vs h
    all_goals simp [hasTy] at h
theorem allTys_subst (hΞ : ∀ p ∈ Ξ, VTy.closedL p.2 = true) (θ : Nat → VTy) :
    ∀ (ts : List VTy) (vs : List Value), allTys Ξ vs ts = true →
    allTys Ξ vs (ts.map (VTy.subst θ)) = true
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [allTys] at h
  | _ :: _, [], h => by simp [allTys] at h
  | t :: ts, v :: vs, h => by
    simp only [allTys, Bool.and_eq_true, List.map_cons] at h ⊢
    exact ⟨hasTy_subst hΞ θ t v h.1, allTys_subst hΞ θ ts vs h.2⟩
end

mutual
theorem VTy.subst_comp (θ₁ θ₂ : Nat → VTy) : ∀ t : VTy,
    (t.subst θ₁).subst θ₂ = t.subst (fun j => (θ₁ j).subst θ₂)
  | .int | .logic | .char | .float | .var _ => by simp
  | .ref _ args => by simpa using VTy.substL_comp θ₁ θ₂ args
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

theorem FieldTy.subst {S : Sigs} {ts : List Nat} {args : List VTy} {k : Nat} {τ : VTy} (θ : Nat → VTy)
    (h : FieldTy S ts args k τ) : FieldTy S ts (args.map (VTy.subst θ)) k (τ.subst θ) := by
  intro t ht
  obtain ⟨fs, f, hc, hk, hv, rfl⟩ := h t ht
  exact ⟨fs, f, hc, hk, by simpa using hv, (VTy.inst_subst θ args f).symm⟩

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
theorem VTy.substL_congr {σ σ' : Nat → VTy} {n : Nat} (hσ : ∀ j < n, σ j = σ' j) :
    ∀ ts : List VTy, VTy.varsBelowL n ts = true → ts.map (VTy.subst σ) = ts.map (VTy.subst σ')
  | [], _ => rfl
  | t :: ts, h => by
    simp only [VTy.varsBelowL, Bool.and_eq_true] at h
    simp [VTy.subst_congr hσ t h.1, VTy.substL_congr hσ ts h.2]
end

/-- A field type mentioning only the first `args.length` type parameters
    has the same instance at every extension of `args` (#39). -/
theorem VTy.inst_prefix {args args' : List VTy} (hp : args <+: args') {f : VTy}
    (hf : f.varsBelow args.length = true) : f.inst args' = f.inst args := by
  unfold VTy.inst
  refine VTy.subst_congr (n := args.length) (fun j hj => ?_) f hf
  obtain ⟨r, rfl⟩ := hp
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem PrimTy.subst (θ : Nat → VTy) {op ts τ} (h : PrimTy op ts τ) :
    PrimTy op (ts.map (VTy.subst θ)) (τ.subst θ) := by
  cases h with
  | arith hop => simpa using PrimTy.arith hop
  | unary hop => simpa using PrimTy.unary hop
  | cmpInt hop => simpa using PrimTy.cmpInt hop
  | cmpChar hop => simpa using PrimTy.cmpChar hop
  | eq => exact .eq
  | ne => exact .ne
  | queryLogic => simpa using PrimTy.queryLogic
  | queryOpt => simpa using PrimTy.queryOpt
  | mkArr hall =>
    simp only [VTy.subst_arr]
    exact .mkArr fun u hu => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
      rw [hall w hw]
  | mkTup => simpa using PrimTy.mkTup
  | mkSome => simpa using PrimTy.mkSome
  | concat => simpa using PrimTy.concat
  | index => simpa using PrimTy.index
  | len => simpa using PrimTy.len
  | arrSet => simpa using PrimTy.arrSet
  | flatten => simpa using PrimTy.flatten
  | range => simpa using PrimTy.range
  | tupGet hk => simpa using PrimTy.tupGet (by simp [hk] : (_ : List VTy)[_]? = _)
  | toStrInt => simpa using PrimTy.toStrInt
  | toStrChar => simpa using PrimTy.toStrChar
  | toStrStr => simpa using PrimTy.toStrStr
  | farith hop => simpa using PrimTy.farith hop
  | funary hop => simpa using PrimTy.funary hop
  | fcmp hop => simpa using PrimTy.fcmp hop
  | fofInt => simpa using PrimTy.fofInt
  | fofBits => simpa using PrimTy.fofBits
  | ftoInt hop => simpa using PrimTy.ftoInt hop
  | toStrFloat => simpa using PrimTy.toStrFloat
  | fail => exact .fail
  | userErr => exact .userErr

theorem getElem?_map_some {α β} {l : List α} {i : Nat} {a : α} (f : α → β) (h : l[i]? = some a) :
    (l.map f)[i]? = some (f a) := by
  simp [h]

/-! ### Subtyping (#32) -/

mutual
theorem VTy.sub_refl : ∀ t : VTy, t.sub t = true
  | .ref ts args => by simp [VTy.sub]
  | .arr t => by simp only [VTy.sub]; exact VTy.sub_refl t
  | .opt t => by simp only [VTy.sub]; exact VTy.sub_refl t
  | .tup ts => by simp only [VTy.sub]; exact VTy.subL_refl ts
  | .int | .logic | .char | .float | .var _ => by simp [VTy.sub]
theorem VTy.subL_refl : ∀ ts : List VTy, VTy.subL ts ts = true
  | [] => rfl
  | t :: ts => by simp [VTy.subL, VTy.sub_refl t, VTy.subL_refl ts]
end

mutual
theorem VTy.sub_trans : ∀ (t u w : VTy), t.sub u = true → u.sub w = true → t.sub w = true
  | .ref ts as, u, w, h1, h2 => by
    cases u <;> simp [VTy.sub] at h1
    cases w <;> simp [VTy.sub] at h2 ⊢
    exact ⟨fun x hx => h2.1 x (h1.1 x hx), h2.2.trans h1.2⟩
  | .arr t, u, w, h1, h2 => by
    cases u <;> simp [VTy.sub] at h1
    cases w <;> simp [VTy.sub] at h2 ⊢
    exact VTy.sub_trans _ _ _ h1 h2
  | .opt t, u, w, h1, h2 => by
    cases u <;> simp [VTy.sub] at h1
    cases w <;> simp [VTy.sub] at h2 ⊢
    exact VTy.sub_trans _ _ _ h1 h2
  | .tup ts, u, w, h1, h2 => by
    cases u <;> simp [VTy.sub] at h1
    cases w <;> simp [VTy.sub] at h2 ⊢
    exact VTy.subL_trans _ _ _ h1 h2
  | .int, u, w, h1, h2 | .logic, u, w, h1, h2 | .char, u, w, h1, h2 | .float, u, w, h1, h2 | .var _, u, w, h1, h2 => by
    cases u <;> simp [VTy.sub] at h1 <;> subst_vars <;> exact h2
theorem VTy.subL_trans : ∀ (ts us ws : List VTy), VTy.subL ts us = true → VTy.subL us ws = true →
    VTy.subL ts ws = true
  | [], [], [], _, _ => rfl
  | t :: ts, u :: us, w :: ws, h1, h2 => by
    simp only [VTy.subL, Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨VTy.sub_trans _ _ _ h1.1 h2.1, VTy.subL_trans _ _ _ h1.2 h2.2⟩
  | [], [], _ :: _, _, h | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ | _ :: _, _ :: _, [], _, h => by
    simp [VTy.subL] at h
end

mutual
/-- Subtyping is stable under substitution. -/
theorem VTy.sub_subst (θ : Nat → VTy) : ∀ (t u : VTy), t.sub u = true → (t.subst θ).sub (u.subst θ) = true
  | .ref ts as, u, h => by
    cases u <;> simp [VTy.sub] at h ⊢
    exact ⟨h.1, h.2.map _⟩
  | .arr t, u, h => by
    cases u <;> simp [VTy.sub] at h
    simpa [VTy.sub] using VTy.sub_subst θ _ _ h
  | .opt t, u, h => by
    cases u <;> simp [VTy.sub] at h
    simpa [VTy.sub] using VTy.sub_subst θ _ _ h
  | .tup ts, u, h => by
    cases u <;> simp [VTy.sub] at h
    simpa [VTy.sub] using VTy.subL_subst θ _ _ h
  | .int, u, h | .logic, u, h | .char, u, h | .float, u, h | .var _, u, h => by
    cases u <;> simp [VTy.sub] at h <;> subst_vars <;> exact VTy.sub_refl _
theorem VTy.subL_subst (θ : Nat → VTy) : ∀ (ts us : List VTy), VTy.subL ts us = true →
    VTy.subL (ts.map (VTy.subst θ)) (us.map (VTy.subst θ)) = true
  | [], [], _ => rfl
  | t :: ts, u :: us, h => by
    simp only [VTy.subL, Bool.and_eq_true, List.map_cons] at h ⊢
    exact ⟨VTy.sub_subst θ _ _ h.1, VTy.subL_subst θ _ _ h.2⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [VTy.subL] at h
end

mutual
/-- **Subsumption is sound**: a value of a type is a value of every type above it. -/
theorem hasTy_sub : ∀ (t u : VTy) (v : Value), t.sub u = true → hasTy Ξ v t = true → hasTy Ξ v u = true
  | .ref ts as, u, v, hs, hv => by
    cases u <;> simp [VTy.sub] at hs
    cases v with
    | ref a =>
      simp only [hasTy] at hv ⊢
      rcases ha : Ξ[a]? with _ | ⟨t, args'⟩
      · simp [ha] at hv
      · simp only [ha, Bool.and_eq_true, List.isPrefixOf_iff_prefix] at hv ⊢
        exact ⟨by simpa using hs.1 t (by simpa using hv.1), hs.2.trans hv.2⟩
    | _ => simp [hasTy] at hv
  | .arr t, u, v, hs, hv => by
    cases u <;> simp [VTy.sub] at hs
    cases v with
    | arr vs =>
      simp only [hasTy] at hv ⊢
      rw [allTy_iff] at hv ⊢
      exact fun w hw => hasTy_sub _ _ w hs (hv w hw)
    | _ => simp [hasTy] at hv
  | .opt t, u, v, hs, hv => by
    cases u <;> simp [VTy.sub] at hs
    cases v with
    | none => rfl
    | some w => simp only [hasTy] at hv ⊢; exact hasTy_sub _ _ w hs hv
    | _ => simp [hasTy] at hv
  | .tup ts, u, v, hs, hv => by
    cases u <;> simp [VTy.sub] at hs
    cases v with
    | tup vs => simp only [hasTy] at hv ⊢; exact allTys_sub _ _ vs hs hv
    | _ => simp [hasTy] at hv
  | .int, u, v, hs, hv | .logic, u, v, hs, hv | .char, u, v, hs, hv | .float, u, v, hs, hv | .var _, u, v, hs, hv => by
    cases u <;> simp [VTy.sub] at hs <;> subst_vars <;> exact hv
theorem allTys_sub : ∀ (ts us : List VTy) (vs : List Value), VTy.subL ts us = true →
    allTys Ξ vs ts = true → allTys Ξ vs us = true
  | [], [], [], _, _ => rfl
  | t :: ts, u :: us, v :: vs, hs, hv => by
    simp only [VTy.subL, allTys, Bool.and_eq_true] at hs hv ⊢
    exact ⟨hasTy_sub _ _ _ hs.1 hv.1, allTys_sub _ _ _ hs.2 hv.2⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => by simp [VTy.subL] at h
  | [], [], _ :: _, _, h | _ :: _, _ :: _, [], _, h => by simp [allTys] at h
end

theorem ResOK_sub {t u ρ : VTy} {r : Res} (hs : t.sub u = true) (h : ResOK Ξ t ρ r) : ResOK Ξ u ρ r := by
  cases r <;> simp only [ResOK] at h ⊢
  · exact hasTy_sub _ _ _ hs h
  all_goals exact h

section
variable {S : Sigs} {Γ : List VTy} {ρ : VTy}

mutual
/-- **The substitution lemma.** A typing with type variables holds at every
    instance: this is what lets a generic function be checked once. -/
theorem Typed.subst (hS : S.ClosedProtos) (θ : Nat → VTy) : ∀ {e τ}, Typed S Γ ρ e τ →
    Typed S (Γ.map (VTy.subst θ)) (ρ.subst θ) e (τ.subst θ)
  | _, _, .lit hv => .lit (hasTy_subst hS θ _ _ hv)
  | _, _, .local hi => .local (getElem?_map_some _ hi)
  | _, _, .assign hi he => .assign (getElem?_map_some _ hi) (Typed.subst hS θ he)
  | _, _, .seq ha hb => .seq (Typed.subst hS θ ha) (Typed.subst hS θ hb)
  | _, _, .prim hes hp => .prim (TypedL.subst hS θ hes) (hp.subst θ)
  | _, _, .call θ' hs hes => by
    have h := TypedL.subst hS θ hes
    rw [List.map_map] at h
    have h' := Typed.call (fun j => (θ' j).subst θ) hs
      (by rw [← VTy.substL_comp]; simpa [Function.comp_def] using h)
    rwa [← VTy.subst_comp] at h'
  | _, _, .ite hc ht he => .ite (Typed.subst hS θ hc) (Typed.subst hS θ ht) (Typed.subst hS θ he)
  | _, _, .forE hi hit hfl hb => by
    simpa using Typed.forE (getElem?_map_some _ hi) (by simpa using Typed.subst hS θ hit)
      (Typed.subst hS θ hfl) (Typed.subst hS θ hb)
  | _, _, .loop hb => by simpa using Typed.loop (Typed.subst hS θ hb)
  | _, _, .brk => .brk
  | _, _, .ret he => .ret (Typed.subst hS θ he)
  | _, _, .print he => by simpa using Typed.print (by simpa using Typed.subst hS θ he)
  | _, _, .sub he hs => .sub (Typed.subst hS θ he) (VTy.sub_subst θ _ _ hs)
  | _, _, .heap_new hc ht hes => by
    have h := TypedL.subst hS θ hes
    rw [VTy.map_inst_subst] at h
    simpa using Typed.heap_new hc ht h
  | _, _, .heap_get he hft => by
    have h := Typed.subst hS θ he
    simp only [VTy.subst_ref] at h
    exact .heap_get h (hft.subst θ)
  | _, _, .heap_set he hft hv => by
    have h := Typed.subst hS θ he
    simp only [VTy.subst_ref] at h
    exact .heap_set h (hft.subst θ) (Typed.subst hS θ hv)
  | _, _, .heap_tag he => by
    have h := Typed.subst hS θ he
    simp only [VTy.subst_ref] at h
    simpa using Typed.heap_tag h
  | _, _, .heap_isTag he => by
    have h := Typed.subst hS θ he
    simp only [VTy.subst_ref] at h
    simpa using Typed.heap_isTag h
theorem TypedL.subst (hS : S.ClosedProtos) (θ : Nat → VTy) : ∀ {es ts}, TypedL S Γ ρ es ts →
    TypedL S (Γ.map (VTy.subst θ)) (ρ.subst θ) es (ts.map (VTy.subst θ))
  | _, _, .nil => .nil
  | _, _, .cons he hes => .cons (Typed.subst hS θ he) (TypedL.subst hS θ hes)
end
end

theorem hasTy_int {v} (h : hasTy Ξ v .int = true) : ∃ a, v = .int a := by
  cases v <;> simp_all [hasTy]
theorem hasTy_logic {v} (h : hasTy Ξ v .logic = true) : ∃ b, v = .logic b := by
  cases v <;> simp_all [hasTy]
theorem hasTy_char {v} (h : hasTy Ξ v .char = true) : ∃ c, v = .char c ∧ c < 256 := by
  cases v <;> simp_all [hasTy]
theorem hasTy_arr {v t} (h : hasTy Ξ v (.arr t) = true) : ∃ vs, v = .arr vs ∧ allTy Ξ vs.toList t = true := by
  cases v <;> simp_all [hasTy]
theorem hasTy_tup {v ts} (h : hasTy Ξ v (.tup ts) = true) : ∃ vs, v = .tup vs ∧ allTys Ξ vs ts = true := by
  cases v <;> simp_all [hasTy]
theorem hasTy_opt {v t} (h : hasTy Ξ v (.opt t) = true) : v = .none ∨ ∃ w, v = .some w ∧ hasTy Ξ w t = true := by
  cases v <;> simp_all [hasTy]

/-! ### Primitives -/

theorem ResOK_ofInt {ρ} (i : Int) : ResOK Ξ .int ρ (Res.ofInt i) := by
  unfold Res.ofInt; split <;> simp [ResOK, hasTy]

theorem flattenArrs_typed : ∀ {xss : List Value} {t}, allTy Ξ xss (.arr t) = true →
    ∃ vs, flattenArrs xss = some vs ∧ allTy Ξ vs t = true
  | [], _, _ => ⟨[], rfl, rfl⟩
  | x :: xss, t, h => by
    simp only [allTy, Bool.and_eq_true] at h
    obtain ⟨xs, rfl, hx⟩ := hasTy_arr h.1
    obtain ⟨vs, hvs, hv⟩ := flattenArrs_typed h.2
    exact ⟨xs.toList ++ vs, by simp [flattenArrs, hvs], allTy_append hx hv⟩

theorem rangeVals_typed (a b : Int) : allTy Ξ (rangeVals a b) .int = true := by
  rw [allTy_iff]; intro v hv
  simp only [rangeVals, List.mem_map] at hv
  obtain ⟨_, _, rfl⟩ := hv; rfl

theorem asBytes_of_char : ∀ {vs : List Value}, allTy Ξ vs .char = true → (asBytes vs).isSome
  | [], _ => rfl
  | v :: vs, h => by
    simp only [allTy, Bool.and_eq_true] at h
    obtain ⟨c, rfl, _⟩ := hasTy_char h.1
    have := asBytes_of_char h.2
    simp only [asBytes]
    rcases hb : asBytes vs with _ | bs
    · simp [hb] at this
    · simp

theorem intBytes_typed (i : Int) : allTy Ξ ((intBytes i).map Value.char) .char = true := by
  rw [allTy_iff]; intro v hv
  simp only [intBytes, List.map_map, List.mem_map] at hv
  obtain ⟨b, _, rfl⟩ := hv
  have := b.toNat_lt
  show hasTy Ξ (Value.char b.toNat) VTy.char = true
  simp only [hasTy, decide_eq_true_eq]; omega

theorem hasTy_float {v} (h : hasTy Ξ v .float = true) : ∃ b, v = .float b := by
  cases v <;> simp_all [hasTy]

theorem ofString_typed (s : String) : hasTy Ξ (Value.ofString s) VTy.str = true := by
  simp only [Value.ofString, hasTy, VTy.str, List.toList_toArray]
  rw [allTy_iff]; intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨b, _, rfl⟩ := hv
  have := b.toNat_lt
  show hasTy Ξ (Value.char b.toNat) VTy.char = true
  simp only [hasTy, decide_eq_true_eq]; omega

theorem toStr_typed {v t} (ht : PrimTy .toStr [t] VTy.str) (hv : hasTy Ξ v t = true) {ρ} :
    ResOK Ξ VTy.str ρ (toStrValue v) := by
  cases ht with
  | toStrInt => obtain ⟨a, rfl⟩ := hasTy_int hv; simp [toStrValue, ResOK, hasTy, VTy.str, intBytes_typed]
  | toStrChar =>
    obtain ⟨c, rfl, hc⟩ := hasTy_char hv
    simp [toStrValue, ResOK, hasTy, VTy.str, allTy, hc]
  | toStrStr =>
    obtain ⟨vs, rfl, hvs⟩ := hasTy_arr hv
    have := asBytes_of_char hvs
    simp only [toStrValue]
    rcases hb : asBytes vs.toList with _ | bs
    · simp [hb] at this
    · simp [ResOK, hasTy, VTy.str, hvs]
  | toStrFloat =>
    obtain ⟨b, rfl⟩ := hasTy_float hv
    simp only [toStrValue, ResOK]
    exact ofString_typed _

theorem cmpRes_ok {b : Bool} {v : Value} {τ ρ} (h : hasTy Ξ v τ = true) : ResOK Ξ τ ρ (cmpRes b v) := by
  unfold cmpRes; split <;> simp [ResOK, h]

/-- **Primitives are type safe**: a primitive applied to arguments of its
    parameter types gives a value of its result type, or fails, or raises an
    error other than a type error. -/
theorem prim_typed {op ts τ ρ} {vs : List Value} (hp : PrimTy op ts τ) (hv : allTys Ξ vs ts = true) :
    ResOK Ξ τ ρ (op.apply vs) := by
  cases hp with
  | arith hop =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl⟩ := hasTy_int hv.1; obtain ⟨y, rfl⟩ := hasTy_int hv.2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.apply] <;>
        (try split) <;> first | exact ResOK_ofInt _ | simp [ResOK]
  | unary hop =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl⟩ := hasTy_int hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
      rcases hop with rfl | rfl <;> exact ResOK_ofInt _
  | cmpInt hop =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl⟩ := hasTy_int hv.1; obtain ⟨y, rfl⟩ := hasTy_int hv.2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl <;> exact cmpRes_ok rfl
  | cmpChar hop =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl, hx⟩ := hasTy_char hv.1; obtain ⟨y, rfl, _⟩ := hasTy_char hv.2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl <;> exact cmpRes_ok (by simp [hasTy, hx])
  | farith hop =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl⟩ := hasTy_float hv.1; obtain ⟨y, rfl⟩ := hasTy_float hv.2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Prim.apply, ResOK, hasTy]
  | funary hop =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl⟩ := hasTy_float hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
      rcases hop with rfl | rfl <;> simp [Prim.apply, ResOK, hasTy]
  | fcmp hop =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl⟩ := hasTy_float hv.1; obtain ⟨y, rfl⟩ := hasTy_float hv.2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl <;> exact cmpRes_ok (by simp [hasTy])
  | fofInt =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl⟩ := hasTy_int hv
      simp [Prim.apply, ResOK, hasTy]
  | fofBits =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl⟩ := hasTy_int hv
      simp [Prim.apply, ResOK, hasTy]
  | ftoInt hop =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl⟩ := hasTy_float hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl <;> simp only [Prim.apply, VFloat.toIntRes] <;>
        (repeat' split) <;> simp [ResOK, hasTy]
  | toStrFloat =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      exact toStr_typed .toStrFloat hv
  | eq =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals exact cmpRes_ok hv.1
  | ne =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals exact cmpRes_ok hv.1
  | queryLogic =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨b, rfl⟩ := hasTy_logic hv
      simp only [Prim.apply]; split <;> simp [ResOK, hasTy]
  | queryOpt =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      rcases hasTy_opt hv with rfl | ⟨w, rfl, hw⟩
      · simp [Prim.apply, ResOK]
      · simp [Prim.apply, ResOK, hw]
  | mkArr hall => simp [Prim.apply, ResOK, hasTy, allTy_of_allTys hall hv]
  | mkTup => simp [Prim.apply, ResOK, hasTy, hv]
  | mkSome =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals simp [Prim.apply, ResOK, hasTy, hv]
  | concat =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨xs, rfl, hx⟩ := hasTy_arr hv.1; obtain ⟨ys, rfl, hy⟩ := hasTy_arr hv.2
      simp [Prim.apply, ResOK, hasTy, allTy_append hx hy]
  | index =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨xs, rfl, hx⟩ := hasTy_arr hv.1; obtain ⟨i, rfl⟩ := hasTy_int hv.2
      simp only [Prim.apply]
      split
      · split
        · next v hv' => exact allTy_get hx (by simpa using hv')
        · simp [ResOK]
      · simp [ResOK]
  | len =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨xs, rfl, _⟩ := hasTy_arr hv
      simp [Prim.apply, ResOK, hasTy]
  | arrSet =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨xs, rfl, hx⟩ := hasTy_arr hv.1; obtain ⟨i, rfl⟩ := hasTy_int hv.2.1
      simp only [Prim.apply]
      split
      · simp [ResOK, hasTy, allTy_set hx hv.2.2]
      · simp [ResOK]
  | flatten =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨xss, rfl, hx⟩ := hasTy_arr hv
      obtain ⟨ws, hws, hw⟩ := flattenArrs_typed hx
      simp [Prim.apply, hws, ResOK, hasTy, hw]
  | range =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨x, rfl⟩ := hasTy_int hv.1; obtain ⟨y, rfl⟩ := hasTy_int hv.2
      simp [Prim.apply, ResOK, hasTy, rangeVals_typed]
  | tupGet hk =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      obtain ⟨ws, rfl, hw⟩ := hasTy_tup hv
      obtain ⟨w, hwk, hwt⟩ := allTys_get hw hk
      simp [Prim.apply, hwk, ResOK, hwt]
  | toStrInt =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      exact toStr_typed .toStrInt hv
  | toStrChar =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      exact toStr_typed .toStrChar hv
  | toStrStr =>
    rcases vs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals
      exact toStr_typed .toStrStr hv
  | fail =>
    rcases vs with _ | ⟨_, _⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals simp [Prim.apply, ResOK]
  | userErr =>
    rcases vs with _ | ⟨_, _⟩ <;> simp only [allTys, Bool.and_eq_true, Bool.false_eq_true, and_false, and_true] at hv
    all_goals simp [Prim.apply, ResOK]

/-! ### The heap (#29, #39) -/

theorem lt_of_getElem?_some {α} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : i < l.length := by
  rcases Nat.lt_or_ge i l.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

theorem prefix_getElem? {α} {l l' : List α} (h : l <+: l') {a : Nat} {t : α} (ha : l[a]? = some t) :
    l'[a]? = some t := by
  obtain ⟨r, rfl⟩ := h
  rw [List.getElem?_append_left (lt_of_getElem?_some ha)]; exact ha

mutual
/-- Typings survive the growth of the heap typing: objects are only added. -/
theorem hasTy_mono {Ξ₁ Ξ₂ : HeapTy} (hx : Ξ₁ <+: Ξ₂) : ∀ (t : VTy) (v : Value),
    hasTy Ξ₁ v t = true → hasTy Ξ₂ v t = true
  | .int, v, hv | .logic, v, hv | .char, v, hv | .float, v, hv | .var _, v, hv => by cases v <;> simp_all [hasTy]
  | .arr t, v, hv => by
    cases v
    case arr vs =>
      simp only [hasTy] at hv ⊢
      rw [allTy_iff] at hv ⊢
      exact fun w hw => hasTy_mono hx t w (hv w hw)
    all_goals simp [hasTy] at hv
  | .opt t, v, hv => by
    cases v
    case none => simp [hasTy]
    case some w => simp only [hasTy] at hv ⊢; exact hasTy_mono hx t w hv
    all_goals simp [hasTy] at hv
  | .tup ts, v, hv => by
    cases v
    case tup vs => simp only [hasTy] at hv ⊢; exact allTys_mono hx ts vs hv
    all_goals simp [hasTy] at hv
  | .ref ts args, v, hv => by
    cases v
    case ref a =>
      simp only [hasTy] at hv ⊢
      rcases ha : Ξ₁[a]? with _ | ⟨t, args'⟩
      · simp [ha] at hv
      · simp only [ha] at hv; simp only [prefix_getElem? hx ha]; exact hv
    all_goals simp [hasTy] at hv
theorem allTys_mono {Ξ₁ Ξ₂ : HeapTy} (hx : Ξ₁ <+: Ξ₂) : ∀ (ts : List VTy) (vs : List Value),
    allTys Ξ₁ vs ts = true → allTys Ξ₂ vs ts = true
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [allTys] at h
  | t :: ts, v :: vs, h => by
    simp only [allTys, Bool.and_eq_true] at h ⊢
    exact ⟨hasTy_mono hx t v h.1, allTys_mono hx ts vs h.2⟩
end

theorem allTy_mono {Ξ₁ Ξ₂ : HeapTy} (hx : Ξ₁ <+: Ξ₂) {vs : List Value} {t : VTy}
    (h : allTy Ξ₁ vs t = true) : allTy Ξ₂ vs t = true := by
  rw [allTy_iff] at h ⊢; exact fun w hw => hasTy_mono hx t w (h w hw)

theorem ResOK_mono {Ξ₁ Ξ₂ : HeapTy} (hx : Ξ₁ <+: Ξ₂) {τ ρ : VTy} {r : Res}
    (h : ResOK Ξ₁ τ ρ r) : ResOK Ξ₂ τ ρ r := by
  cases r <;> simp only [ResOK] at h ⊢
  · exact hasTy_mono hx _ _ h
  · exact hasTy_mono hx _ _ h
  all_goals exact h

theorem LResOK_mono {Ξ₁ Ξ₂ : HeapTy} (hx : Ξ₁ <+: Ξ₂) {ts : List VTy} {ρ : VTy} {r : LRes}
    (h : LResOK Ξ₁ ts ρ r) : LResOK Ξ₂ ts ρ r := by
  cases r <;> simp only [LResOK] at h ⊢
  · exact allTys_mono hx _ _ h
  · exact ⟨ResOK_mono hx h.1, h.2⟩

/-- A value of a reference type is a reference to an object of a class in
    the set, whose type arguments extend the type's. -/
theorem hasTy_ref {v : Value} {ts : List Nat} {args : List VTy} (h : hasTy Ξ v (.ref ts args) = true) :
    ∃ a t args', v = .ref a ∧ Ξ[a]? = some (t, args') ∧ t ∈ ts ∧ args <+: args' := by
  cases v with
  | ref a =>
    simp only [hasTy] at h
    rcases ha : Ξ[a]? with _ | ⟨t, args'⟩
    · simp [ha] at h
    · simp only [ha, Bool.and_eq_true, List.isPrefixOf_iff_prefix] at h
      exact ⟨a, t, args', rfl, ha, by simpa using h.1, h.2⟩
  | _ => simp [hasTy] at h

/-- A reference, in a well-typed heap: the object it refers to, of a class
    in its type, whose fields have the class's types at its arguments. -/
theorem ref_arg {S : Sigs} {h : Array Obj} (hH : HeapOK S Ξ h) {v : Value} {ts : List Nat}
    {args : List VTy} (hv : hasTy Ξ v (.ref ts args) = true) :
    ∃ a o args' fs, v = .ref a ∧ h[a]? = some o ∧ o.tag ∈ ts ∧ Ξ[a]? = some (o.tag, args') ∧
      args <+: args' ∧ S.classes[o.tag]? = some fs ∧ allTys Ξ o.fields (fs.map (VTy.inst args')) = true := by
  obtain ⟨a, t, args', rfl, hta, htin, hpre⟩ := hasTy_ref hv
  have hlt : a < h.size := by rw [← hH.1]; exact lt_of_getElem?_some hta
  have ho : h[a]? = some h[a] := by simp [hlt]
  obtain ⟨args'', fs, hΞ, hc, hf⟩ := hH.2.1 a h[a] (by rw [Array.getElem?_toList]; exact ho)
  rw [hta] at hΞ
  simp only [Option.some.injEq, Prod.mk.injEq] at hΞ
  obtain ⟨rfl, rfl⟩ := hΞ
  exact ⟨a, h[a], args', fs, rfl, ho, htin, hta, hpre, hc, hf⟩

/-- The empty heap is typed by the empty heap typing, if there are no prototypes. -/
theorem HeapOK.empty {S : Sigs} (hp : S.protos = []) : HeapOK S [] #[] :=
  ⟨rfl, fun a o h => by simp at h, by simp [hp]⟩

theorem HeapOK.new {S : Sigs} {h : Array Obj} (hH : HeapOK S Ξ h) {t : Nat} {args : List VTy}
    {vs : List Value} {fs : List VTy} (hc : S.classes[t]? = some fs)
    (hvs : allTys Ξ vs (fs.map (VTy.inst args)) = true) :
    HeapOK S (Ξ ++ [(t, args)]) (h.push ⟨t, vs⟩) := by
  have hx : Ξ <+: Ξ ++ [(t, args)] := List.prefix_append _ _
  have hl : h.toList.length = Ξ.length := by rw [Array.length_toList, hH.1]
  refine ⟨by simp [hH.1], fun a o ho => ?_, hH.2.2.trans hx⟩
  rw [Array.toList_push] at ho
  rcases Nat.lt_or_ge a h.toList.length with ha | ha
  · rw [List.getElem?_append_left ha] at ho
    obtain ⟨args', fs', hΞ, hc', hf⟩ := hH.2.1 a o ho
    exact ⟨args', fs', prefix_getElem? hx hΞ, hc', allTys_mono hx _ _ hf⟩
  · rw [List.getElem?_append_right ha] at ho
    rcases hk : a - h.toList.length with _ | k
    · rw [hk] at ho
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ho; subst ho
      have : a = Ξ.length := by omega
      subst this
      exact ⟨args, fs, by simp, hc, allTys_mono hx _ _ hvs⟩
    · rw [hk] at ho; simp at ho

theorem HeapOK.set {S : Sigs} {h : Array Obj} (hH : HeapOK S Ξ h) {a k : Nat} {o : Obj} {v : Value}
    {args fs : List VTy} {τ : VTy} (ho₀ : h[a]? = some o) (hΞ : Ξ[a]? = some (o.tag, args))
    (hc : S.classes[o.tag]? = some fs) (hk : (fs.map (VTy.inst args))[k]? = some τ)
    (hv : hasTy Ξ v τ = true) :
    HeapOK S Ξ (h.setIfInBounds a { o with fields := o.fields.set k v }) := by
  have ho : h.toList[a]? = some o := by rw [Array.getElem?_toList]; exact ho₀
  refine ⟨by simp [hH.1], fun b ob hob => ?_, hH.2.2⟩
  rw [Array.toList_setIfInBounds] at hob
  by_cases hab : b = a
  · subst hab
    obtain ⟨ha, -⟩ := List.getElem?_eq_some_iff.mp ho
    rw [List.getElem?_set_self ha] at hob
    simp only [Option.some.injEq] at hob; subst hob
    obtain ⟨args', fs', hΞ', hc', hf⟩ := hH.2.1 b o ho
    rw [hΞ] at hΞ'; simp only [Option.some.injEq, Prod.mk.injEq] at hΞ'; obtain ⟨-, rfl⟩ := hΞ'
    rw [hc] at hc'; simp only [Option.some.injEq] at hc'; subst hc'
    exact ⟨_, _, hΞ, hc, allTys_set hf hk hv⟩
  · rw [List.getElem?_set_ne (Ne.symm hab)] at hob
    exact hH.2.1 b ob hob

/-! ### Frames -/

theorem ResOK_retype {σ τ ρ : VTy} {r : Res} (hr : r.isOk = false) (h : ResOK Ξ σ ρ r) : ResOK Ξ τ ρ r := by
  cases r <;> simp_all [ResOK]

theorem readSlot_typed {Γ : List VTy} {s : St} {i : Nat} {τ : VTy} (hf : FrameOK Ξ Γ s.fr)
    (hi : Γ[i]? = some τ) : ∃ v, readSlot s i = .ok v ∧ hasTy Ξ v τ = true := by
  obtain ⟨v, hv, ht⟩ := allTys_get hf hi
  exact ⟨v, by simp [readSlot, hv], ht⟩

theorem writeSlot_typed {Γ : List VTy} {s : St} {i : Nat} {τ : VTy} {v : Value} (hf : FrameOK Ξ Γ s.fr)
    (hi : Γ[i]? = some τ) (hv : hasTy Ξ v τ = true) :
    ∃ s', writeSlot s i v = some s' ∧ FrameOK Ξ Γ s'.fr ∧ s'.g = s.g := by
  have hlen := allTys_length hf
  have hlt : i < s.fr.length := by rw [hlen]; exact lt_of_getElem?_some hi
  refine ⟨{ s with fr := s.fr.set i v }, by simp [writeSlot, hlt], ?_, rfl⟩
  exact allTys_set hf hi hv

theorem take_set_succ {α} : ∀ (l : List α) (k : Nat) (d : α), k < l.length →
    (l.set k d).take (k + 1) = l.take k ++ [d]
  | [], _, _, h => absurd h (by simp)
  | _ :: _, 0, _, _ => by simp
  | a :: l, k + 1, d, h => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append, List.cons.injEq, true_and]
    exact take_set_succ l k d (by simpa using h)

theorem DefaultEL.length {S a Γ} : ∀ {ds ts}, DefaultEL S a Γ ds ts → ds.length = ts.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [DefaultEL.length h]

/-- What evaluating a default expression from state `s` (with heap typing
    `Ξ`) gives: a value of its type, in a state with the same frame and a
    well-typed, grown heap. -/
def DefaultOK (S : Sigs) (Ξ : HeapTy) (s : St) (t : VTy) (x : Res × St) : Prop :=
  ∃ v s' Ξ', x = (.ok v, s') ∧ s'.fr = s.fr ∧ HeapOK S Ξ' s'.g.heap ∧ Ξ <+: Ξ' ∧ hasTy Ξ' v t = true

def DefaultLOK (S : Sigs) (Ξ : HeapTy) (s : St) (ts : List VTy) (x : LRes × St) : Prop :=
  ∃ vs s' Ξ', x = (.ok vs, s') ∧ s'.fr = s.fr ∧ HeapOK S Ξ' s'.g.heap ∧ Ξ <+: Ξ' ∧
    allTys Ξ' vs ts = true

mutual
/-- A default expression evaluates without failing to a value of its type
    under `θ`, once the parameters (the first `a` slots) hold values of their
    types under `θ`: it keeps the frame, and may only add well-typed objects. -/
theorem DefaultE.eval_ok {P : Prog} {S : Sigs} (hS : S.ClosedProtos) {a : Nat} {Γ : List VTy}
    {θ : Nat → VTy} :
    ∀ {d t} (n : Nat) {s : St} {Ξ : HeapTy} {x}, DefaultE S a Γ d t →
      allTys Ξ (s.fr.take a) ((Γ.take a).map (VTy.subst θ)) = true →
      HeapOK S Ξ s.g.heap → eval P n s d = some x → DefaultOK S Ξ s (t.subst θ) x
  | _, _, 0, _, _, _, _, _, _, h => by simp [eval] at h
  | _, _, _ + 1, _, _, _, .lit hv, _, hH, h => by
    simp only [eval, Option.some.injEq] at h
    exact ⟨_, _, _, h.symm, rfl, hH, List.prefix_refl _, hasTy_mono hH.2.2 _ _ (hasTy_subst hS θ _ _ hv)⟩
  | _, _, _ + 1, s, Ξ, _, .param (i := i) hi hΓ, hp, hH, h => by
    simp only [eval, Option.some.injEq] at h
    have hΓ' : ((Γ.take a).map (VTy.subst θ))[i]? = some (VTy.subst θ _) :=
      getElem?_map_some _ (by rw [List.getElem?_take_of_lt hi]; exact hΓ)
    obtain ⟨v, hv, ht⟩ := allTys_get hp hΓ'
    rw [List.getElem?_take_of_lt hi] at hv
    exact ⟨v, s, Ξ, by rw [← h]; simp [readSlot, hv], rfl, hH, List.prefix_refl _, ht⟩
  | _, _, n + 1, s, _, _, .tup hds, hp, hH, h => by
    simp only [eval] at h
    rcases bindL_some h with ⟨vs, s1, hx, hk⟩ | ⟨r1, s1, hx, rfl⟩
    · obtain ⟨vs', s1', Ξ1, hvs, hfr, hH1, hx1, ht⟩ := DefaultEL.eval_ok hS n hds hp hH hx
      simp only [Option.some.injEq, Prod.mk.injEq, LRes.ok.injEq] at hvs
      obtain ⟨rfl, rfl⟩ := hvs
      split at hk
      · simp at hk
      simp only [Option.some.injEq] at hk
      exact ⟨_, s1, Ξ1, by rw [← hk]; rfl, hfr, hH1, hx1, by simpa [hasTy] using ht⟩
    · obtain ⟨vs', s1', Ξ1, hvs, -⟩ := DefaultEL.eval_ok hS n hds hp hH hx
      simp at hvs
  | _, _, n + 1, s, _, _, .new (t := t) (args := args) hc ht hds, hp, hH, h => by
    simp only [eval] at h
    rcases bindL_some h with ⟨vs, s1, hx, hk⟩ | ⟨r1, s1, hx, rfl⟩
    · obtain ⟨vs', s1', Ξ1, hvs, hfr, hH1, hx1, hft⟩ := DefaultEL.eval_ok hS n hds hp hH hx
      simp only [Option.some.injEq, Prod.mk.injEq, LRes.ok.injEq] at hvs
      obtain ⟨rfl, rfl⟩ := hvs
      simp only [Option.some.injEq] at hk
      rw [VTy.map_inst_subst] at hft
      refine ⟨_, _, _, hk.symm, hfr, HeapOK.new hH1 hc hft, hx1.trans (List.prefix_append _ _), ?_⟩
      simp [HeapOp.apply, hasTy, ← hH1.1, ht]
    · obtain ⟨vs', s1', Ξ1, hvs, -⟩ := DefaultEL.eval_ok hS n hds hp hH hx
      simp at hvs
  | _, _, n, s, _, _, .sub hd hsub, hp, hH, h => by
    obtain ⟨v, s', Ξ', hx, hfr, hH', hx', hv⟩ := DefaultE.eval_ok hS n hd hp hH h
    exact ⟨v, s', Ξ', hx, hfr, hH', hx', hasTy_sub _ _ _ (VTy.sub_subst θ _ _ hsub) hv⟩
theorem DefaultEL.eval_ok {P : Prog} {S : Sigs} (hS : S.ClosedProtos) {a : Nat} {Γ : List VTy}
    {θ : Nat → VTy} :
    ∀ {ds ts} (n : Nat) {s : St} {Ξ : HeapTy} {x}, DefaultEL S a Γ ds ts →
      allTys Ξ (s.fr.take a) ((Γ.take a).map (VTy.subst θ)) = true →
      HeapOK S Ξ s.g.heap → evalList P n s ds = some x → DefaultLOK S Ξ s (ts.map (VTy.subst θ)) x
  | _, _, 0, _, _, _, _, _, _, h => by simp [evalList] at h
  | _, _, _ + 1, s, Ξ, _, .nil, _, hH, h => by
    simp only [evalList, Option.some.injEq] at h
    exact ⟨[], s, Ξ, h.symm, rfl, hH, List.prefix_refl _, rfl⟩
  | _, _, n + 1, s, _, _, .cons hd hds, hp, hH, h => by
    simp only [evalList] at h
    split at h
    · simp at h
    · next v s1 hx =>
      obtain ⟨v', s1', Ξ1, hv, hfr1, hH1, hx1, ht⟩ := DefaultE.eval_ok hS n hd hp hH hx
      simp only [Option.some.injEq, Prod.mk.injEq, Res.ok.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      have hp1 : allTys Ξ1 (s1.fr.take a) ((Γ.take a).map (VTy.subst θ)) = true := by
        rw [hfr1]; exact allTys_mono hx1 _ _ hp
      split at h
      · simp at h
      · next vs s2 hxs =>
        obtain ⟨vs', s2', Ξ2, hvs, hfr2, hH2, hx2, hts⟩ := DefaultEL.eval_ok hS n hds hp1 hH1 hxs
        simp only [Option.some.injEq, Prod.mk.injEq, LRes.ok.injEq] at hvs
        obtain ⟨rfl, rfl⟩ := hvs
        simp only [Option.some.injEq] at h
        exact ⟨_, s2, Ξ2, h.symm, hfr2.trans hfr1, hH2, hx1.trans hx2,
          by simp [allTys, hasTy_mono hx2 _ _ ht, hts]⟩
      · next r s2 hxs =>
        obtain ⟨vs', s2', Ξ2, hvs, -⟩ := DefaultEL.eval_ok hS n hds hp1 hH1 hxs
        simp at hvs
    all_goals
      next hx =>
      obtain ⟨v', s1', Ξ1, hv, -⟩ := DefaultE.eval_ok hS n hd hp hH hx
      simp at hv
end

/-- Running the initialisation prefix: what is left is the rest of the body,
    from a frame whose slots `k, …` hold values of their types under `θ`
    and a well-typed, grown heap, with no more fuel. -/
theorem eval_initPrefixE {P : Prog} {S : Sigs} (hS : S.ClosedProtos) {a : Nat} {Γ : List VTy}
    {θ : Nat → VTy} :
    ∀ (ds : List Expr) (ts : List VTy) (n k : Nat) (fr : List Value) (o : Glob) (Ξ : HeapTy) (b : Expr)
      (x : Res × St), DefaultEL S a Γ ds ts → a ≤ k → k + ds.length = fr.length →
      allTys Ξ (fr.take a) ((Γ.take a).map (VTy.subst θ)) = true → HeapOK S Ξ o.heap →
      eval P n ⟨fr, o⟩ (initPrefixE k ds b) = some x →
      ∃ m ≤ n, ∃ ws o' Ξ', allTys Ξ' ws (ts.map (VTy.subst θ)) = true ∧ HeapOK S Ξ' o'.heap ∧
        Ξ <+: Ξ' ∧ eval P m ⟨fr.take k ++ ws, o'⟩ b = some x
  | [], _, n, k, fr, o, Ξ, b, x, .nil, _, hl, _, hH, h => by
    refine ⟨n, Nat.le_refl _, [], o, Ξ, rfl, hH, List.prefix_refl _, ?_⟩
    simp only [List.length_nil, Nat.add_zero] at hl
    rw [List.take_of_length_le (by omega), List.append_nil]
    simpa [initPrefixE] using h
  | d :: ds, t :: ts, n, k, fr, o, Ξ, b, x, .cons hd hds, hak, hl, hp, hH, h => by
    have hk : k < fr.length := by simp at hl; omega
    match n, h with
    | n + 1, h =>
      simp only [initPrefixE, eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk'⟩ | ⟨r1, s1, hx, hr, _⟩
      · match n, hx, hk' with
        | n' + 1, hx, hk' =>
          simp only [eval] at hx
          rcases bindR_some hx with ⟨w, s2, hw, hw'⟩ | ⟨r2, s2, hw, hr2, hw'⟩
          · obtain ⟨w', s2', Ξ2, hwv, hfr2, hH2, hx2, hwt⟩ :=
              DefaultE.eval_ok (s := ⟨fr, o⟩) hS n' hd hp hH hw
            simp only [Option.some.injEq, Prod.mk.injEq, Res.ok.injEq] at hwv
            obtain ⟨rfl, rfl⟩ := hwv
            obtain ⟨fr2, o2⟩ := s2
            simp only at hfr2; subst fr2
            simp only [writeSlot, hk, ite_true, Option.some.injEq, Prod.mk.injEq, Res.ok.injEq] at hw'
            obtain ⟨rfl, rfl⟩ := hw'
            have hp' : allTys Ξ2 ((fr.set k w).take a) ((Γ.take a).map (VTy.subst θ)) = true := by
              rw [List.take_set_of_le hak]; exact allTys_mono hx2 _ _ hp
            obtain ⟨m, hm, ws, o', Ξ', hws, hH', hx', hm'⟩ :=
              eval_initPrefixE hS ds ts (n' + 1) (k + 1) (fr.set k w) o2 Ξ2 b x hds (by omega)
                (by simp at hl ⊢; omega) hp' hH2 hk'
            refine ⟨m, by omega, w :: ws, o', Ξ', by simp [allTys, hasTy_mono hx' _ _ hwt, hws], hH',
              hx2.trans hx', ?_⟩
            rw [take_set_succ fr k _ hk] at hm'
            simpa using hm'
          · obtain ⟨w', s2', -, hwv, -⟩ := DefaultE.eval_ok (s := ⟨fr, o⟩) hS n' hd hp hH hw
            simp only [Option.some.injEq, Prod.mk.injEq] at hwv
            obtain ⟨rfl, -⟩ := hwv
            simp at hr2
        | 0, hx, _ => simp [eval] at hx
      · match n, hx with
        | n' + 1, hx =>
          simp only [eval] at hx
          rcases bindR_some hx with ⟨w, s2, hw, hw'⟩ | ⟨r2, s2, hw, hr2, hw'⟩
          · obtain ⟨w', s2', -, hwv, hfr2, -⟩ := DefaultE.eval_ok (s := ⟨fr, o⟩) hS n' hd hp hH hw
            simp only [Option.some.injEq, Prod.mk.injEq, Res.ok.injEq] at hwv
            obtain ⟨rfl, rfl⟩ := hwv
            obtain ⟨fr2, o2⟩ := s2
            simp only at hfr2; subst fr2
            simp only [writeSlot, hk, ite_true, Option.some.injEq, Prod.mk.injEq] at hw'
            obtain ⟨rfl, -⟩ := hw'
            simp at hr
          · obtain ⟨w', s2', -, hwv, -⟩ := DefaultE.eval_ok (s := ⟨fr, o⟩) hS n' hd hp hH hw
            simp only [Option.some.injEq, Prod.mk.injEq] at hwv
            obtain ⟨rfl, -⟩ := hwv
            simp at hr2
        | 0, hx => simp [eval] at hx

/-! ### Preservation, by strong induction on fuel -/

section
variable (P : Prog) (S : Sigs)

/-- Evaluation keeps the frame typed and the heap well typed, its outcome
    has its type, and the heap only grows: some extension of the heap
    typing types all of it. -/
def StmtE (n : Nat) : Prop :=
  ∀ (s : St) (e : Expr) (x : Res × St) (Γ : List VTy) (ρ τ : VTy) {Ξ : HeapTy}, eval P n s e = some x →
    Typed S Γ ρ e τ → FrameOK Ξ Γ s.fr → HeapOK S Ξ s.g.heap →
    ∃ Ξ', FrameOK Ξ' Γ x.2.fr ∧ ResOK Ξ' τ ρ x.1 ∧ HeapOK S Ξ' x.2.g.heap ∧ Ξ <+: Ξ'

def StmtL (n : Nat) : Prop :=
  ∀ (s : St) (es : List Expr) (x : LRes × St) (Γ : List VTy) (ρ : VTy) (ts : List VTy) {Ξ : HeapTy},
    evalList P n s es = some x → TypedL S Γ ρ es ts → FrameOK Ξ Γ s.fr → HeapOK S Ξ s.g.heap →
    ∃ Ξ', FrameOK Ξ' Γ x.2.fr ∧ LResOK Ξ' ts ρ x.1 ∧ HeapOK S Ξ' x.2.g.heap ∧ Ξ <+: Ξ'

def StmtF (n : Nat) : Prop :=
  ∀ (i : Nat) (filt body : Expr) (s : St) (vs acc : List Value) (x : Res × St) (Γ : List VTy)
    (ρ τe σ τb : VTy) {Ξ : HeapTy}, evalFor P n i filt body s vs acc = some x → Γ[i]? = some τe →
    allTy Ξ vs τe = true → allTy Ξ acc τb = true → Typed S Γ ρ filt σ →
    Typed S Γ ρ body τb → FrameOK Ξ Γ s.fr → HeapOK S Ξ s.g.heap →
    ∃ Ξ', FrameOK Ξ' Γ x.2.fr ∧ ResOK Ξ' (.arr τb) ρ x.1 ∧ HeapOK S Ξ' x.2.g.heap ∧ Ξ <+: Ξ'
end

theorem hasTy_void : hasTy Ξ Value.void VTy.void = true := rfl

/-- The rules of `Typed` but subsumption, over `Typed` premises: the last
    step of a derivation, once subsumption is peeled off (`stepE_d`). -/
inductive TypedR (S : Sigs) (Γ : List VTy) (ρ : VTy) : Expr → VTy → Prop
  | lit {v τ} : hasTy S.protos v τ = true → TypedR S Γ ρ (.lit v) τ
  | local {i τ} : Γ[i]? = some τ → TypedR S Γ ρ (.local i) τ
  | assign {i e τ} : Γ[i]? = some τ → Typed S Γ ρ e τ → TypedR S Γ ρ (.assign i e) τ
  | seq {a b σ τ} : Typed S Γ ρ a σ → Typed S Γ ρ b τ → TypedR S Γ ρ (.seq a b) τ
  | prim {op es ts τ} : TypedL S Γ ρ es ts → PrimTy op ts τ → TypedR S Γ ρ (.prim op es) τ
  | call {f es ps τ} (θ : Nat → VTy) : S.fns[f]? = some (ps, τ) → TypedL S Γ ρ es (ps.map (VTy.subst θ)) →
      TypedR S Γ ρ (.call f es) (τ.subst θ)
  | ite {c t e σ τ} : Typed S Γ ρ c σ → Typed S Γ ρ t τ → Typed S Γ ρ e τ →
      TypedR S Γ ρ (.ite c t e) τ
  | forE {i it filt body τe σ τb} : Γ[i]? = some τe → Typed S Γ ρ it (.arr τe) →
      Typed S Γ ρ filt σ → Typed S Γ ρ body τb → TypedR S Γ ρ (.forE i it filt body) (.arr τb)
  | loop {b σ} : Typed S Γ ρ b σ → TypedR S Γ ρ (.loop b) VTy.void
  | brk {τ} : TypedR S Γ ρ .brk τ
  | ret {e τ} : Typed S Γ ρ e ρ → TypedR S Γ ρ (.ret e) τ
  | print {e} : Typed S Γ ρ e VTy.str → TypedR S Γ ρ (.print e) VTy.void
  | heap_new {t es fs ts args} : S.classes[t]? = some fs → t ∈ ts →
      TypedL S Γ ρ es (fs.map (VTy.inst args)) → TypedR S Γ ρ (.heap (.new t) es) (.ref ts args)
  | heap_get {k e ts args τ} : Typed S Γ ρ e (.ref ts args) → FieldTy S ts args k τ →
      TypedR S Γ ρ (.heap (.get k) [e]) τ
  | heap_set {k e v ts args τ} : Typed S Γ ρ e (.ref ts args) → FieldTy S ts args k τ →
      Typed S Γ ρ v τ → TypedR S Γ ρ (.heap (.set k) [e, v]) τ
  | heap_tag {e ts args} : Typed S Γ ρ e (.ref ts args) → TypedR S Γ ρ (.heap .tag [e]) .int
  | heap_isTag {e ts args us} : Typed S Γ ρ e (.ref ts args) →
      TypedR S Γ ρ (.heap (.isTag us) [e]) (.ref us args)

/-- The arguments of a heap operation are typed. -/
theorem heap_args {S : Sigs} {Γ : List VTy} {ρ : VTy} {op : HeapOp} {es : List Expr} {τ : VTy}
    (ht : TypedR S Γ ρ (.heap op es) τ) : ∃ ts, TypedL S Γ ρ es ts := by
  cases ht with
  | heap_new _ _ hes => exact ⟨_, hes⟩
  | heap_get he _ => exact ⟨_, .cons he .nil⟩
  | heap_set he _ hv => exact ⟨_, .cons he (.cons hv .nil)⟩
  | heap_tag he => exact ⟨_, .cons he .nil⟩
  | heap_isTag he => exact ⟨_, .cons he .nil⟩

/-- The conclusion of `StmtE`. -/
def StmtE.post (S : Sigs) (Ξ : HeapTy) (x : Res × St) (Γ : List VTy) (ρ τ : VTy) : Prop :=
  ∃ Ξ', FrameOK Ξ' Γ x.2.fr ∧ ResOK Ξ' τ ρ x.1 ∧ HeapOK S Ξ' x.2.g.heap ∧ Ξ <+: Ξ'

/-- Preservation for a derivation that does not end with subsumption. -/
theorem stepE_rule {P : Prog} {S : Sigs} (hP : ProgTyped P S) (n : Nat)
    (ih : ∀ m ≤ n, StmtE P S m ∧ StmtL P S m ∧ StmtF P S m) {s : St} {e : Expr} {x : Res × St}
    {Γ : List VTy} {ρ τ : VTy} {Ξ : HeapTy} (h : eval P (n + 1) s e = some x) (ht : TypedR S Γ ρ e τ)
    (hf : FrameOK Ξ Γ s.fr) (hH : HeapOK S Ξ s.g.heap) :
    StmtE.post S Ξ x Γ ρ τ := by
  have IE := (ih n (Nat.le_refl _)).1
  have IL := (ih n (Nat.le_refl _)).2.1
  have IF := (ih n (Nat.le_refl _)).2.2
  unfold StmtE.post
  cases e with
  | lit v =>
    simp only [eval, Option.some.injEq] at h; subst h
    cases ht with
    | lit hv => exact ⟨_, hf, hasTy_mono hH.2.2 _ _ hv, hH, List.prefix_refl _⟩
  | «local» i =>
    simp only [eval, Option.some.injEq] at h; subst h
    cases ht with
    | «local» hi =>
      obtain ⟨v, hv, ht⟩ := readSlot_typed hf hi
      exact ⟨_, hf, by simp [hv, ResOK, ht], hH, List.prefix_refl _⟩
  | assign i e =>
    cases ht with
    | assign hi he =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk⟩ | ⟨r1, s1, hx, hr, rfl⟩
      · obtain ⟨Ξ1, hf1, hv, hH1, hp1⟩ := IE _ _ _ _ _ _ hx he hf hH
        obtain ⟨s2, hw, hf2, hg⟩ := writeSlot_typed hf1 hi hv
        simp only [hw, Option.some.injEq] at hk; subst hk
        exact ⟨_, hf2, hv, by rw [hg]; exact hH1, hp1⟩
      · exact IE _ _ _ _ _ _ hx he hf hH
  | seq a b =>
    cases ht with
    | seq ha hb =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk⟩ | ⟨r1, s1, hx, hr, rfl⟩
      · obtain ⟨Ξ1, hf1, -, hH1, hp1⟩ := IE _ _ _ _ _ _ hx ha hf hH
        obtain ⟨Ξ2, hf2, hr2, hH2, hp2⟩ := IE _ _ _ _ _ _ hk hb hf1 hH1
        exact ⟨_, hf2, hr2, hH2, hp1.trans hp2⟩
      · obtain ⟨Ξ1, hf1, hr1, hH1, hp1⟩ := IE _ _ _ _ _ _ hx ha hf hH
        exact ⟨_, hf1, ResOK_retype hr hr1, hH1, hp1⟩
  | prim op es =>
    cases ht with
    | prim hes hp =>
      simp only [eval] at h
      rcases bindL_some h with ⟨vs, s1, hx, hk⟩ | ⟨r1, s1, hx, rfl⟩
      · split at hk
        · simp at hk
        simp only [Option.some.injEq] at hk; subst hk
        obtain ⟨Ξ1, hf1, hvs, hH1, hp1⟩ := IL _ _ _ _ _ _ hx hes hf hH
        exact ⟨_, hf1, prim_typed hp hvs, hH1, hp1⟩
      · obtain ⟨Ξ1, hf1, ⟨hr1, hok⟩, hH1, hp1⟩ := IL _ _ _ _ _ _ hx hes hf hH
        exact ⟨_, hf1, ResOK_retype hok hr1, hH1, hp1⟩
  | call f es =>
    cases ht with
    | call θ hsig hes =>
      rename_i ps τ₀
      simp only [eval] at h
      rcases bindL_some h with ⟨vs, s1, hx, hk⟩ | ⟨r1, s1, hx, rfl⟩
      · obtain ⟨Ξ1, hf1, hvs, hH1, hp1⟩ := IL _ _ _ _ _ _ hx hes hf hH
        split at hk
        · simp only [Option.some.injEq] at hk; subst hk
          exact ⟨_, hf1, by simp [ResOK], hH1, hp1⟩
        · next fn hc =>
          split at hk
          · simp at hk
          · next r2 s2 hb =>
            simp only [Option.some.injEq] at hk; subst hk
            -- the callee
            unfold Prog.callable at hc
            split at hc
            · next fn' hfn =>
              split at hc
              · next har =>
                simp only [Option.some.injEq] at hc; subst hc
                obtain ⟨Γ', hft⟩ := hP.2.2.1 f fn' ps τ₀ hfn hsig
                obtain ⟨b, ds, hbody, hds, hbt⟩ := hft.body
                have hlen := allTys_length hvs
                rw [hbody] at hb
                have hfr : (frameOf fn' vs).take fn'.arity = vs := by
                  simp [frameOf, ← har]
                -- the arguments have the callee's parameter types under θ
                have hp : allTys Ξ1 ((frameOf fn' vs).take fn'.arity)
                    ((Γ'.take fn'.arity).map (VTy.subst θ)) = true := by
                  rw [hfr, hft.params]; exact hvs
                have hl : fn'.arity + ds.length = (frameOf fn' vs).length := by
                  rw [DefaultEL.length hds]
                  simp [frameOf, hft.slots]; omega
                obtain ⟨m, hm, ws, o', Ξo, hws, hHo, hxo, hm'⟩ :=
                  eval_initPrefixE hP.1 _ _ _ _ _ _ _ _ _ hds (Nat.le_refl _) hl hp hH1 hb
                rw [hfr] at hm'
                -- so the callee runs from a frame typed by its slot types under θ
                have hf' : FrameOK Ξo (Γ'.map (VTy.subst θ)) (vs ++ ws) := by
                  have := allTys_append (allTys_mono hxo _ _ hvs) hws
                  rw [← hft.params, ← List.map_append, List.take_append_drop] at this
                  exact this
                obtain ⟨Ξ2, -, hres, hH2, hp2⟩ :=
                  ((ih m hm).1) ⟨vs ++ ws, o'⟩ _ _ _ _ _ hm' (Typed.subst hP.1 θ hbt) hf' hHo
                -- the caller's frame survives the callee's allocations
                have hp12 : Ξ1 <+: Ξ2 := hxo.trans hp2
                refine ⟨_, allTys_mono hp12 _ _ hf1, ?_, hH2, hp1.trans hp12⟩
                cases r2 <;> simp_all [retOf, ResOK]
              · simp at hc
            · simp at hc
      · obtain ⟨Ξ1, hf1, ⟨hr1, hok⟩, hH1, hp1⟩ := IL _ _ _ _ _ _ hx hes hf hH
        exact ⟨_, hf1, ResOK_retype hok hr1, hH1, hp1⟩
  | ite c t e =>
    cases ht with
    | ite hc htt hte =>
      simp only [eval] at h
      split at h
      · simp at h
      · next v s1 hx =>
        obtain ⟨Ξ1, hf1, -, hH1, hp1⟩ := IE _ _ _ _ _ _ hx hc hf hH
        obtain ⟨Ξ2, hf2, hr2, hH2, hp2⟩ := IE _ _ _ _ _ _ h htt hf1 hH1
        exact ⟨_, hf2, hr2, hH2, hp1.trans hp2⟩
      · exact IE _ _ _ _ _ _ h hte hf hH
      all_goals
        rename_i hx
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨Ξ1, hf1, hr1, hH1, hp1⟩ := IE _ _ _ _ _ _ hx hc hf hH
        exact ⟨_, hf1, ResOK_retype rfl hr1, hH1, hp1⟩
  | forE i it filt body =>
    cases ht with
    | forE hi hit hfl hbd =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk⟩ | ⟨r1, s1, hx, hr, rfl⟩
      · obtain ⟨Ξ1, hf1, hv, hH1, hp1⟩ := IE _ _ _ _ _ _ hx hit hf hH
        obtain ⟨vs, rfl, hvs⟩ := hasTy_arr hv
        obtain ⟨Ξ2, hf2, hr2, hH2, hp2⟩ := IF _ _ _ _ _ _ _ _ _ _ _ _ hk hi hvs rfl hfl hbd hf1 hH1
        exact ⟨_, hf2, hr2, hH2, hp1.trans hp2⟩
      · obtain ⟨Ξ1, hf1, hr1, hH1, hp1⟩ := IE _ _ _ _ _ _ hx hit hf hH
        exact ⟨_, hf1, ResOK_retype hr hr1, hH1, hp1⟩
  | loop b =>
    cases ht with
    | loop hb =>
      simp only [eval] at h
      split at h
      · simp at h
      · next v s1 hx =>
        obtain ⟨Ξ1, hf1, -, hH1, hp1⟩ := IE _ _ _ _ _ _ hx hb hf hH
        obtain ⟨Ξ2, hf2, hr2, hH2, hp2⟩ := IE _ _ _ _ _ _ h (.loop hb) hf1 hH1
        exact ⟨_, hf2, hr2, hH2, hp1.trans hp2⟩
      · next s1 hx =>
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨Ξ1, hf1, -, hH1, hp1⟩ := IE _ _ _ _ _ _ hx hb hf hH
        exact ⟨_, hf1, hasTy_void, hH1, hp1⟩
      all_goals
        rename_i hx
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨Ξ1, hf1, hr1, hH1, hp1⟩ := IE _ _ _ _ _ _ hx hb hf hH
        exact ⟨_, hf1, ResOK_retype rfl hr1, hH1, hp1⟩
  | brk =>
    simp only [eval, Option.some.injEq] at h; subst h
    exact ⟨_, hf, trivial, hH, List.prefix_refl _⟩
  | ret e =>
    cases ht with
    | ret he =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk⟩ | ⟨r1, s1, hx, hr, rfl⟩
      · simp only [Option.some.injEq] at hk; subst hk
        obtain ⟨Ξ1, hf1, hv, hH1, hp1⟩ := IE _ _ _ _ _ _ hx he hf hH
        exact ⟨_, hf1, hv, hH1, hp1⟩
      · obtain ⟨Ξ1, hf1, hr1, hH1, hp1⟩ := IE _ _ _ _ _ _ hx he hf hH
        exact ⟨_, hf1, ResOK_retype hr hr1, hH1, hp1⟩
  | heap op es =>
    simp only [eval, St.heapStep_eq] at h
    rcases bindL_some h with ⟨vs, s1, hx, hk⟩ | ⟨r1, s1, hx, rfl⟩
    · simp only [Option.some.injEq] at hk; subst hk
      cases ht with
      | heap_new hc htt hes =>
        rename_i t fs ts args
        obtain ⟨Ξ1, hf1, hvs, hH1, hp1⟩ := IL _ _ _ _ _ _ hx hes hf hH
        have hx2 : Ξ1 <+: Ξ1 ++ [(t, args)] := List.prefix_append _ _
        have happ : (HeapOp.new t).apply vs s1.g =
            (.ok (.ref s1.g.heap.size), { s1.g with heap := s1.g.heap.push ⟨t, vs⟩ }) := rfl
        simp only [happ]
        refine ⟨_, allTys_mono hx2 _ _ hf1, ?_, HeapOK.new hH1 hc hvs, hp1.trans hx2⟩
        simp [ResOK, hasTy, ← hH1.1, htt]
      | heap_get he hft =>
        rename_i k e₀ ts args
        obtain ⟨Ξ1, hf1, hvs, hH1, hp1⟩ := IL _ _ _ _ _ _ hx (.cons he .nil) hf hH
        obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ hasTy Ξ1 v (.ref ts args) = true := by
          rcases vs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp [LResOK, allTys] at hvs
          exact ⟨v, rfl, hvs⟩
        obtain ⟨a, o, args', fs, rfl, ho, htin, -, hpre, hc, hfs⟩ := ref_arg hH1 hv
        obtain ⟨fs', f, hc', hk, hvb, hfτ⟩ := hft _ htin
        rw [hc] at hc'; simp only [Option.some.injEq] at hc'; subst hc'
        have hk' : (fs.map (VTy.inst args'))[k]? = some τ := by
          rw [List.getElem?_map, hk, Option.map_some, VTy.inst_prefix hpre hvb, hfτ]
        obtain ⟨w, hw, hwt⟩ := allTys_get hfs hk'
        have happ : (HeapOp.get k).apply [.ref a] s1.g = (.ok w, s1.g) := by
          simp [HeapOp.apply, ho, hw]
        simp only [happ]
        exact ⟨_, hf1, hwt, hH1, hp1⟩
      | heap_set he hft hv₀ =>
        rename_i k e₀ v₀ ts args
        obtain ⟨Ξ1, hf1, hvs, hH1, hp1⟩ := IL _ _ _ _ _ _ hx (.cons he (.cons hv₀ .nil)) hf hH
        obtain ⟨r, w, rfl, hr, hw⟩ : ∃ r w, vs = [r, w] ∧ hasTy Ξ1 r (.ref ts args) = true ∧
            hasTy Ξ1 w τ = true := by
          rcases vs with _ | ⟨r, _ | ⟨w, _ | ⟨_, _⟩⟩⟩ <;> simp [LResOK, allTys] at hvs
          exact ⟨r, w, rfl, hvs.1, hvs.2⟩
        obtain ⟨a, o, args', fs, rfl, ho, htin, hΞa, hpre, hc, hfs⟩ := ref_arg hH1 hr
        obtain ⟨fs', f, hc', hk, hvb, hfτ⟩ := hft _ htin
        rw [hc] at hc'; simp only [Option.some.injEq] at hc'; subst hc'
        have hk' : (fs.map (VTy.inst args'))[k]? = some τ := by
          rw [List.getElem?_map, hk, Option.map_some, VTy.inst_prefix hpre hvb, hfτ]
        have hklt : k < o.fields.length := by rw [allTys_length hfs]; exact lt_of_getElem?_some hk'
        have happ : (HeapOp.set k).apply [.ref a, w] s1.g =
            (.ok w, { s1.g with heap := s1.g.heap.setIfInBounds a { o with fields := o.fields.set k w } }) := by
          simp [HeapOp.apply, ho, hklt]
        simp only [happ]
        exact ⟨_, hf1, hw, HeapOK.set hH1 ho hΞa hc hk' hw, hp1⟩
      | heap_tag he =>
        rename_i e₀ ts args
        obtain ⟨Ξ1, hf1, hvs, hH1, hp1⟩ := IL _ _ _ _ _ _ hx (.cons he .nil) hf hH
        obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ hasTy Ξ1 v (.ref ts args) = true := by
          rcases vs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp [LResOK, allTys] at hvs
          exact ⟨v, rfl, hvs⟩
        obtain ⟨a, o, -, -, rfl, ho, -⟩ := ref_arg hH1 hv
        have happ : HeapOp.tag.apply [.ref a] s1.g = (.ok (.int o.tag), s1.g) := by
          simp [HeapOp.apply, ho]
        simp only [happ]
        exact ⟨_, hf1, rfl, hH1, hp1⟩
      | heap_isTag he =>
        rename_i e₀ ts args us
        obtain ⟨Ξ1, hf1, hvs, hH1, hp1⟩ := IL _ _ _ _ _ _ hx (.cons he .nil) hf hH
        obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ hasTy Ξ1 v (.ref ts args) = true := by
          rcases vs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp [LResOK, allTys] at hvs
          exact ⟨v, rfl, hvs⟩
        obtain ⟨a, o, args', fs, rfl, ho, -, hΞa, hpre, -⟩ := ref_arg hH1 hv
        have happ : (HeapOp.isTag us).apply [.ref a] s1.g =
            (if us.contains o.tag then .ok (.ref a) else .fail, s1.g) := by
          simp [HeapOp.apply, ho]
        simp only [happ]
        refine ⟨_, hf1, ?_, hH1, hp1⟩
        split
        · next hu =>
          show hasTy Ξ1 (.ref a) (.ref us args) = true
          simp only [hasTy, hΞa, Bool.and_eq_true, List.isPrefixOf_iff_prefix]
          exact ⟨hu, hpre⟩
        · trivial
    · obtain ⟨_, hes⟩ := heap_args ht
      obtain ⟨Ξ1, hf1, ⟨hr1, hok⟩, hH1, hp1⟩ := IL _ _ _ _ _ _ hx hes hf hH
      exact ⟨_, hf1, ResOK_retype hok hr1, hH1, hp1⟩
  | print e =>
    cases ht with
    | print he =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk⟩ | ⟨r1, s1, hx, hr, rfl⟩
      · obtain ⟨Ξ1, hf1, hv, hH1, hp1⟩ := IE _ _ _ _ _ _ hx he hf hH
        obtain ⟨vs, rfl, hvs⟩ := hasTy_arr hv
        have hb := asBytes_of_char hvs
        split at hk
        · simp only [Option.some.injEq] at hk; subst hk
          exact ⟨_, hf1, hasTy_void, hH1, hp1⟩
        · next hp =>
          simp only [printBytes] at hp
          rcases hab : asBytes vs.toList with _ | bs
          · simp [hab] at hb
          · simp [hab] at hp
      · obtain ⟨Ξ1, hf1, hr1, hH1, hp1⟩ := IE _ _ _ _ _ _ hx he hf hH
        exact ⟨_, hf1, ResOK_retype hr hr1, hH1, hp1⟩

mutual
/-- Preservation at fuel `n + 1`, by recursion on the typing derivation for
    subsumption (the rest is `stepE_rule`). -/
theorem stepE_d {P : Prog} {S : Sigs} (hP : ProgTyped P S) (n : Nat)
    (ih : ∀ m ≤ n, StmtE P S m ∧ StmtL P S m ∧ StmtF P S m) {Γ : List VTy} {ρ : VTy} :
    ∀ {e : Expr} {τ : VTy}, Typed S Γ ρ e τ → ∀ {s : St} {x : Res × St}, eval P (n + 1) s e = some x →
      ∀ {Ξ : HeapTy}, FrameOK Ξ Γ s.fr → HeapOK S Ξ s.g.heap → StmtE.post S Ξ x Γ ρ τ
  | _, _, .sub ht hs, _, _, h, _, hf, hH => by
    obtain ⟨Ξ', a, b, c, d⟩ := stepE_d hP n ih ht h hf hH
    exact ⟨Ξ', a, ResOK_sub hs b, c, d⟩
  | _, _, .lit a, _, _, h, _, hf, hH => stepE_rule hP n ih h (.lit a) hf hH
  | _, _, .local a, _, _, h, _, hf, hH => stepE_rule hP n ih h (.local a) hf hH
  | _, _, .assign a b, _, _, h, _, hf, hH => stepE_rule hP n ih h (.assign a b) hf hH
  | _, _, .seq a b, _, _, h, _, hf, hH => stepE_rule hP n ih h (.seq a b) hf hH
  | _, _, .prim a b, _, _, h, _, hf, hH => stepE_rule hP n ih h (.prim a b) hf hH
  | _, _, .call θ a b, _, _, h, _, hf, hH => stepE_rule hP n ih h (.call θ a b) hf hH
  | _, _, .ite a b c, _, _, h, _, hf, hH => stepE_rule hP n ih h (.ite a b c) hf hH
  | _, _, .forE a b c d, _, _, h, _, hf, hH => stepE_rule hP n ih h (.forE a b c d) hf hH
  | _, _, .loop a, _, _, h, _, hf, hH => stepE_rule hP n ih h (.loop a) hf hH
  | _, _, .brk, _, _, h, _, hf, hH => stepE_rule hP n ih h .brk hf hH
  | _, _, .ret a, _, _, h, _, hf, hH => stepE_rule hP n ih h (.ret a) hf hH
  | _, _, .print a, _, _, h, _, hf, hH => stepE_rule hP n ih h (.print a) hf hH
  | _, _, .heap_new a b c, _, _, h, _, hf, hH => stepE_rule hP n ih h (.heap_new a b c) hf hH
  | _, _, .heap_get a b, _, _, h, _, hf, hH => stepE_rule hP n ih h (.heap_get a b) hf hH
  | _, _, .heap_set a b c, _, _, h, _, hf, hH => stepE_rule hP n ih h (.heap_set a b c) hf hH
  | _, _, .heap_tag a, _, _, h, _, hf, hH => stepE_rule hP n ih h (.heap_tag a) hf hH
  | _, _, .heap_isTag a, _, _, h, _, hf, hH => stepE_rule hP n ih h (.heap_isTag a) hf hH
/-- `stepE_d`'s partner over `TypedL` (Lean recurses structurally on a
    mutual inductive only through a mutual block). -/
theorem stepE_dL {S : Sigs} {Γ : List VTy} {ρ : VTy} :
    ∀ {es : List Expr} {ts : List VTy}, TypedL S Γ ρ es ts → True
  | _, _, _ => trivial
end

theorem stepE {P : Prog} {S : Sigs} (hP : ProgTyped P S) (n : Nat)
    (ih : ∀ m ≤ n, StmtE P S m ∧ StmtL P S m ∧ StmtF P S m) : StmtE P S (n + 1) :=
  fun _ _ _ _ _ _ _ h ht hf hH => stepE_d hP n ih ht h hf hH

theorem stepL {P : Prog} {S : Sigs} (n : Nat)
    (ih : ∀ m ≤ n, StmtE P S m ∧ StmtL P S m ∧ StmtF P S m) : StmtL P S (n + 1) := by
  have IE := (ih n (Nat.le_refl _)).1
  have IL := (ih n (Nat.le_refl _)).2.1
  intro s es x Γ ρ ts Ξ h ht hf hH
  cases es with
  | nil =>
    simp only [evalList, Option.some.injEq] at h; subst h
    cases ht with | nil => exact ⟨_, hf, rfl, hH, List.prefix_refl _⟩
  | cons e es =>
    cases ht with
    | cons he hes =>
      simp only [evalList] at h
      split at h
      · simp at h
      · next v s1 hx =>
        obtain ⟨Ξ1, hf1, hv, hH1, hp1⟩ := IE _ _ _ _ _ _ hx he hf hH
        split at h
        · simp at h
        · next vs s2 hxs =>
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨Ξ2, hf2, hvs, hH2, hp2⟩ := IL _ _ _ _ _ _ hxs hes hf1 hH1
          have hv0 : hasTy Ξ1 v _ = true := hv
          have hv' : hasTy Ξ2 v _ = true := hasTy_mono hp2 _ _ hv0
          have hvs' : allTys Ξ2 vs _ = true := hvs
          exact ⟨_, hf2, by simp [LResOK, allTys, hv', hvs'], hH2, hp1.trans hp2⟩
        · next r s2 hxs =>
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨Ξ2, hf2, hr2, hH2, hp2⟩ := IL _ _ _ _ _ _ hxs hes hf1 hH1
          exact ⟨_, hf2, hr2, hH2, hp1.trans hp2⟩
      all_goals
        rename_i hx
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨Ξ1, hf1, hr1, hH1, hp1⟩ := IE _ _ _ _ _ _ hx he hf hH
        exact ⟨_, hf1, ⟨ResOK_retype rfl hr1, rfl⟩, hH1, hp1⟩

theorem stepF {P : Prog} {S : Sigs} (n : Nat)
    (ih : ∀ m ≤ n, StmtE P S m ∧ StmtL P S m ∧ StmtF P S m) : StmtF P S (n + 1) := by
  have IE := (ih n (Nat.le_refl _)).1
  have IF := (ih n (Nat.le_refl _)).2.2
  intro i filt body s vs acc x Γ ρ τe σ τb Ξ h hi hvs hacc hfl hbd hf hH
  cases vs with
  | nil =>
    simp only [evalFor, Option.some.injEq] at h; subst h
    exact ⟨_, hf, by simp [ResOK, hasTy, allTy_reverse hacc], hH, List.prefix_refl _⟩
  | cons v vs =>
    simp only [allTy, Bool.and_eq_true] at hvs
    simp only [evalFor] at h
    obtain ⟨s0, hw, hf0, hg0⟩ := writeSlot_typed hf hi hvs.1
    have hH0 : HeapOK S Ξ s0.g.heap := by rw [hg0]; exact hH
    simp only [hw] at h
    split at h
    · simp at h
    · exact IF _ _ _ _ _ _ _ _ _ _ _ _ h hi hvs.2 hacc hfl hbd hf0 hH0
    · next u s1 hx =>
      obtain ⟨Ξ1, hf1, _, hH1, hp1⟩ := IE _ _ _ _ _ _ hx hfl hf0 hH0
      split at h
      · simp at h
      · next w s2 hb =>
        obtain ⟨Ξ2, hf2, hw2, hH2, hp2⟩ := IE _ _ _ _ _ _ hb hbd hf1 hH1
        have hw2' : hasTy Ξ2 w τb = true := hw2
        have hp02 : Ξ <+: Ξ2 := hp1.trans hp2
        obtain ⟨Ξ3, hf3, hr3, hH3, hp3⟩ := IF _ _ _ _ _ _ _ _ _ _ _ _ h hi (allTy_mono hp02 hvs.2)
          (by simp [allTy, hw2', allTy_mono hp02 hacc]) hfl hbd hf2 hH2
        exact ⟨_, hf3, hr3, hH3, hp02.trans hp3⟩
      all_goals
        rename_i hb
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨Ξ2, hf2, hr2, hH2, hp2⟩ := IE _ _ _ _ _ _ hb hbd hf1 hH1
        exact ⟨_, hf2, ResOK_retype rfl hr2, hH2, hp1.trans hp2⟩
    all_goals
      rename_i hx
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨Ξ1, hf1, hr1, hH1, hp1⟩ := IE _ _ _ _ _ _ hx hfl hf0 hH0
      exact ⟨_, hf1, ResOK_retype rfl hr1, hH1, hp1⟩

theorem typed_all {P : Prog} {S : Sigs} (hP : ProgTyped P S) :
    ∀ n, ∀ m ≤ n, StmtE P S m ∧ StmtL P S m ∧ StmtF P S m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have : m = 0 := by omega
    subst this
    refine ⟨?_, ?_, ?_⟩
    · intro _ _ _ _ _ _ _ h; simp [eval] at h
    · intro _ _ _ _ _ _ _ h; simp [evalList] at h
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [evalFor] at h
  | succ n ih =>
    intro m hm
    by_cases hmn : m ≤ n
    · exact ih m hmn
    · have : m = n + 1 := by omega
      subst this
      exact ⟨stepE hP n ih, stepL n ih, stepF n ih⟩

/-! ### Type safety -/

/-- **Preservation.** A typed expression evaluated from a well-typed frame
    and a well-typed heap (under a heap typing `Ξ`) leaves a well-typed
    frame and heap, under an extension of `Ξ` (the heap only grows), and its
    outcome is a value of its type, a `return` of a value of the function's
    type, or anything but a type error. -/
theorem Eval.typed {P : Prog} {S : Sigs} (hP : ProgTyped P S) {s e r s' Γ ρ τ} {Ξ : HeapTy}
    (h : Eval P s e r s') (ht : Typed S Γ ρ e τ) (hf : FrameOK Ξ Γ s.fr)
    (hH : HeapOK S Ξ s.g.heap) :
    ∃ Ξ', FrameOK Ξ' Γ s'.fr ∧ ResOK Ξ' τ ρ r ∧ HeapOK S Ξ' s'.g.heap ∧ Ξ <+: Ξ' := by
  obtain ⟨n, hn⟩ := eval_iff.mp h
  exact (typed_all hP n n (Nat.le_refl _)).1 s e (r, s') Γ ρ τ hn ht hf hH

/-- Literals evaluate to their values, in place. -/
theorem EvalList.lits {P : Prog} : ∀ {vs : List Value} {s lr s'}, EvalList P s (vs.map .lit) lr s' →
    lr = .ok vs ∧ s' = s
  | [], _, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | v :: vs, _, _, _, h => by
    cases h with
    | cons_ok h₁ h₂ =>
      cases h₁
      obtain ⟨h₃, rfl⟩ := EvalList.lits h₂
      cases h₃
      exact ⟨rfl, rfl⟩
    | cons_stop h₁ hr => cases h₁; simp at hr
    | cons_stop_tail h₁ h₂ => cases h₁; obtain ⟨h, -⟩ := EvalList.lits h₂; cases h

/-- **The prelude** (#37): after it, the heap has the prototypes appended,
    and nothing else has changed. -/
theorem Eval.of_protoPrelude {P : Prog} : ∀ (objs : List (Nat × List Value)) {s : St} {e : Expr} {r s'},
    Eval P s (protoPrelude objs e) r s' →
    Eval P ⟨s.fr, { s.g with heap := s.g.heap ++ protoObjs objs }⟩ e r s'
  | [], s, e, r, s', h => by simpa [protoPrelude, protoObjs] using h
  | (t, vs) :: rest, s, e, r, s', h => by
    simp only [protoPrelude] at h
    cases h with
    | seq_ok hn hrest =>
      cases hn with
      | heap_ok hl =>
        obtain ⟨h₁, rfl⟩ := EvalList.lits hl
        cases h₁
        have := Eval.of_protoPrelude rest hrest
        simpa [HeapOp.apply, protoObjs, List.append_assoc] using this
      | heap_stop hl => obtain ⟨h₁, -⟩ := EvalList.lits hl; cases h₁
    | seq_stop hn hr =>
      cases hn with
      | heap_ok hl =>
        obtain ⟨h₁, rfl⟩ := EvalList.lits hl
        cases h₁
        simp [HeapOp.apply] at hr
      | heap_stop hl => obtain ⟨h₁, -⟩ := EvalList.lits hl; cases h₁

/-- **Type safety of programs.** In a typed program whose `Main` takes no
    parameters and returns `τ`, no run raises a type error, and every run
    ends with a well-typed heap in which a successful run's value has type
    `τ`. -/
theorem Runs.typed {P : Prog} {S : Sigs} (hP : ProgTyped P S) {τ r out}
    (hm : S.fns[P.main]? = some ([], τ)) (h : Runs P r out) :
    r ≠ .err .type ∧ ∃ fr heap, Eval P Prog.initSt (.call P.main []) r ⟨fr, ⟨out, heap⟩⟩ ∧
      ∃ Ξ, HeapOK S Ξ heap ∧ ∀ v, r = .ok v → hasTy Ξ v τ = true := by
  obtain ⟨fr, heap, h⟩ := h
  rcases hP.2.2.2 with hnil | ⟨fn, objs, m, hfn, har, hns, hbody, hHo, hsm⟩
  · -- no prototypes: the empty heap is well typed
    have ht : Typed S [] τ (.call P.main []) τ := by
      simpa [VTy.subst_id] using Typed.call (Γ := []) (ρ := τ) VTy.var hm .nil
    obtain ⟨Ξ, -, hr, hH, -⟩ := Eval.typed (Ξ := []) hP h ht rfl (HeapOK.empty hnil)
    refine ⟨?_, fr, heap, h, Ξ, hH, ?_⟩
    · intro he; subst he; exact hr rfl
    · intro v hv; subst hv; exact hr
  · -- `Main` is the prelude, then a call of `m` from the heap of prototypes
    have hm' : S.fns[m]? = some ([], τ) := hsm.trans hm
    have ht : Typed S [] τ (.call m []) τ := by
      simpa [VTy.subst_id] using Typed.call (Γ := []) (ρ := τ) VTy.var hm' .nil
    suffices key : ∀ {s'}, Eval P Prog.initSt (.call P.main []) r s' →
        r ≠ .err .type ∧ ∃ Ξ, HeapOK S Ξ s'.g.heap ∧ ∀ v, r = .ok v → hasTy Ξ v τ = true by
      obtain ⟨h1, Ξ, h2, h3⟩ := key h
      exact ⟨h1, fr, heap, h, Ξ, h2, h3⟩
    intro s' hcall
    cases hcall with
    | @call_ok _ _ _ _ _ _ _ r₀ hl hc hb =>
      cases hl
      have hc' : P.callable P.main ([] : List Value).length = some fn := by simp [Prog.callable, hfn, har]
      rw [hc'] at hc; cases hc
      rw [hbody] at hb
      have hb' := Eval.of_protoPrelude objs hb
      have hfr : frameOf fn [] = [] := by simp [frameOf, har, hns]
      simp only [Prog.initSt, hfr, Array.empty_append] at hb'
      obtain ⟨Ξ, -, hr, hH, -⟩ := Eval.typed hP hb' ht rfl hHo
      refine ⟨?_, Ξ, hH, ?_⟩
      · intro he
        cases r₀ <;> simp_all [retOf, ResOK]
      · intro v hv
        cases r₀ <;> simp_all [retOf, ResOK]
    | call_bad hl hc =>
      cases hl
      have hc' : P.callable P.main 0 = some fn := by simp [Prog.callable, hfn, har]
      simp [hc'] at hc
    | call_stop hl => cases hl

end OpenVerse
