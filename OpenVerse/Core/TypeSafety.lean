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

/-! ### Values -/

theorem allTy_iff {vs : List Value} {t : VTy} : allTy vs t = true ↔ ∀ v ∈ vs, hasTy v t = true := by
  induction vs with
  | nil => simp [allTy]
  | cons v vs ih => simp [allTy, ih]

theorem allTys_length : ∀ {vs : List Value} {ts : List VTy}, allTys vs ts = true → vs.length = ts.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [allTys, Bool.and_eq_true] at h
    simp [allTys_length h.2]
  | [], _ :: _, h => by simp [allTys] at h
  | _ :: _, [], h => by simp [allTys] at h

theorem allTys_get : ∀ {vs : List Value} {ts : List VTy} {i : Nat} {t : VTy}, allTys vs ts = true → ts[i]? = some t →
    ∃ v, vs[i]? = some v ∧ hasTy v t = true
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

theorem allTys_set : ∀ {vs : List Value} {ts : List VTy} {i : Nat} {t : VTy} {v : Value}, allTys vs ts = true → ts[i]? = some t →
    hasTy v t = true → allTys (vs.set i v) ts = true
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

theorem allTys_append : ∀ {a : List Value} {c : List VTy} {b d}, allTys a c = true → allTys b d = true →
    allTys (a ++ b) (c ++ d) = true
  | [], [], _, _, _, h => by simpa using h
  | _ :: _, _ :: _, _, _, h, h' => by
    simp only [allTys, Bool.and_eq_true] at h
    simp [allTys, h.1, allTys_append h.2 h']
  | [], _ :: _, _, _, h, _ => by simp [allTys] at h
  | _ :: _, [], _, _, h, _ => by simp [allTys] at h

theorem allTy_of_allTys : ∀ {vs : List Value} {ts : List VTy} {t}, (∀ u ∈ ts, u = t) →
    allTys vs ts = true → allTy vs t = true
  | [], [], _, _, _ => rfl
  | _ :: _, u :: _, t, hu, h => by
    simp only [allTys, Bool.and_eq_true] at h
    have : u = t := hu u (by simp)
    subst this
    simp [allTy, h.1, allTy_of_allTys (fun w hw => hu w (by simp [hw])) h.2]
  | [], _ :: _, _, _, h => by simp [allTys] at h
  | _ :: _, [], _, _, h => by simp [allTys] at h

theorem allTy_append {a b : List Value} {t} (ha : allTy a t = true) (hb : allTy b t = true) :
    allTy (a ++ b) t = true := by
  rw [allTy_iff] at *; intro v hv; rcases List.mem_append.mp hv with h | h; exact ha v h; exact hb v h

theorem allTy_get {xs : List Value} {t : VTy} {n : Nat} {v : Value} (h : allTy xs t = true) (hv : xs[n]? = some v) :
    hasTy v t = true :=
  allTy_iff.mp h v (List.mem_of_getElem? hv)

theorem allTy_set {xs : List Value} {t : VTy} {n : Nat} {v : Value} (h : allTy xs t = true) (hv : hasTy v t = true) :
    allTy (xs.set n v) t = true := by
  rw [allTy_iff] at *
  intro w hw
  rcases List.mem_or_eq_of_mem_set hw with h' | h'
  · exact h w h'
  · subst h'; exact hv

theorem allTy_reverse {xs : List Value} {t} (h : allTy xs t = true) : allTy xs.reverse t = true := by
  rw [allTy_iff] at *; intro v hv; exact h v (List.mem_reverse.mp hv)

mutual
theorem hasTy_default : ∀ t : VTy, hasTy t.default t = true
  | .int => rfl
  | .logic => rfl
  | .char => by decide
  | .arr _ => rfl
  | .opt _ => rfl
  | .tup ts => by simp only [VTy.default, hasTy]; exact allTys_defaults ts
theorem allTys_defaults : ∀ ts : List VTy, allTys (VTy.defaults ts) ts = true
  | [] => rfl
  | t :: ts => by simp [VTy.defaults, allTys, hasTy_default t, allTys_defaults ts]
end

theorem hasTy_int {v} (h : hasTy v .int = true) : ∃ a, v = .int a := by
  cases v <;> simp_all [hasTy]
theorem hasTy_logic {v} (h : hasTy v .logic = true) : ∃ b, v = .logic b := by
  cases v <;> simp_all [hasTy]
theorem hasTy_char {v} (h : hasTy v .char = true) : ∃ c, v = .char c ∧ c < 256 := by
  cases v <;> simp_all [hasTy]
theorem hasTy_arr {v t} (h : hasTy v (.arr t) = true) : ∃ vs, v = .arr vs ∧ allTy vs t = true := by
  cases v <;> simp_all [hasTy]
theorem hasTy_tup {v ts} (h : hasTy v (.tup ts) = true) : ∃ vs, v = .tup vs ∧ allTys vs ts = true := by
  cases v <;> simp_all [hasTy]
theorem hasTy_opt {v t} (h : hasTy v (.opt t) = true) : v = .none ∨ ∃ w, v = .some w ∧ hasTy w t = true := by
  cases v <;> simp_all [hasTy]

/-! ### Primitives -/

theorem ResOK_ofInt {ρ} (i : Int) : ResOK .int ρ (Res.ofInt i) := by
  unfold Res.ofInt; split <;> simp [ResOK, hasTy]

theorem flattenArrs_typed : ∀ {xss : List Value} {t}, allTy xss (.arr t) = true →
    ∃ vs, flattenArrs xss = some vs ∧ allTy vs t = true
  | [], _, _ => ⟨[], rfl, rfl⟩
  | x :: xss, t, h => by
    simp only [allTy, Bool.and_eq_true] at h
    obtain ⟨xs, rfl, hx⟩ := hasTy_arr h.1
    obtain ⟨vs, hvs, hv⟩ := flattenArrs_typed h.2
    exact ⟨xs ++ vs, by simp [flattenArrs, hvs], allTy_append hx hv⟩

theorem rangeVals_typed (a b : Int) : allTy (rangeVals a b) .int = true := by
  rw [allTy_iff]; intro v hv
  simp only [rangeVals, List.mem_map] at hv
  obtain ⟨_, _, rfl⟩ := hv; rfl

theorem asBytes_of_char : ∀ {vs : List Value}, allTy vs .char = true → (asBytes vs).isSome
  | [], _ => rfl
  | v :: vs, h => by
    simp only [allTy, Bool.and_eq_true] at h
    obtain ⟨c, rfl, _⟩ := hasTy_char h.1
    have := asBytes_of_char h.2
    simp only [asBytes]
    rcases hb : asBytes vs with _ | bs
    · simp [hb] at this
    · simp

theorem intBytes_typed (i : Int) : allTy ((intBytes i).map Value.char) .char = true := by
  rw [allTy_iff]; intro v hv
  simp only [intBytes, List.map_map, List.mem_map] at hv
  obtain ⟨b, _, rfl⟩ := hv
  have := b.toNat_lt
  show hasTy (Value.char b.toNat) VTy.char = true
  simp only [hasTy, decide_eq_true_eq]; omega

theorem toStr_typed {v t} (ht : PrimTy .toStr [t] VTy.str) (hv : hasTy v t = true) {ρ} :
    ResOK VTy.str ρ (toStrValue v) := by
  cases ht with
  | toStrInt => obtain ⟨a, rfl⟩ := hasTy_int hv; simp [toStrValue, ResOK, hasTy, VTy.str, intBytes_typed]
  | toStrChar =>
    obtain ⟨c, rfl, hc⟩ := hasTy_char hv
    simp [toStrValue, ResOK, hasTy, VTy.str, allTy, hc]
  | toStrStr =>
    obtain ⟨vs, rfl, hvs⟩ := hasTy_arr hv
    have := asBytes_of_char hvs
    simp only [toStrValue]
    rcases hb : asBytes vs with _ | bs
    · simp [hb] at this
    · simp [ResOK, hasTy, VTy.str, hvs]

theorem cmpRes_ok {b : Bool} {v : Value} {τ ρ} (h : hasTy v τ = true) : ResOK τ ρ (cmpRes b v) := by
  unfold cmpRes; split <;> simp [ResOK, h]

/-- **Primitives are type safe**: a primitive applied to arguments of its
    parameter types gives a value of its result type, or fails, or raises an
    error other than a type error. -/
theorem prim_typed {op ts τ ρ} {vs : List Value} (hp : PrimTy op ts τ) (hv : allTys vs ts = true) :
    ResOK τ ρ (op.apply vs) := by
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
        · next v hv' => exact allTy_get hx hv'
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

/-! ### Frames -/

theorem ResOK_retype {σ τ ρ : VTy} {r : Res} (hr : r.isOk = false) (h : ResOK σ ρ r) : ResOK τ ρ r := by
  cases r <;> simp_all [ResOK]

theorem lt_of_getElem?_some {α} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : i < l.length := by
  rcases Nat.lt_or_ge i l.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

theorem readSlot_typed {Γ : List VTy} {s : St} {i : Nat} {τ : VTy} (hf : FrameOK Γ s.fr)
    (hi : Γ[i]? = some τ) : ∃ v, readSlot s i = .ok v ∧ hasTy v τ = true := by
  obtain ⟨v, hv, ht⟩ := allTys_get hf hi
  exact ⟨v, by simp [readSlot, hv], ht⟩

theorem writeSlot_typed {Γ : List VTy} {s : St} {i : Nat} {τ : VTy} {v : Value} (hf : FrameOK Γ s.fr)
    (hi : Γ[i]? = some τ) (hv : hasTy v τ = true) :
    ∃ s', writeSlot s i v = some s' ∧ FrameOK Γ s'.fr ∧ s'.out = s.out := by
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

/-- Running the initialisation prefix: what is left is the rest of the body,
    from the frame whose slots `k, …` hold the defaults, with no more fuel. -/
theorem eval_initPrefix {P : Prog} : ∀ (ts : List VTy) (n k : Nat) (fr : List Value) (o : List Nat)
    (b : Expr) (x : Res × St), eval P n ⟨fr, o⟩ (initPrefix k ts b) = some x →
    k + ts.length = fr.length → ∃ m ≤ n, eval P m ⟨fr.take k ++ VTy.defaults ts, o⟩ b = some x
  | [], n, k, fr, o, b, x, h, hl => by
    refine ⟨n, Nat.le_refl _, ?_⟩
    simp only [List.length_nil, Nat.add_zero] at hl
    rw [List.take_of_length_le (by omega)]
    simpa [VTy.defaults, initPrefix] using h
  | t :: ts, n, k, fr, o, b, x, h, hl => by
    have hk : k < fr.length := by simp at hl; omega
    match n, h with
    | n + 1, h =>
      simp only [initPrefix, eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk'⟩ | ⟨r1, s1, hx, hr, _⟩
      · match n, hx, hk' with
        | n' + 2, hx, hk' =>
          simp only [eval, bindR, writeSlot, hk, ite_true, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨-, rfl⟩ := hx
          obtain ⟨m, hm, hm'⟩ := eval_initPrefix ts (n' + 2) (k + 1) (fr.set k t.default) o b x hk'
            (by simp at hl ⊢; omega)
          refine ⟨m, by omega, ?_⟩
          rw [take_set_succ fr k _ hk] at hm'
          simpa [VTy.defaults] using hm'
        | 0, hx, _ => simp [eval] at hx
        | 1, hx, _ => simp [eval, bindR] at hx
      · match n, hx with
        | n' + 2, hx =>
          simp only [eval, bindR, writeSlot, hk, ite_true, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          simp at hr
        | 0, hx => simp [eval] at hx
        | 1, hx => simp [eval, bindR] at hx

/-! ### Preservation, by strong induction on fuel -/

section
variable (P : Prog) (S : Sigs)

def StmtE (n : Nat) : Prop :=
  ∀ (s : St) (e : Expr) (x : Res × St) (Γ : List VTy) (ρ τ : VTy), eval P n s e = some x →
    Typed S Γ ρ e τ → FrameOK Γ s.fr → FrameOK Γ x.2.fr ∧ ResOK τ ρ x.1

def StmtL (n : Nat) : Prop :=
  ∀ (s : St) (es : List Expr) (x : LRes × St) (Γ : List VTy) (ρ : VTy) (ts : List VTy),
    evalList P n s es = some x → TypedL S Γ ρ es ts → FrameOK Γ s.fr →
    FrameOK Γ x.2.fr ∧ LResOK ts ρ x.1

def StmtF (n : Nat) : Prop :=
  ∀ (i : Nat) (filt body : Expr) (s : St) (vs acc : List Value) (x : Res × St) (Γ : List VTy)
    (ρ τe σ τb : VTy), evalFor P n i filt body s vs acc = some x → Γ[i]? = some τe →
    allTy vs τe = true → allTy acc τb = true → Typed S Γ ρ filt σ → Typed S Γ ρ body τb →
    FrameOK Γ s.fr → FrameOK Γ x.2.fr ∧ ResOK (.arr τb) ρ x.1
end

theorem hasTy_void : hasTy Value.void VTy.void = true := rfl

theorem stepE {P : Prog} {S : Sigs} (hP : ProgTyped P S) (n : Nat)
    (ih : ∀ m ≤ n, StmtE P S m ∧ StmtL P S m ∧ StmtF P S m) : StmtE P S (n + 1) := by
  have IE := (ih n (Nat.le_refl _)).1
  have IL := (ih n (Nat.le_refl _)).2.1
  have IF := (ih n (Nat.le_refl _)).2.2
  intro s e x Γ ρ τ h ht hf
  cases e with
  | lit v =>
    simp only [eval, Option.some.injEq] at h; subst h
    cases ht with | lit hv => exact ⟨hf, hv⟩
  | «local» i =>
    simp only [eval, Option.some.injEq] at h; subst h
    cases ht with
    | «local» hi =>
      obtain ⟨v, hv, ht⟩ := readSlot_typed hf hi
      exact ⟨hf, by simp [hv, ResOK, ht]⟩
  | assign i e =>
    cases ht with
    | assign hi he =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk⟩ | ⟨r1, s1, hx, hr, rfl⟩
      · obtain ⟨hf1, hv⟩ := IE _ _ _ _ _ _ hx he hf
        obtain ⟨s2, hw, hf2, _⟩ := writeSlot_typed hf1 hi hv
        simp only [hw, Option.some.injEq] at hk; subst hk
        exact ⟨hf2, hv⟩
      · exact IE _ _ _ _ _ _ hx he hf
  | seq a b =>
    cases ht with
    | seq ha hb =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk⟩ | ⟨r1, s1, hx, hr, rfl⟩
      · exact IE _ _ _ _ _ _ hk hb (IE _ _ _ _ _ _ hx ha hf).1
      · obtain ⟨hf1, hr1⟩ := IE _ _ _ _ _ _ hx ha hf
        exact ⟨hf1, ResOK_retype hr hr1⟩
  | prim op es =>
    cases ht with
    | prim hes hp =>
      simp only [eval] at h
      rcases bindL_some h with ⟨vs, s1, hx, hk⟩ | ⟨r1, s1, hx, rfl⟩
      · simp only [Option.some.injEq] at hk; subst hk
        obtain ⟨hf1, hvs⟩ := IL _ _ _ _ _ _ hx hes hf
        exact ⟨hf1, prim_typed hp hvs⟩
      · obtain ⟨hf1, hr1, hok⟩ := IL _ _ _ _ _ _ hx hes hf
        exact ⟨hf1, ResOK_retype hok hr1⟩
  | call f es =>
    cases ht with
    | call hsig hes =>
      rename_i ps
      simp only [eval] at h
      rcases bindL_some h with ⟨vs, s1, hx, hk⟩ | ⟨r1, s1, hx, rfl⟩
      · obtain ⟨hf1, hvs⟩ := IL _ _ _ _ _ _ hx hes hf
        split at hk
        · simp only [Option.some.injEq] at hk; subst hk
          exact ⟨hf1, by simp [ResOK]⟩
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
                obtain ⟨Γ', hft⟩ := hP.2 f fn' ps τ hfn hsig
                obtain ⟨b, hbody, hbt⟩ := hft.body
                have hlen := allTys_length hvs
                rw [hbody] at hb
                have hl : fn'.arity + (Γ'.drop fn'.arity).length = (frameOf fn' vs).length := by
                  simp [frameOf, hft.slots]; omega
                obtain ⟨m, hm, hm'⟩ := eval_initPrefix _ _ _ _ _ _ _ hb hl
                have hfr : (frameOf fn' vs).take fn'.arity = vs := by
                  simp [frameOf, ← har]
                rw [hfr] at hm'
                have hf' : FrameOK Γ' (vs ++ VTy.defaults (Γ'.drop fn'.arity)) := by
                  have := allTys_append hvs (allTys_defaults (Γ'.drop fn'.arity))
                  rw [← hft.params, List.take_append_drop] at this
                  exact this
                obtain ⟨-, hres⟩ := ((ih m hm).1) _ _ _ _ _ _ hm' hbt hf'
                refine ⟨hf1, ?_⟩
                cases r2 <;> simp_all [retOf, ResOK]
              · simp at hc
            · simp at hc
      · obtain ⟨hf1, hr1, hok⟩ := IL _ _ _ _ _ _ hx hes hf
        exact ⟨hf1, ResOK_retype hok hr1⟩
  | ite c t e =>
    cases ht with
    | ite hc htt hte =>
      simp only [eval] at h
      split at h
      · simp at h
      · next v s1 hx => exact IE _ _ _ _ _ _ h htt (IE _ _ _ _ _ _ hx hc hf).1
      · exact IE _ _ _ _ _ _ h hte hf
      all_goals
        rename_i hx
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hf1, hr1⟩ := IE _ _ _ _ _ _ hx hc hf
        exact ⟨hf1, ResOK_retype rfl hr1⟩
  | forE i it filt body =>
    cases ht with
    | forE hi hit hfl hbd =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk⟩ | ⟨r1, s1, hx, hr, rfl⟩
      · obtain ⟨hf1, hv⟩ := IE _ _ _ _ _ _ hx hit hf
        obtain ⟨vs, rfl, hvs⟩ := hasTy_arr hv
        exact IF _ _ _ _ _ _ _ _ _ _ _ _ hk hi hvs rfl hfl hbd hf1
      · obtain ⟨hf1, hr1⟩ := IE _ _ _ _ _ _ hx hit hf
        exact ⟨hf1, ResOK_retype hr hr1⟩
  | loop b =>
    cases ht with
    | loop hb =>
      simp only [eval] at h
      split at h
      · simp at h
      · next v s1 hx => exact IE _ _ _ _ _ _ h (.loop hb) (IE _ _ _ _ _ _ hx hb hf).1
      · next s1 hx =>
        simp only [Option.some.injEq] at h; subst h
        exact ⟨(IE _ _ _ _ _ _ hx hb hf).1, hasTy_void⟩
      all_goals
        rename_i hx
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hf1, hr1⟩ := IE _ _ _ _ _ _ hx hb hf
        exact ⟨hf1, ResOK_retype rfl hr1⟩
  | brk =>
    simp only [eval, Option.some.injEq] at h; subst h
    exact ⟨hf, trivial⟩
  | ret e =>
    cases ht with
    | ret he =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk⟩ | ⟨r1, s1, hx, hr, rfl⟩
      · simp only [Option.some.injEq] at hk; subst hk
        obtain ⟨hf1, hv⟩ := IE _ _ _ _ _ _ hx he hf
        exact ⟨hf1, hv⟩
      · obtain ⟨hf1, hr1⟩ := IE _ _ _ _ _ _ hx he hf
        exact ⟨hf1, ResOK_retype hr hr1⟩
  | print e =>
    cases ht with
    | print he =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s1, hx, hk⟩ | ⟨r1, s1, hx, hr, rfl⟩
      · obtain ⟨hf1, hv⟩ := IE _ _ _ _ _ _ hx he hf
        obtain ⟨vs, rfl, hvs⟩ := hasTy_arr hv
        have hb := asBytes_of_char hvs
        split at hk
        · simp only [Option.some.injEq] at hk; subst hk
          exact ⟨hf1, hasTy_void⟩
        · next hp =>
          simp only [printBytes] at hp
          rcases hab : asBytes vs with _ | bs
          · simp [hab] at hb
          · simp [hab] at hp
      · obtain ⟨hf1, hr1⟩ := IE _ _ _ _ _ _ hx he hf
        exact ⟨hf1, ResOK_retype hr hr1⟩

theorem stepL {P : Prog} {S : Sigs} (n : Nat)
    (ih : ∀ m ≤ n, StmtE P S m ∧ StmtL P S m ∧ StmtF P S m) : StmtL P S (n + 1) := by
  have IE := (ih n (Nat.le_refl _)).1
  have IL := (ih n (Nat.le_refl _)).2.1
  intro s es x Γ ρ ts h ht hf
  cases es with
  | nil =>
    simp only [evalList, Option.some.injEq] at h; subst h
    cases ht with | nil => exact ⟨hf, rfl⟩
  | cons e es =>
    cases ht with
    | cons he hes =>
      simp only [evalList] at h
      split at h
      · simp at h
      · next v s1 hx =>
        obtain ⟨hf1, hv⟩ := IE _ _ _ _ _ _ hx he hf
        split at h
        · simp at h
        · next vs s2 hxs =>
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨hf2, hvs⟩ := IL _ _ _ _ _ _ hxs hes hf1
          have hv' : hasTy v _ = true := hv
          have hvs' : allTys vs _ = true := hvs
          exact ⟨hf2, by simp [LResOK, allTys, hv', hvs']⟩
        · next r s2 hxs =>
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨hf2, hr2⟩ := IL _ _ _ _ _ _ hxs hes hf1
          exact ⟨hf2, hr2⟩
      all_goals
        rename_i hx
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hf1, hr1⟩ := IE _ _ _ _ _ _ hx he hf
        exact ⟨hf1, ResOK_retype rfl hr1, rfl⟩

theorem stepF {P : Prog} {S : Sigs} (n : Nat)
    (ih : ∀ m ≤ n, StmtE P S m ∧ StmtL P S m ∧ StmtF P S m) : StmtF P S (n + 1) := by
  have IE := (ih n (Nat.le_refl _)).1
  have IF := (ih n (Nat.le_refl _)).2.2
  intro i filt body s vs acc x Γ ρ τe σ τb h hi hvs hacc hfl hbd hf
  cases vs with
  | nil =>
    simp only [evalFor, Option.some.injEq] at h; subst h
    exact ⟨hf, by simp [ResOK, hasTy, allTy_reverse hacc]⟩
  | cons v vs =>
    simp only [allTy, Bool.and_eq_true] at hvs
    simp only [evalFor] at h
    obtain ⟨s0, hw, hf0, _⟩ := writeSlot_typed hf hi hvs.1
    simp only [hw] at h
    split at h
    · simp at h
    · exact IF _ _ _ _ _ _ _ _ _ _ _ _ h hi hvs.2 hacc hfl hbd hf0
    · next u s1 hx =>
      obtain ⟨hf1, _⟩ := IE _ _ _ _ _ _ hx hfl hf0
      split at h
      · simp at h
      · next w s2 hb =>
        obtain ⟨hf2, hw2⟩ := IE _ _ _ _ _ _ hb hbd hf1
        have hw2' : hasTy w τb = true := hw2
        exact IF _ _ _ _ _ _ _ _ _ _ _ _ h hi hvs.2 (by simp [allTy, hw2', hacc]) hfl hbd hf2
      all_goals
        rename_i hb
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hf2, hr2⟩ := IE _ _ _ _ _ _ hb hbd hf1
        exact ⟨hf2, ResOK_retype rfl hr2⟩
    all_goals
      rename_i hx
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hf1, hr1⟩ := IE _ _ _ _ _ _ hx hfl hf0
      exact ⟨hf1, ResOK_retype rfl hr1⟩

theorem typed_all {P : Prog} {S : Sigs} (hP : ProgTyped P S) :
    ∀ n, ∀ m ≤ n, StmtE P S m ∧ StmtL P S m ∧ StmtF P S m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have : m = 0 := by omega
    subst this
    refine ⟨?_, ?_, ?_⟩
    · intro _ _ _ _ _ _ h; simp [eval] at h
    · intro _ _ _ _ _ _ h; simp [evalList] at h
    · intro _ _ _ _ _ _ _ _ _ _ _ _ h; simp [evalFor] at h
  | succ n ih =>
    intro m hm
    by_cases hmn : m ≤ n
    · exact ih m hmn
    · have : m = n + 1 := by omega
      subst this
      exact ⟨stepE hP n ih, stepL n ih, stepF n ih⟩

/-! ### Type safety -/

/-- **Preservation.** A typed expression evaluated from a well-typed frame
    leaves a well-typed frame, and its outcome is a value of its type, a
    `return` of a value of the function's type, or anything but a type error. -/
theorem Eval.typed {P : Prog} {S : Sigs} (hP : ProgTyped P S) {s e r s' Γ ρ τ}
    (h : Eval P s e r s') (ht : Typed S Γ ρ e τ) (hf : FrameOK Γ s.fr) :
    FrameOK Γ s'.fr ∧ ResOK τ ρ r := by
  obtain ⟨n, hn⟩ := eval_iff.mp h
  exact (typed_all hP n n (Nat.le_refl _)).1 s e (r, s') Γ ρ τ hn ht hf

/-- **Type safety of programs.** In a typed program whose `Main` takes no
    parameters and returns `τ`, no run raises a type error, and a successful
    run returns a value of type `τ`. -/
theorem Runs.typed {P : Prog} {S : Sigs} (hP : ProgTyped P S) {τ r out}
    (hm : S[P.main]? = some ([], τ)) (h : Runs P r out) :
    r ≠ .err .type ∧ ∀ v, r = .ok v → hasTy v τ = true := by
  obtain ⟨fr, h⟩ := h
  have ht : Typed S [] τ (.call P.main []) τ := .call hm .nil
  obtain ⟨-, hr⟩ := Eval.typed hP h ht rfl
  refine ⟨?_, ?_⟩
  · intro he; subst he; exact hr rfl
  · intro v hv; subst hv; exact hr

end OpenVerse
