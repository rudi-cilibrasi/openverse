/-
  OpenVerse — the interpreter computes exactly the big-step semantics.

  * `eval_sound`: whatever `eval` returns is derivable in `Eval`.
  * `eval_complete`: every derivation is what `eval` returns for all large
    enough fuels.
  * `Eval.det`: the semantics is deterministic (a corollary of the two).
  * `eval_fuel_irrelevant`: two fuels that both finish give the same answer.
-/
import OpenVerse.Core.Interp

namespace OpenVerse

/-! ### Inversion of the binding combinators -/

theorem bindR_some {x : Option (Res × St)} {k y} (h : bindR x k = some y) :
    (∃ v s, x = some (.ok v, s) ∧ k v s = some y) ∨
    (∃ r s, x = some (r, s) ∧ r.isOk = false ∧ y = (r, s)) := by
  rcases x with _ | ⟨r, s⟩
  · simp [bindR] at h
  · cases r with
    | ok v => exact .inl ⟨v, s, rfl, h⟩
    | _ => simp only [bindR, Option.some.injEq] at h; subst h; exact .inr ⟨_, s, rfl, rfl, rfl⟩

theorem bindR_stop {r : Res} {s : St} {k} (h : r.isOk = false) :
    bindR (some (r, s)) k = some (r, s) := by
  cases r <;> simp_all [bindR]

theorem bindL_some {x : Option (LRes × St)} {k y} (h : bindL x k = some y) :
    (∃ vs s, x = some (.ok vs, s) ∧ k vs s = some y) ∨
    (∃ r s, x = some (.stop r, s) ∧ y = (r, s)) := by
  rcases x with _ | ⟨r, s⟩
  · simp [bindL] at h
  · cases r with
    | ok vs => exact .inl ⟨vs, s, rfl, h⟩
    | stop r => simp only [bindL, Option.some.injEq] at h; subst h; exact .inr ⟨r, s, rfl, rfl⟩

/-! ### Soundness -/

mutual
theorem eval_sound {P : Prog} : ∀ (n : Nat) {s e r s'},
    eval P n s e = some (r, s') → Eval P s e r s'
  | 0, _, _, _, _, h => by simp [eval] at h
  | n+1, s, e, r, s', h => by
    cases e with
    | lit v => simp only [eval, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .lit
    | «local» i => simp only [eval, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .local
    | assign i e =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s₁, hx, hk⟩ | ⟨r₁, s₁, hx, hr, hy⟩
      · split at hk
        · next s₂ hw =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
          exact .assign_ok (eval_sound n hx) hw
        · next hw =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
          exact .assign_bad (eval_sound n hx) hw
      · simp only [Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy
        exact .assign_stop (eval_sound n hx) hr
    | seq a b =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s₁, hx, hk⟩ | ⟨r₁, s₁, hx, hr, hy⟩
      · exact .seq_ok (eval_sound n hx) (eval_sound n hk)
      · simp only [Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy
        exact .seq_stop (eval_sound n hx) hr
    | prim op es =>
      simp only [eval] at h
      rcases bindL_some h with ⟨vs, s₁, hx, hk⟩ | ⟨r₁, s₁, hx, hy⟩
      · split at hk
        · simp at hk
        · simp only [Option.some.injEq, Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
          exact .prim_ok (evalList_sound n hx)
      · simp only [Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy
        exact .prim_stop (evalList_sound n hx)
    | heap op es =>
      simp only [eval, St.heapStep_eq] at h
      rcases bindL_some h with ⟨vs, s₁, hx, hk⟩ | ⟨r₁, s₁, hx, hy⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
        exact .heap_ok (evalList_sound n hx)
      · simp only [Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy
        exact .heap_stop (evalList_sound n hx)
    | call f es =>
      simp only [eval] at h
      rcases bindL_some h with ⟨vs, s₁, hx, hk⟩ | ⟨r₁, s₁, hx, hy⟩
      · split at hk
        · next hc =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
          exact .call_bad (evalList_sound n hx) hc
        · next fn hc =>
          split at hk
          · simp at hk
          · next r₂ s₂ hb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
            exact .call_ok (evalList_sound n hx) hc (eval_sound n hb)
      · simp only [Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy
        exact .call_stop (evalList_sound n hx)
    | ite c t e =>
      simp only [eval] at h
      split at h
      · simp at h
      · next v s₁ hc => exact .ite_ok (eval_sound n hc) (eval_sound n h)
      · next s₁ hc => exact .ite_fail (eval_sound n hc) (eval_sound n h)
      all_goals
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        rename_i hc
        exact .ite_stop (eval_sound n hc) rfl (by simp)
    | forE i it filt body =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s₁, hx, hk⟩ | ⟨r₁, s₁, hx, hr, hy⟩
      · cases v with
        | arr vs => exact .for_ok (eval_sound n hx) (evalFor_sound n hk)
        | _ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
          exact .for_type (eval_sound n hx) (by intro vs h; cases h)
      · simp only [Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy
        exact .for_stop (eval_sound n hx) hr
    | loop b =>
      simp only [eval] at h
      split at h
      · simp at h
      · next v s₁ hb => exact .loop_ok (eval_sound n hb) (eval_sound n h)
      · next s₁ hb =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact .loop_brk (eval_sound n hb)
      all_goals
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        rename_i hb
        exact .loop_stop (eval_sound n hb) rfl (by simp)
    | brk => simp only [eval, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .brk
    | ret e =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s₁, hx, hk⟩ | ⟨r₁, s₁, hx, hr, hy⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
        exact .ret_ok (eval_sound n hx)
      · simp only [Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy
        exact .ret_stop (eval_sound n hx) hr
    | print e =>
      simp only [eval] at h
      rcases bindR_some h with ⟨v, s₁, hx, hk⟩ | ⟨r₁, s₁, hx, hr, hy⟩
      · split at hk
        · next bs hp =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
          exact .print_ok (eval_sound n hx) hp
        · next hp =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
          exact .print_bad (eval_sound n hx) hp
      · simp only [Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy
        exact .print_stop (eval_sound n hx) hr

theorem evalList_sound {P : Prog} : ∀ (n : Nat) {s es lr s'},
    evalList P n s es = some (lr, s') → EvalList P s es lr s'
  | 0, _, _, _, _, h => by simp [evalList] at h
  | n+1, s, [], lr, s', h => by
    simp only [evalList, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .nil
  | n+1, s, e :: es, lr, s', h => by
    simp only [evalList] at h
    split at h
    · simp at h
    · next v s₁ he =>
      split at h
      · simp at h
      · next vs s₂ hes =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact .cons_ok (eval_sound n he) (evalList_sound n hes)
      · next r s₂ hes =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact .cons_stop_tail (eval_sound n he) (evalList_sound n hes)
    all_goals
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rename_i he
      exact .cons_stop (eval_sound n he) rfl

theorem evalFor_sound {P : Prog} : ∀ (n : Nat) {i filt body s vs acc r s'},
    evalFor P n i filt body s vs acc = some (r, s') → EvalFor P i filt body s vs acc r s'
  | 0, _, _, _, _, _, _, _, _, h => by simp [evalFor] at h
  | n+1, i, filt, body, s, [], acc, r, s', h => by
    simp only [evalFor, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .done
  | n+1, i, filt, body, s, v :: vs, acc, r, s', h => by
    simp only [evalFor] at h
    split at h
    · next hw =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact .bad_slot hw
    · next s₀ hw =>
      split at h
      · simp at h
      · next s₁ hf => exact .skip hw (eval_sound n hf) (evalFor_sound n h)
      · next u s₁ hf =>
        split at h
        · simp at h
        · next w s₂ hb => exact .step hw (eval_sound n hf) (eval_sound n hb) (evalFor_sound n h)
        all_goals
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          rename_i hb
          exact .body_stop hw (eval_sound n hf) (eval_sound n hb) rfl
      all_goals
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        rename_i hf
        exact .filt_stop hw (eval_sound n hf) rfl (by simp)
end

/-! ### Completeness -/

/-- Fuel above `n + 1` is a successor above `n`. -/
private theorem succ_above {n m : Nat} (h : n + 1 ≤ m) : ∃ k, m = k + 1 ∧ n ≤ k :=
  ⟨m - 1, by omega, by omega⟩

/-- "From some fuel on, the interpreter returns `y`." -/
def Eventually (f : Nat → Option α) (y : α) : Prop := ∃ n, ∀ m, n ≤ m → f m = some y

mutual
theorem eval_complete {P : Prog} : ∀ {s e r s'}, Eval P s e r s' →
    Eventually (fun n => eval P n s e) (r, s')
  | _, _, _, _, .lit => ⟨1, fun m hm => by
      obtain ⟨k, rfl, -⟩ := succ_above hm; simp [eval]⟩
  | _, _, _, _, .local => ⟨1, fun m hm => by
      obtain ⟨k, rfl, -⟩ := succ_above hm; simp [eval]⟩
  | _, _, _, _, .assign_ok h hw => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp [eval, H k hk, bindR, hw]⟩
  | _, _, _, _, .assign_bad h hw => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp [eval, H k hk, bindR, hw]⟩
  | _, _, _, _, .assign_stop h hr => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindR_stop hr]⟩
  | _, _, _, _, .seq_ok h1 h2 => by
      obtain ⟨n1, H1⟩ := eval_complete h1
      obtain ⟨n2, H2⟩ := eval_complete h2
      exact ⟨max n1 n2 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H1 k (by omega), bindR, H2 k (by omega)]⟩
  | _, _, _, _, .seq_stop h hr => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindR_stop hr]⟩
  | _, _, _, _, .prim_ok (op := op) (vs := vs) h => by
      obtain ⟨n, H⟩ := evalList_complete h
      exact ⟨max n (op.cost vs) + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        have h1 : n ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
        have h2 : ¬ k < op.cost vs := Nat.not_lt.mpr (Nat.le_trans (Nat.le_max_right _ _) hk)
        simp only [eval, H k h1, bindL, h2, ite_false]⟩
  | _, _, _, _, .prim_stop h => by
      obtain ⟨n, H⟩ := evalList_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindL]⟩
  | _, _, _, _, .heap_ok h => by
      obtain ⟨n, H⟩ := evalList_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindL, St.heapStep_eq]⟩
  | _, _, _, _, .heap_stop h => by
      obtain ⟨n, H⟩ := evalList_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindL]⟩
  | _, _, _, _, .call_ok h hc hb => by
      obtain ⟨n1, H1⟩ := evalList_complete h
      obtain ⟨n2, H2⟩ := eval_complete hb
      exact ⟨max n1 n2 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H1 k (by omega), bindL, hc, H2 k (by omega)]⟩
  | _, _, _, _, .call_bad h hc => by
      obtain ⟨n, H⟩ := evalList_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindL, hc]⟩
  | _, _, _, _, .call_stop h => by
      obtain ⟨n, H⟩ := evalList_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindL]⟩
  | _, _, _, _, .ite_ok h1 h2 => by
      obtain ⟨n1, H1⟩ := eval_complete h1
      obtain ⟨n2, H2⟩ := eval_complete h2
      exact ⟨max n1 n2 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H1 k (by omega), H2 k (by omega)]⟩
  | _, _, _, _, .ite_fail h1 h2 => by
      obtain ⟨n1, H1⟩ := eval_complete h1
      obtain ⟨n2, H2⟩ := eval_complete h2
      exact ⟨max n1 n2 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H1 k (by omega), H2 k (by omega)]⟩
  | _, _, _, _, .ite_stop (r := r) h hr hf => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk]
        cases r <;> simp_all⟩
  | _, _, _, _, .for_ok h1 h2 => by
      obtain ⟨n1, H1⟩ := eval_complete h1
      obtain ⟨n2, H2⟩ := evalFor_complete h2
      exact ⟨max n1 n2 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H1 k (by omega), bindR, H2 k (by omega)]⟩
  | _, _, _, _, .for_type (v := v) h hv => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindR]
        cases v <;> simp_all⟩
  | _, _, _, _, .for_stop h hr => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindR_stop hr]⟩
  | _, _, _, _, .loop_ok h1 h2 => by
      obtain ⟨n1, H1⟩ := eval_complete h1
      obtain ⟨n2, H2⟩ := eval_complete h2
      exact ⟨max n1 n2 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H1 k (by omega), H2 k (by omega)]⟩
  | _, _, _, _, .loop_brk h => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk]⟩
  | _, _, _, _, .loop_stop (r := r) h hr hb => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk]
        cases r <;> simp_all⟩
  | _, _, _, _, .brk => ⟨1, fun m hm => by
      obtain ⟨k, rfl, -⟩ := succ_above hm; simp [eval]⟩
  | _, _, _, _, .ret_ok h => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindR]⟩
  | _, _, _, _, .ret_stop h hr => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindR_stop hr]⟩
  | _, _, _, _, .print_ok h hp => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindR, hp]⟩
  | _, _, _, _, .print_bad h hp => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindR, hp]⟩
  | _, _, _, _, .print_stop h hr => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [eval, H k hk, bindR_stop hr]⟩

theorem evalList_complete {P : Prog} : ∀ {s es lr s'}, EvalList P s es lr s' →
    Eventually (fun n => evalList P n s es) (lr, s')
  | _, _, _, _, .nil => ⟨1, fun m hm => by
      obtain ⟨k, rfl, -⟩ := succ_above hm; simp [evalList]⟩
  | _, _, _, _, .cons_ok h1 h2 => by
      obtain ⟨n1, H1⟩ := eval_complete h1
      obtain ⟨n2, H2⟩ := evalList_complete h2
      exact ⟨max n1 n2 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [evalList, H1 k (by omega), H2 k (by omega)]⟩
  | _, _, _, _, .cons_stop (r := r) h hr => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [evalList, H k hk]
        cases r <;> simp_all⟩
  | _, _, _, _, .cons_stop_tail h1 h2 => by
      obtain ⟨n1, H1⟩ := eval_complete h1
      obtain ⟨n2, H2⟩ := evalList_complete h2
      exact ⟨max n1 n2 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [evalList, H1 k (by omega), H2 k (by omega)]⟩

theorem evalFor_complete {P : Prog} : ∀ {i filt body s vs acc r s'},
    EvalFor P i filt body s vs acc r s' →
    Eventually (fun n => evalFor P n i filt body s vs acc) (r, s')
  | _, _, _, _, _, _, _, _, .done => ⟨1, fun m hm => by
      obtain ⟨k, rfl, -⟩ := succ_above hm; simp [evalFor]⟩
  | _, _, _, _, _, _, _, _, .bad_slot hw => ⟨1, fun m hm => by
      obtain ⟨k, rfl, -⟩ := succ_above hm; simp [evalFor, hw]⟩
  | _, _, _, _, _, _, _, _, .skip hw h1 h2 => by
      obtain ⟨n1, H1⟩ := eval_complete h1
      obtain ⟨n2, H2⟩ := evalFor_complete h2
      exact ⟨max n1 n2 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [evalFor, hw, H1 k (by omega), H2 k (by omega)]⟩
  | _, _, _, _, _, _, _, _, .filt_stop (r := r) hw h hr hf => by
      obtain ⟨n, H⟩ := eval_complete h
      exact ⟨n+1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [evalFor, hw, H k hk]
        cases r <;> simp_all⟩
  | _, _, _, _, _, _, _, _, .step hw h1 h2 h3 => by
      obtain ⟨n1, H1⟩ := eval_complete h1
      obtain ⟨n2, H2⟩ := eval_complete h2
      obtain ⟨n3, H3⟩ := evalFor_complete h3
      exact ⟨max (max n1 n2) n3 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [evalFor, hw, H1 k (by omega), H2 k (by omega), H3 k (by omega)]⟩
  | _, _, _, _, _, _, _, _, .body_stop (r := r) hw h1 h2 hr => by
      obtain ⟨n1, H1⟩ := eval_complete h1
      obtain ⟨n2, H2⟩ := eval_complete h2
      exact ⟨max n1 n2 + 1, fun m hm => by
        obtain ⟨k, rfl, hk⟩ := succ_above hm
        simp only [evalFor, hw, H1 k (by omega), H2 k (by omega)]
        cases r <;> simp_all⟩
end

/-! ### Consequences -/

/-- **Adequacy.** The big-step relation holds exactly when the interpreter,
    given enough fuel, returns that outcome. -/
theorem eval_iff {P : Prog} {s e r s'} :
    Eval P s e r s' ↔ ∃ n, eval P n s e = some (r, s') :=
  ⟨fun h => let ⟨n, H⟩ := eval_complete h; ⟨n, H n (Nat.le_refl _)⟩,
   fun ⟨n, h⟩ => eval_sound n h⟩

/-- Fuel only decides *whether* the interpreter finishes, never *what* it returns. -/
theorem eval_fuel_irrelevant {P : Prog} {n₁ n₂ s e x₁ x₂}
    (h₁ : eval P n₁ s e = some x₁) (h₂ : eval P n₂ s e = some x₂) : x₁ = x₂ := by
  obtain ⟨N₁, H₁⟩ := eval_complete (eval_sound n₁ h₁)
  obtain ⟨N₂, H₂⟩ := eval_complete (eval_sound n₂ h₂)
  have a := H₁ (max N₁ N₂) (by omega)
  have b := H₂ (max N₁ N₂) (by omega)
  rw [a] at b
  exact Option.some.inj b

/-- More fuel never changes a finished answer. -/
theorem eval_mono {P : Prog} {n m s e x} (h : eval P n s e = some x) (_hm : n ≤ m)
    (hfin : (eval P m s e).isSome) : eval P m s e = some x := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hfin
  rw [hy, eval_fuel_irrelevant h hy]

/-- **Determinism.** Verse Core evaluation has at most one outcome. -/
theorem Eval.det {P : Prog} {s e r₁ s₁ r₂ s₂}
    (h₁ : Eval P s e r₁ s₁) (h₂ : Eval P s e r₂ s₂) : r₁ = r₂ ∧ s₁ = s₂ := by
  obtain ⟨n₁, H₁⟩ := eval_iff.mp h₁
  obtain ⟨n₂, H₂⟩ := eval_iff.mp h₂
  have := eval_fuel_irrelevant H₁ H₂
  simp only [Prod.mk.injEq] at this
  exact this

/-- A program run is deterministic: one outcome, one output. -/
theorem Runs.det {P : Prog} {r₁ o₁ r₂ o₂} (h₁ : Runs P r₁ o₁) (h₂ : Runs P r₂ o₂) :
    r₁ = r₂ ∧ o₁ = o₂ := by
  obtain ⟨_, _, h₁⟩ := h₁
  obtain ⟨_, _, h₂⟩ := h₂
  obtain ⟨hr, hs⟩ := Eval.det h₁ h₂
  exact ⟨hr, congrArg (fun s : St => s.g.out) hs⟩

/-- `Prog.run` is correct: when it finishes, the program `Runs` to that outcome and output. -/
theorem Prog.run_sound {P : Prog} {n r out} (h : P.run n = some (r, out)) : Runs P r out := by
  unfold Prog.run at h
  rcases hx : eval P n Prog.initSt (.call P.main []) with _ | ⟨r', s'⟩
  · simp [hx] at h
  · simp only [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s'.fr, s'.g.heap, eval_sound n hx⟩

/-- `Prog.run` is complete: a program that `Runs` is run correctly by enough fuel. -/
theorem Prog.run_complete {P : Prog} {r out} (h : Runs P r out) :
    ∃ N, ∀ n, N ≤ n → P.run n = some (r, out) := by
  obtain ⟨fr, heap, h⟩ := h
  obtain ⟨N, H⟩ := eval_complete h
  exact ⟨N, fun n hn => by simp [Prog.run, H n hn]⟩

end OpenVerse
