/-
  OpenVerse — derived surface forms and their rollback laws.

  The Book of Verse (ch. 4 "Operators", ch. 8 "Failure") describes these
  constructs; here each is a definition in terms of Verse Core, followed by
  the theorems that say it behaves as the book states:

  * `not e` succeeds exactly when `e` fails, and *always* discards the
    effects of `e` ("`not e` always throws away `e`'s effects").
  * `a or b` gives `a`'s value if `a` succeeds, else `b`'s, with the effects
    of a failed `a` rolled back.
  * `option{e}` is `some v` when `e` succeeds with `v` and the empty option
    (with no effects) when it fails.
  * `logic{e}` is `true` / `false` in the same way.
  * A failed `if` condition leaves no trace: the `else` branch behaves
    exactly as if the condition had never run.
-/
import OpenVerse.Core.Adequacy

namespace OpenVerse

/-- `not e` (the result of a successful `not` is `void`). -/
def Expr.notE (e : Expr) : Expr := .ite e (.prim .fail []) (.lit .void)
/-- `a or b`; slot `t` is a fresh temporary of the elaborator. -/
def Expr.orE (t : Nat) (a b : Expr) : Expr := .ite (.assign t a) (.local t) b
/-- `a and b`: the value of `b`. -/
def Expr.andE (a b : Expr) : Expr := .seq a b
/-- `option{e}`; slot `t` is a fresh temporary. -/
def Expr.optionE (t : Nat) (e : Expr) : Expr :=
  .ite (.assign t e) (.prim .mkSome [.local t]) (.lit .none)
/-- `logic{e}`. -/
def Expr.logicE (e : Expr) : Expr := .ite e (.lit (.logic true)) (.lit (.logic false))

/-! ### Small inversion helpers -/

theorem Eval.lit_inv {P s v r s'} (h : Eval P s (.lit v) r s') : r = .ok v ∧ s' = s := by
  cases h; exact ⟨rfl, rfl⟩

theorem Eval.fail_inv {P s r s'} (h : Eval P s (.prim .fail []) r s') : r = .fail ∧ s' = s := by
  cases h with
  | prim_ok hl => cases hl; exact ⟨rfl, rfl⟩
  | prim_stop hl => cases hl

/-! ### Failure contexts roll back -/

/-- **Rollback of `if`.** Once the condition has failed, the whole `if`
    behaves as its `else` branch run from the *original* state. -/
theorem ite_rollback {P s s₁ c t e r s'} (hc : Eval P s c .fail s₁) :
    Eval P s (.ite c t e) r s' ↔ Eval P s e r s' := by
  constructor
  · intro h
    cases h with
    | ite_ok h1 _ => exact absurd (Eval.det h1 hc).1 (by simp)
    | ite_fail _ h2 => exact h2
    | ite_stop h1 _ hf => exact absurd (Eval.det h1 hc).1 hf
  · intro h; exact .ite_fail hc h

/-- **`not` discards effects.** A successful `not e` returns `void` and
    leaves the state exactly as it found it. -/
theorem notE_ok {P s e v s'} (h : Eval P s (Expr.notE e) (.ok v) s') :
    v = .void ∧ s' = s ∧ ∃ s₁, Eval P s e .fail s₁ := by
  unfold Expr.notE at h
  cases h with
  | ite_ok _ h2 => exact absurd (Eval.fail_inv h2).1 (by simp)
  | ite_fail h1 h2 =>
    obtain ⟨hv, hs⟩ := Eval.lit_inv h2
    cases hv; exact ⟨rfl, hs, _, h1⟩
  | ite_stop _ hr _ => simp at hr

/-- `not e` fails when `e` succeeds. -/
theorem notE_of_ok {P s e v s₁} (h : Eval P s e (.ok v) s₁) :
    Eval P s (Expr.notE e) .fail s₁ :=
  .ite_ok h (.prim_ok .nil)

/-- `not e` succeeds, with no effect, when `e` fails. -/
theorem notE_of_fail {P s e s₁} (h : Eval P s e .fail s₁) :
    Eval P s (Expr.notE e) (.ok .void) s :=
  .ite_fail h .lit

/-- **`not not e` is a pure test**: it succeeds exactly when `e` succeeds,
    and never changes the state. -/
theorem notE_notE_ok {P s e v s'} (h : Eval P s (Expr.notE (Expr.notE e)) (.ok v) s') :
    s' = s ∧ ∃ u s₁, Eval P s e (.ok u) s₁ := by
  obtain ⟨-, hs, s₁, hf⟩ := notE_ok h
  refine ⟨hs, ?_⟩
  unfold Expr.notE at hf
  cases hf with
  | ite_ok h1 h2 => exact ⟨_, _, h1⟩
  | ite_fail _ h2 => exact absurd (Eval.lit_inv h2).1 (by simp)
  | ite_stop _ _ hf' => exact absurd rfl hf'

/-- `mkSome` never produces the empty option. -/
theorem Eval.mkSome_ne_none {P s e r s'} (h : Eval P s (.prim .mkSome [e]) r s')
    (hr : r = .ok .none) : False := by
  cases h with
  | prim_ok hl =>
    cases hl with
    | cons_ok _ hl' => cases hl'; simp [Prim.apply] at hr
  | prim_stop hl =>
    cases hl with
    | cons_stop _ h' => subst hr; simp at h'
    | cons_stop_tail _ hl' => cases hl'

/-- **`option{}` of a failure is empty and effect-free.** -/
theorem optionE_none {P s t e s'} (h : Eval P s (Expr.optionE t e) (.ok .none) s') : s' = s := by
  unfold Expr.optionE at h
  cases h with
  | ite_ok _ h2 => exact (Eval.mkSome_ne_none h2 rfl).elim
  | ite_fail _ h2 => exact (Eval.lit_inv h2).2
  | ite_stop _ hr _ => simp at hr

/-- `option{e}` of a success with `v` is `some v`. -/
theorem optionE_some {P s t e v s₁ s₂} (h : Eval P s e (.ok v) s₁) (hw : writeSlot s₁ t v = some s₂) :
    Eval P s (Expr.optionE t e) (.ok (.some v)) s₂ := by
  unfold Expr.optionE
  have hread : readSlot s₂ t = .ok v := by
    unfold writeSlot at hw
    split at hw
    · next hlt =>
      simp only [Option.some.injEq] at hw; subst hw
      simp [readSlot, List.getElem?_set_self hlt]
    · simp at hw
  have := Eval.prim_ok (P := P) (op := .mkSome)
    (EvalList.cons_ok (hread ▸ Eval.local) EvalList.nil)
  exact .ite_ok (.assign_ok h hw) (by simpa [Prim.apply] using this)

/-- `option{e}` of a failure is the empty option. -/
theorem optionE_of_fail {P s t e s₁} (h : Eval P s e .fail s₁) :
    Eval P s (Expr.optionE t e) (.ok .none) s :=
  .ite_fail (.assign_stop h rfl) .lit

/-- `a or b` with a failing `a` is `b` from the original state. -/
theorem orE_right {P s s₁ t a b r s'} (ha : Eval P s a .fail s₁) :
    Eval P s (Expr.orE t a b) r s' ↔ Eval P s b r s' :=
  ite_rollback (.assign_stop ha rfl)

/-- `logic{e}` is `false`, with no effect, when `e` fails. -/
theorem logicE_of_fail {P s e s₁} (h : Eval P s e .fail s₁) :
    Eval P s (Expr.logicE e) (.ok (.logic false)) s :=
  .ite_fail h .lit

/-- `logic{e}` never fails. -/
theorem logicE_ne_fail {P s e s'} (h : Eval P s (Expr.logicE e) .fail s') : False := by
  unfold Expr.logicE at h
  cases h with
  | ite_ok _ h2 => exact absurd (Eval.lit_inv h2).1 (by simp)
  | ite_fail _ h2 => exact absurd (Eval.lit_inv h2).1 (by simp)
  | ite_stop _ _ hf => exact hf rfl

end OpenVerse
