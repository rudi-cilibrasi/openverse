/-
  OpenVerse — soundness of the `<decides>` effect.

  In Verse, only `<decides>` functions may fail, and failable expressions may
  only appear in failure contexts (Book of Verse, ch. 8 "Failure", ch. 13
  "Effects"). `Expr.mayFail` is the conservative analysis the elaborator
  enforces: an expression "may fail" if it contains a failable primitive or
  a call to a `<decides>` function *outside* every failure context.

  `Eval.no_fail`: an expression that may not fail never evaluates to
  failure, in any program whose non-`<decides>` functions all have bodies
  that may not fail (`Prog.EffectSound`). So a function without `<decides>`
  never fails (`call_no_fail`), and a program whose `Main` is not
  `<decides>` never ends in failure (`Runs.no_fail`).
-/
import OpenVerse.Core.Adequacy

namespace OpenVerse

mutual
/-- Can `e` fail (outside the failure contexts it contains)? -/
def Expr.mayFail (P : Prog) : Expr → Bool
  | .lit _ => false
  | .local _ => false
  | .brk => false
  | .assign _ e => e.mayFail P
  | .ret e => e.mayFail P
  | .print e => e.mayFail P
  | .loop e => e.mayFail P
  | .seq a b => a.mayFail P || b.mayFail P
  | .prim op es => op.failable || Expr.mayFailList P es
  -- a heap operation never fails (`HeapOp.apply_res`)
  | .heap _ es => Expr.mayFailList P es
  | .call f es =>
    (match P.fns[f]? with
      | some fn => fn.decides
      | none => false) || Expr.mayFailList P es
  -- the condition is a failure context: its failure is caught
  | .ite _ t e => t.mayFail P || e.mayFail P
  -- the filter is a failure context: its failure skips the element
  | .forE _ it _ body => it.mayFail P || body.mayFail P
/-- Can some expression of the list fail? -/
def Expr.mayFailList (P : Prog) : List Expr → Bool
  | [] => false
  | e :: es => e.mayFail P || Expr.mayFailList P es
end

/-- Every function that is not `<decides>` has a body that cannot fail. -/
def Prog.EffectSound (P : Prog) : Prop :=
  ∀ fn ∈ P.fns, fn.decides = false → fn.body.mayFail P = false

theorem readSlot_ne_fail (s : St) (i : Nat) : readSlot s i ≠ .fail := by
  unfold readSlot; split <;> simp

theorem retOf_ne_fail {r : Res} (h : r ≠ .fail) : retOf r ≠ .fail := by
  cases r <;> simp_all [retOf]

mutual
theorem Eval.no_fail {P : Prog} (hP : P.EffectSound) : ∀ {s e r s'},
    Eval P s e r s' → e.mayFail P = false → r ≠ .fail
  | _, _, _, _, .lit, _ => by simp
  | _, _, _, _, .local, _ => readSlot_ne_fail _ _
  | _, _, _, _, .assign_ok _ _, _ => by simp
  | _, _, _, _, .assign_bad _ _, _ => by simp
  | _, _, _, _, .assign_stop h _, hm => Eval.no_fail hP h (by simpa [Expr.mayFail] using hm)
  | _, _, _, _, .seq_ok _ h2, hm => by
      simp only [Expr.mayFail, Bool.or_eq_false_iff] at hm
      exact Eval.no_fail hP h2 hm.2
  | _, _, _, _, .seq_stop h _, hm => by
      simp only [Expr.mayFail, Bool.or_eq_false_iff] at hm
      exact Eval.no_fail hP h hm.1
  | _, _, _, _, .prim_ok _, hm => by
      simp only [Expr.mayFail, Bool.or_eq_false_iff] at hm
      exact Prim.apply_ne_fail hm.1 _
  | _, _, _, _, .prim_stop hl, hm => by
      have ih := EvalList.no_fail hP hl
      simp only [Expr.mayFail, Bool.or_eq_false_iff] at hm
      intro h; subst h; exact ih hm.2 rfl
  | _, _, _, _, .heap_ok (op := op) (vs := vs) (s₁ := s₁) _, _ => by
      rcases HeapOp.apply_res op vs s₁.g with ⟨v, hv⟩ | hv <;> simp [hv]
  | _, _, _, _, .heap_stop hl, hm => by
      have ih := EvalList.no_fail hP hl
      simp only [Expr.mayFail] at hm
      intro h; subst h; exact ih hm rfl
  | _, _, _, _, .call_ok (f := f) (fn := fn) _ hc hb, hm => by
      have ih := Eval.no_fail hP hb
      simp only [Expr.mayFail, Bool.or_eq_false_iff] at hm
      unfold Prog.callable at hc
      split at hc
      · next fn' hf =>
        split at hc
        · simp only [Option.some.injEq] at hc; subst hc
          rw [hf] at hm
          have hmem : fn' ∈ P.fns := List.mem_of_getElem? hf
          exact retOf_ne_fail (ih (hP fn' hmem hm.1))
        · simp at hc
      · simp at hc
  | _, _, _, _, .call_bad _ _, _ => by simp
  | _, _, _, _, .call_stop hl, hm => by
      have ih := EvalList.no_fail hP hl
      simp only [Expr.mayFail, Bool.or_eq_false_iff] at hm
      intro h; subst h; exact ih hm.2 rfl
  | _, _, _, _, .ite_ok _ h2, hm => by
      simp only [Expr.mayFail, Bool.or_eq_false_iff] at hm
      exact Eval.no_fail hP h2 hm.1
  | _, _, _, _, .ite_fail _ h2, hm => by
      simp only [Expr.mayFail, Bool.or_eq_false_iff] at hm
      exact Eval.no_fail hP h2 hm.2
  | _, _, _, _, .ite_stop _ _ hf, _ => hf
  | _, _, _, _, .for_ok _ h2, hm => by
      simp only [Expr.mayFail, Bool.or_eq_false_iff] at hm
      exact EvalFor.no_fail hP h2 hm.2
  | _, _, _, _, .for_type _ _, _ => by simp
  | _, _, _, _, .for_stop h _, hm => by
      simp only [Expr.mayFail, Bool.or_eq_false_iff] at hm
      exact Eval.no_fail hP h hm.1
  | _, _, _, _, .loop_ok _ h2, hm => Eval.no_fail hP h2 hm
  | _, _, _, _, .loop_brk _, _ => by simp
  | _, _, _, _, .loop_stop h _ _, hm => Eval.no_fail hP h (by simpa [Expr.mayFail] using hm)
  | _, _, _, _, .brk, _ => by simp
  | _, _, _, _, .ret_ok _, _ => by simp
  | _, _, _, _, .ret_stop h _, hm => Eval.no_fail hP h (by simpa [Expr.mayFail] using hm)
  | _, _, _, _, .print_ok _ _, _ => by simp
  | _, _, _, _, .print_bad _ _, _ => by simp
  | _, _, _, _, .print_stop h _, hm => Eval.no_fail hP h (by simpa [Expr.mayFail] using hm)

theorem EvalList.no_fail {P : Prog} (hP : P.EffectSound) : ∀ {s es lr s'},
    EvalList P s es lr s' → Expr.mayFailList P es = false → lr ≠ .stop .fail
  | _, _, _, _, .nil, _ => by simp
  | _, _, _, _, .cons_ok _ _, _ => by simp
  | _, _, _, _, .cons_stop h _, hm => by
      have ih := Eval.no_fail hP h
      simp only [Expr.mayFailList, Bool.or_eq_false_iff] at hm
      intro h'; cases h'; exact ih hm.1 rfl
  | _, _, _, _, .cons_stop_tail _ h2, hm => by
      simp only [Expr.mayFailList, Bool.or_eq_false_iff] at hm
      exact EvalList.no_fail hP h2 hm.2

theorem EvalFor.no_fail {P : Prog} (hP : P.EffectSound) : ∀ {i filt body s vs acc r s'},
    EvalFor P i filt body s vs acc r s' → body.mayFail P = false → r ≠ .fail
  | _, _, _, _, _, _, _, _, .done, _ => by simp
  | _, _, _, _, _, _, _, _, .bad_slot _, _ => by simp
  | _, _, _, _, _, _, _, _, .skip _ _ h, hm => EvalFor.no_fail hP h hm
  | _, _, _, _, _, _, _, _, .filt_stop _ _ _ hf, _ => hf
  | _, _, _, _, _, _, _, _, .step _ _ _ h, hm => EvalFor.no_fail hP h hm
  | _, _, _, _, _, _, _, _, .body_stop _ _ h _, hm => Eval.no_fail hP h hm
end

/-- **`<decides>` soundness.** In an effect-sound program, a call to a
    function that is not `<decides>`, with arguments that cannot fail,
    never fails. -/
theorem call_no_fail {P : Prog} (hP : P.EffectSound) {s f es r s' fn}
    (hf : P.fns[f]? = some fn) (hd : fn.decides = false)
    (hes : Expr.mayFailList P es = false) (h : Eval P s (.call f es) r s') : r ≠ .fail :=
  Eval.no_fail hP h (by simp [Expr.mayFail, hf, hd, hes])

/-- A program whose `Main` is not `<decides>` never ends in failure. -/
theorem Runs.no_fail {P : Prog} (hP : P.EffectSound) {fn r out}
    (hm : P.fns[P.main]? = some fn) (hd : fn.decides = false) (h : Runs P r out) : r ≠ .fail := by
  obtain ⟨_, _, h⟩ := h
  exact call_no_fail hP hm hd rfl h

end OpenVerse
