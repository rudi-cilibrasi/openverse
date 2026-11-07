/-
  OpenVerse — `break` never escapes a loop.

  `Expr.brkSafe` holds when every `break` is inside a `loop` of the same
  function body (the elaborator only emits `break` inside `loop`, and a `for`
  body or a nested function does not count as inside). In a program whose
  function bodies are all `brkSafe`, evaluation never produces
  `err .control`, and no expression outside a loop ends in `brk`
  (`Eval.no_control`). Together with `Prog.accepted`, the only runtime
  errors left to a checked program are integer overflow and `Err()`.
-/
import OpenVerse.Core.Adequacy

namespace OpenVerse

mutual
/-- No `break` outside a `loop` (`inLoop` says whether we are inside one). -/
def Expr.brkSafe (inLoop : Bool) : Expr → Bool
  | .lit _ => true
  | .local _ => true
  | .brk => inLoop
  | .assign _ e => e.brkSafe inLoop
  | .ret e => e.brkSafe inLoop
  | .print e => e.brkSafe inLoop
  | .loop b => b.brkSafe true
  | .seq a b => a.brkSafe inLoop && b.brkSafe inLoop
  | .prim _ es => Expr.brkSafeList inLoop es
  | .heap _ es => Expr.brkSafeList inLoop es
  | .call _ es => Expr.brkSafeList inLoop es
  | .ite c t e => c.brkSafe inLoop && t.brkSafe inLoop && e.brkSafe inLoop
  | .forE _ it filt body => it.brkSafe inLoop && filt.brkSafe inLoop && body.brkSafe inLoop
def Expr.brkSafeList (inLoop : Bool) : List Expr → Bool
  | [] => true
  | e :: es => e.brkSafe inLoop && Expr.brkSafeList inLoop es
end

/-- Every function body is `brkSafe` outside any loop. -/
def Prog.checkControl (P : Prog) : Bool := P.fns.all fun fn => fn.body.brkSafe false

/-- The outcome is not a control error, and not `brk` unless we are in a loop. -/
def Res.ctlOK (inLoop : Bool) : Res → Prop
  | .brk => inLoop = true
  | .err .control => False
  | _ => True

theorem retOf_ctlOK {r : Res} (h : r.ctlOK false) : (retOf r).ctlOK false := by
  cases r with
  | err k => cases k <;> simp_all [retOf, Res.ctlOK]
  | brk => simp [Res.ctlOK] at h
  | _ => simp [retOf, Res.ctlOK]

theorem ctlOK_mono {r : Res} {b : Bool} (h : r.ctlOK false) : r.ctlOK b := by
  cases r with
  | err k => cases k <;> simp_all [Res.ctlOK]
  | brk => simp [Res.ctlOK] at h
  | _ => simp [Res.ctlOK]

theorem ctlOK_of_not_err {r : Res} {b : Bool} (h1 : r ≠ .brk) (h2 : r ≠ .err .control) : r.ctlOK b := by
  cases r with
  | err k => cases k <;> simp_all [Res.ctlOK]
  | brk => exact absurd rfl h1
  | _ => simp [Res.ctlOK]

theorem apply_ctlOK (op : Prim) (vs : List Value) (b : Bool) : (op.apply vs).ctlOK b := by
  have h1 : ∀ i, (Res.ofInt i).ctlOK b := by intro i; unfold Res.ofInt; split <;> simp [Res.ctlOK]
  have h2 : ∀ c v, (cmpRes c v).ctlOK b := by intro c v; unfold cmpRes; split <;> simp [Res.ctlOK]
  have h3 : ∀ v, (toStrValue v).ctlOK b := by
    intro v; unfold toStrValue; split <;> (try split) <;> simp [Res.ctlOK]
  unfold Prim.apply
  split <;> (repeat' split) <;> first | exact h1 _ | exact h2 _ _ | exact h3 _ | simp [Res.ctlOK]

theorem readSlot_ctlOK (s : St) (i : Nat) (b : Bool) : (readSlot s i).ctlOK b := by
  unfold readSlot; split <;> simp [Res.ctlOK]

mutual
theorem Eval.no_control {P : Prog} (hP : P.checkControl = true) : ∀ {s e r s'},
    Eval P s e r s' → ∀ (b : Bool), e.brkSafe b = true → r.ctlOK b
  | _, _, _, _, .lit, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, .local, _, _ => readSlot_ctlOK _ _ _
  | _, _, _, _, .assign_ok _ _, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, .assign_bad _ _, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, .assign_stop h _, _, hb => Eval.no_control hP h _ (by simpa [Expr.brkSafe] using hb)
  | _, _, _, _, .seq_ok _ h2, _, hb => by
      have ih := Eval.no_control hP h2
      simp only [Expr.brkSafe, Bool.and_eq_true] at hb; exact ih _ hb.2
  | _, _, _, _, .seq_stop h _, _, hb => by
      have ih := Eval.no_control hP h
      simp only [Expr.brkSafe, Bool.and_eq_true] at hb; exact ih _ hb.1
  | _, _, _, _, .prim_ok _, _, _ => apply_ctlOK _ _ _
  | _, _, _, _, .prim_stop hl, _, hb => EvalList.no_control hP hl _ _ rfl hb
  | _, _, _, _, .heap_ok (op := op) (vs := vs) (s₁ := s₁) _, _, _ => by
      rcases HeapOp.apply_res op vs s₁.g with ⟨v, hv⟩ | hv <;> simp [hv, Res.ctlOK]
  | _, _, _, _, .heap_stop hl, _, hb => EvalList.no_control hP hl _ _ rfl hb
  | _, _, _, _, .call_ok (fn := fn) _ hc hb', _, _ => by
      have ih := Eval.no_control hP hb'
      unfold Prog.callable at hc
      split at hc
      · next fn' hf =>
        split at hc
        · simp only [Option.some.injEq] at hc; subst hc
          have hfn := List.all_eq_true.mp hP fn' (List.mem_of_getElem? hf)
          exact ctlOK_mono (retOf_ctlOK (ih _ hfn))
        · simp at hc
      · simp at hc
  | _, _, _, _, .call_bad _ _, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, .call_stop hl, _, hb => EvalList.no_control hP hl _ _ rfl hb
  | _, _, _, _, .ite_ok _ h2, _, hb => by
      have ih := Eval.no_control hP h2
      simp only [Expr.brkSafe, Bool.and_eq_true] at hb; exact ih _ hb.1.2
  | _, _, _, _, .ite_fail _ h2, _, hb => by
      have ih := Eval.no_control hP h2
      simp only [Expr.brkSafe, Bool.and_eq_true] at hb; exact ih _ hb.2
  | _, _, _, _, .ite_stop h _ _, _, hb => by
      have ih := Eval.no_control hP h
      simp only [Expr.brkSafe, Bool.and_eq_true] at hb; exact ih _ hb.1.1
  | _, _, _, _, .for_ok _ h2, _, hb => by
      have ih := EvalFor.no_control hP h2
      simp only [Expr.brkSafe, Bool.and_eq_true] at hb; exact ih _ hb.1.2 hb.2
  | _, _, _, _, .for_type _ _, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, .for_stop h _, _, hb => by
      have ih := Eval.no_control hP h
      simp only [Expr.brkSafe, Bool.and_eq_true] at hb; exact ih _ hb.1.1
  | _, _, _, _, .loop_ok _ h2, _, hb => Eval.no_control hP h2 _ hb
  | _, _, _, _, .loop_brk _, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, .loop_stop (r := r) h _ hbr, _, hb => by
      have ih := Eval.no_control hP h
      simp only [Expr.brkSafe] at hb
      have := ih _ hb
      cases r with
      | err k => cases k <;> simp_all [Res.ctlOK]
      | brk => exact absurd rfl hbr
      | _ => simp [Res.ctlOK]
  | _, _, _, _, .brk, _, hb => by simpa [Expr.brkSafe, Res.ctlOK] using hb
  | _, _, _, _, .ret_ok _, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, .ret_stop h _, _, hb => Eval.no_control hP h _ (by simpa [Expr.brkSafe] using hb)
  | _, _, _, _, .print_ok _ _, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, .print_bad _ _, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, .print_stop h _, _, hb => Eval.no_control hP h _ (by simpa [Expr.brkSafe] using hb)

theorem EvalList.no_control {P : Prog} (hP : P.checkControl = true) : ∀ {s es lr s'},
    EvalList P s es lr s' → ∀ (b : Bool) (r : Res), lr = .stop r → Expr.brkSafeList b es = true →
    r.ctlOK b
  | _, _, _, _, .nil, _, _, he, _ => by cases he
  | _, _, _, _, .cons_ok _ _, _, _, he, _ => by cases he
  | _, _, _, _, .cons_stop h _, _, _, he, hb => by
      have ih := Eval.no_control hP h
      cases he
      simp only [Expr.brkSafeList, Bool.and_eq_true] at hb; exact ih _ hb.1
  | _, _, _, _, .cons_stop_tail _ h2, _, _, he, hb => by
      have ih := EvalList.no_control hP h2
      simp only [Expr.brkSafeList, Bool.and_eq_true] at hb; exact ih _ _ he hb.2

theorem EvalFor.no_control {P : Prog} (hP : P.checkControl = true) : ∀ {i filt body s vs acc r s'},
    EvalFor P i filt body s vs acc r s' → ∀ (b : Bool), filt.brkSafe b = true → body.brkSafe b = true →
    r.ctlOK b
  | _, _, _, _, _, _, _, _, .done, _, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, _, _, _, _, .bad_slot _, _, _, _ => by simp [Res.ctlOK]
  | _, _, _, _, _, _, _, _, .skip _ _ h, _, hf, hb => EvalFor.no_control hP h _ hf hb
  | _, _, _, _, _, _, _, _, .filt_stop _ h _ _, _, hf, _ => Eval.no_control hP h _ hf
  | _, _, _, _, _, _, _, _, .step _ _ _ h, _, hf, hb => EvalFor.no_control hP h _ hf hb
  | _, _, _, _, _, _, _, _, .body_stop _ _ h _, _, _, hb => Eval.no_control hP h _ hb
end

/-- A program whose function bodies keep their `break`s inside loops never
    ends with a control error. -/
theorem Runs.no_control {P : Prog} (hP : P.checkControl = true) {r out} (h : Runs P r out) :
    r ≠ .err .control := by
  obtain ⟨_, _, h⟩ := h
  have := Eval.no_control hP h false (by simp [Expr.brkSafe, Expr.brkSafeList])
  intro he; subst he; exact this

end OpenVerse
