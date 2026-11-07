/-
  OpenVerse — well-scoped programs cannot raise scoping errors.

  `Prog.WellScoped` is exactly what the C loader (`runtime/src/load.c`)
  validates before it runs a program: every slot index of a function is
  below its frame size, every call names an existing function with that
  function's arity, and every function has at least as many slots as
  parameters. The QuickProof law `proofs/quickproof/loader` proves that the
  loader accepts only node tables with these properties.

  `Eval.scoped_ok`: in a well-scoped program, evaluation never produces a
  slot error or a call error, and never changes the size of the frame. So
  the C runtime may use fixed-size frames and needs no slot checks of its
  own on loaded programs.
-/
import OpenVerse.Core.Adequacy

namespace OpenVerse

mutual
/-- All slots are below `n` and every call has the arity of its callee. -/
def Expr.scoped (P : Prog) (n : Nat) : Expr → Bool
  | .lit _ => true
  | .local i => decide (i < n)
  | .brk => true
  | .assign i e => decide (i < n) && e.scoped P n
  | .ret e => e.scoped P n
  | .print e => e.scoped P n
  | .loop e => e.scoped P n
  | .seq a b => a.scoped P n && b.scoped P n
  | .prim _ es => Expr.scopedList P n es
  | .heap _ es => Expr.scopedList P n es
  | .call f es =>
    (match P.fns[f]? with
      | some fn => fn.arity == es.length
      | none => false) && Expr.scopedList P n es
  | .ite c t e => c.scoped P n && t.scoped P n && e.scoped P n
  | .forE i it filt body =>
    decide (i < n) && it.scoped P n && filt.scoped P n && body.scoped P n
def Expr.scopedList (P : Prog) (n : Nat) : List Expr → Bool
  | [] => true
  | e :: es => e.scoped P n && Expr.scopedList P n es
end

/-- What the loader checks of every function. -/
def Prog.WellScoped (P : Prog) : Prop :=
  ∀ fn ∈ P.fns, fn.arity ≤ fn.nslots ∧ fn.body.scoped P fn.nslots = true

/-- The two errors that well-scoped programs cannot raise. -/
def Res.scopeErr : Res → Bool
  | .err .slot => true
  | .err .call => true
  | _ => false

theorem Prim.apply_scopeErr (p : Prim) (vs : List Value) : (p.apply vs).scopeErr = false := by
  have h1 : ∀ i, (Res.ofInt i).scopeErr = false := by intro i; unfold Res.ofInt; split <;> rfl
  have h2 : ∀ b v, (cmpRes b v).scopeErr = false := by intro b v; unfold cmpRes; split <;> rfl
  have h3 : ∀ v, (toStrValue v).scopeErr = false := by
    intro v; unfold toStrValue; split <;> (try split) <;> rfl
  have h4 : ∀ r a, (VFloat.toIntRes r a).scopeErr = false := by
    intro r a; unfold VFloat.toIntRes; split <;> rfl
  unfold Prim.apply
  split <;> (repeat' split) <;> first | rfl | exact h1 _ | exact h2 _ _ | exact h3 _ | exact h4 _ _

theorem retOf_scopeErr {r : Res} (h : r.scopeErr = false) : (retOf r).scopeErr = false := by
  cases r <;> simp_all [retOf, Res.scopeErr]

theorem writeSlot_length {s : St} {i v s'} (h : writeSlot s i v = some s') :
    s'.fr.length = s.fr.length := by
  unfold writeSlot at h; split at h
  · simp only [Option.some.injEq] at h; subst h; simp
  · simp at h

theorem writeSlot_isSome {s : St} {i v} (h : i < s.fr.length) : writeSlot s i v ≠ none := by
  simp [writeSlot, h]

theorem EvalList.length_ok {P : Prog} : ∀ {s es lr s'}, EvalList P s es lr s' →
    ∀ vs, lr = .ok vs → vs.length = es.length
  | _, _, _, _, .nil, _, h => by cases h; rfl
  | _, _, _, _, .cons_ok _ hl, _, h => by
      cases h; simp [EvalList.length_ok hl _ rfl]
  | _, _, _, _, .cons_stop _ _, _, h => by cases h
  | _, _, _, _, .cons_stop_tail _ _, _, h => by cases h

mutual
theorem Eval.scoped_ok {P : Prog} (hP : P.WellScoped) : ∀ {s e r s'},
    Eval P s e r s' → e.scoped P s.fr.length = true →
    r.scopeErr = false ∧ s'.fr.length = s.fr.length
  | _, _, _, _, .lit, _ => ⟨rfl, rfl⟩
  | _, _, _, _, .local (s := s) (i := i), hs => by
      simp only [Expr.scoped, decide_eq_true_eq] at hs
      refine ⟨?_, rfl⟩
      simp [readSlot, List.getElem?_eq_getElem hs, Res.scopeErr]
  | _, _, _, _, .assign_ok h hw, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped, Bool.and_eq_true, decide_eq_true_eq] at hs
      exact ⟨rfl, (writeSlot_length hw).trans (ih hs.2).2⟩
  | _, _, _, _, .assign_bad h hw, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped, Bool.and_eq_true, decide_eq_true_eq] at hs
      exact absurd hw (writeSlot_isSome (by rw [(ih hs.2).2]; exact hs.1))
  | _, _, _, _, .assign_stop h _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      exact ih hs.2
  | _, _, _, _, .seq_ok h1 h2, hs => by
      have ih1 := Eval.scoped_ok hP h1
      have ih2 := Eval.scoped_ok hP h2
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      have e1 := (ih1 hs.1).2
      have := ih2 (by rw [e1]; exact hs.2)
      exact ⟨this.1, this.2.trans e1⟩
  | _, _, _, _, .seq_stop h _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      exact ih hs.1
  | _, _, _, _, .prim_ok hl, hs => by
      have ih := EvalList.scoped_ok hP hl
      exact ⟨Prim.apply_scopeErr _ _, (ih hs).2⟩
  | _, _, _, _, .prim_stop hl, hs => by
      have ih := EvalList.scoped_ok hP hl
      exact ⟨(ih hs).1 _ rfl, (ih hs).2⟩
  | _, _, _, _, .heap_ok (op := op) (vs := vs) (s₁ := s₁) hl, hs => by
      have ih := EvalList.scoped_ok hP hl
      refine ⟨?_, (ih hs).2⟩
      rcases HeapOp.apply_res op vs s₁.g with ⟨v, hv⟩ | hv | hv <;> simp [hv, Res.scopeErr]
  | _, _, _, _, .heap_stop hl, hs => by
      have ih := EvalList.scoped_ok hP hl
      exact ⟨(ih hs).1 _ rfl, (ih hs).2⟩
  | _, _, _, _, .call_ok (f := f) (es := es) (vs := vs) (fn := fn) hl hc hb, hs => by
      have ihl := EvalList.scoped_ok hP hl
      have ihb := Eval.scoped_ok hP hb
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      have hlen := EvalList.length_ok hl _ rfl
      unfold Prog.callable at hc
      split at hc
      · next fn' hf =>
        split at hc
        · next har =>
          simp only [Option.some.injEq] at hc; subst hc
          obtain ⟨hle, hbody⟩ := hP fn' (List.mem_of_getElem? hf)
          have hfr : (frameOf fn' vs).length = fn'.nslots := by
            simp [frameOf]; omega
          have := ihb (by simpa [hfr] using hbody)
          exact ⟨retOf_scopeErr this.1, (ihl hs.2).2⟩
        · simp at hc
      · simp at hc
  | _, _, _, _, .call_bad (f := f) (es := es) (vs := vs) hl hc, hs => by
      have hlen := EvalList.length_ok hl _ rfl
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      unfold Prog.callable at hc
      split at hc
      · next fn' hf =>
        rw [hf] at hs
        simp only [beq_iff_eq] at hs
        split at hc
        · simp at hc
        · next har => exact absurd (hs.1.trans hlen.symm) har
      · next hf => rw [hf] at hs; simp at hs
  | _, _, _, _, .call_stop hl, hs => by
      have ih := EvalList.scoped_ok hP hl
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      exact ⟨(ih hs.2).1 _ rfl, (ih hs.2).2⟩
  | _, _, _, _, .ite_ok h1 h2, hs => by
      have ih1 := Eval.scoped_ok hP h1
      have ih2 := Eval.scoped_ok hP h2
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      have e1 := (ih1 hs.1.1).2
      have := ih2 (by rw [e1]; exact hs.1.2)
      exact ⟨this.1, this.2.trans e1⟩
  | _, _, _, _, .ite_fail _ h2, hs => by
      have ih2 := Eval.scoped_ok hP h2
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      exact ih2 hs.2
  | _, _, _, _, .ite_stop h _ _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      exact ih hs.1.1
  | _, _, _, _, .for_ok h1 h2, hs => by
      have ih1 := Eval.scoped_ok hP h1
      have ih2 := EvalFor.scoped_ok hP h2
      simp only [Expr.scoped, Bool.and_eq_true, decide_eq_true_eq] at hs
      have e1 := (ih1 hs.1.1.2).2
      have := ih2 (by rw [e1]; exact hs.1.1.1) (by rw [e1]; exact hs.1.2) (by rw [e1]; exact hs.2)
      exact ⟨this.1, this.2.trans e1⟩
  | _, _, _, _, .for_type h _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      exact ⟨rfl, (ih hs.1.1.2).2⟩
  | _, _, _, _, .for_stop h _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped, Bool.and_eq_true] at hs
      exact ih hs.1.1.2
  | _, _, _, _, .loop_ok h1 h2, hs => by
      have ih1 := Eval.scoped_ok hP h1
      have ih2 := Eval.scoped_ok hP h2
      have hs' : _ = true := hs
      simp only [Expr.scoped] at hs'
      have e1 := (ih1 hs').2
      have := ih2 (by rw [e1]; exact hs)
      exact ⟨this.1, this.2.trans e1⟩
  | _, _, _, _, .loop_brk h, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped] at hs
      exact ⟨rfl, (ih hs).2⟩
  | _, _, _, _, .loop_stop h _ _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped] at hs
      exact ih hs
  | _, _, _, _, .brk, _ => ⟨rfl, rfl⟩
  | _, _, _, _, .ret_ok h, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped] at hs
      exact ⟨rfl, (ih hs).2⟩
  | _, _, _, _, .ret_stop h _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped] at hs
      exact ih hs
  | _, _, _, _, .print_ok h _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped] at hs
      exact ⟨rfl, (ih hs).2⟩
  | _, _, _, _, .print_bad h _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped] at hs
      exact ⟨rfl, (ih hs).2⟩
  | _, _, _, _, .print_stop h _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scoped] at hs
      exact ih hs

theorem EvalList.scoped_ok {P : Prog} (hP : P.WellScoped) : ∀ {s es lr s'},
    EvalList P s es lr s' → Expr.scopedList P s.fr.length es = true →
    (∀ r, lr = .stop r → r.scopeErr = false) ∧ s'.fr.length = s.fr.length
  | _, _, _, _, .nil, _ => ⟨fun _ h => (by cases h), rfl⟩
  | _, _, _, _, .cons_ok h1 h2, hs => by
      have ih1 := Eval.scoped_ok hP h1
      have ih2 := EvalList.scoped_ok hP h2
      simp only [Expr.scopedList, Bool.and_eq_true] at hs
      have e1 := (ih1 hs.1).2
      have := ih2 (by rw [e1]; exact hs.2)
      exact ⟨fun _ h => (by cases h), this.2.trans e1⟩
  | _, _, _, _, .cons_stop h _, hs => by
      have ih := Eval.scoped_ok hP h
      simp only [Expr.scopedList, Bool.and_eq_true] at hs
      exact ⟨fun _ h' => by cases h'; exact (ih hs.1).1, (ih hs.1).2⟩
  | _, _, _, _, .cons_stop_tail h1 h2, hs => by
      have ih1 := Eval.scoped_ok hP h1
      have ih2 := EvalList.scoped_ok hP h2
      simp only [Expr.scopedList, Bool.and_eq_true] at hs
      have e1 := (ih1 hs.1).2
      have := ih2 (by rw [e1]; exact hs.2)
      exact ⟨this.1, this.2.trans e1⟩

theorem EvalFor.scoped_ok {P : Prog} (hP : P.WellScoped) : ∀ {i filt body s vs acc r s'},
    EvalFor P i filt body s vs acc r s' →
    i < s.fr.length → filt.scoped P s.fr.length = true → body.scoped P s.fr.length = true →
    r.scopeErr = false ∧ s'.fr.length = s.fr.length
  | _, _, _, _, _, _, _, _, .done, _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .bad_slot hw, hi, _, _ => absurd hw (writeSlot_isSome hi)
  | _, _, _, _, _, _, _, _, .skip hw _ h, hi, hf, hb => by
      have ih := EvalFor.scoped_ok hP h
      have e0 := writeSlot_length hw
      have := ih (by rw [e0]; exact hi) (by rw [e0]; exact hf) (by rw [e0]; exact hb)
      exact ⟨this.1, this.2.trans e0⟩
  | _, _, _, _, _, _, _, _, .filt_stop hw h _ _, hi, hf, hb => by
      have ih := Eval.scoped_ok hP h
      have e0 := writeSlot_length hw
      have := ih (by rw [e0]; exact hf)
      exact ⟨this.1, this.2.trans e0⟩
  | _, _, _, _, _, _, _, _, .step hw h1 h2 h3, hi, hf, hb => by
      have ih1 := Eval.scoped_ok hP h1
      have ih2 := Eval.scoped_ok hP h2
      have ih3 := EvalFor.scoped_ok hP h3
      have e0 := writeSlot_length hw
      have e1 := (ih1 (by rw [e0]; exact hf)).2
      have e2 := (ih2 (by rw [e1, e0]; exact hb)).2
      have := ih3 (by rw [e2, e1, e0]; exact hi) (by rw [e2, e1, e0]; exact hf)
        (by rw [e2, e1, e0]; exact hb)
      exact ⟨this.1, this.2.trans (e2.trans (e1.trans e0))⟩
  | _, _, _, _, _, _, _, _, .body_stop hw h1 h2 _, hi, hf, hb => by
      have ih1 := Eval.scoped_ok hP h1
      have ih2 := Eval.scoped_ok hP h2
      have e0 := writeSlot_length hw
      have e1 := (ih1 (by rw [e0]; exact hf)).2
      have := ih2 (by rw [e1, e0]; exact hb)
      exact ⟨this.1, this.2.trans (e1.trans e0)⟩
end

/-- A well-scoped program whose `Main` takes no arguments never raises a
    slot or call error. -/
theorem Runs.scoped_ok {P : Prog} (hP : P.WellScoped) {fn r out}
    (hm : P.fns[P.main]? = some fn) (h0 : fn.arity = 0) (h : Runs P r out) :
    r.scopeErr = false := by
  obtain ⟨_, _, h⟩ := h
  refine (Eval.scoped_ok hP h ?_).1
  simp [Expr.scoped, Expr.scopedList, hm, h0]

end OpenVerse
