/-
  OpenVerse — soundness of the effects that exclude `writes` (#35).

  A Verse function whose effects exclude `writes` (`<computes>`, `<reads>`,
  `<allocates>`) cannot change a `var` field of an existing object.
  `Expr.writesHeap` is the analysis the elaborator enforces: an expression
  writes if it contains a field write (`HeapOp.set`) or calls a function
  marked `writes`, anywhere, failure contexts included (a write in a failure
  context that succeeds persists).

  `Eval.no_writes`: an expression that does not write keeps every existing
  object, at its address, with its fields (`Glob.keeps`); it may only add
  objects. It holds in any program whose functions marked as not writing
  have bodies that do not write (`Prog.WriteSound`).
-/
import OpenVerse.Core.Adequacy

namespace OpenVerse

/-- Only `set` changes an existing object. -/
def HeapOp.writes : HeapOp → Bool
  | .set _ => true
  | _ => false

mutual
/-- Can `e` change an existing object? -/
def Expr.writesHeap (P : Prog) : Expr → Bool
  | .lit _ | .local _ | .brk => false
  | .assign _ e | .ret e | .print e | .loop e => e.writesHeap P
  | .seq a b => a.writesHeap P || b.writesHeap P
  | .prim _ es => Expr.writesHeapList P es
  | .heap op es => op.writes || Expr.writesHeapList P es
  | .call f es =>
    (match P.fns[f]? with
      | some fn => fn.writes
      | none => false) || Expr.writesHeapList P es
  | .ite c t e => c.writesHeap P || t.writesHeap P || e.writesHeap P
  | .forE _ it filt body => it.writesHeap P || filt.writesHeap P || body.writesHeap P
/-- Can some expression of the list change an existing object? -/
def Expr.writesHeapList (P : Prog) : List Expr → Bool
  | [] => false
  | e :: es => e.writesHeap P || Expr.writesHeapList P es
end

/-- Every function marked as not writing has a body that does not write. -/
def Prog.WriteSound (P : Prog) : Prop :=
  ∀ fn ∈ P.fns, fn.writes = false → fn.body.writesHeap P = false

/-- Every object of `g` is in `g'`, at the same address, with the same fields. -/
def Glob.keeps (g g' : Glob) : Prop :=
  ∀ (a : Nat) (o : Obj), g.heap[a]? = some o → g'.heap[a]? = some o

theorem Glob.keeps_refl (g : Glob) : g.keeps g := fun _ _ h => h

theorem Glob.keeps_trans {g₁ g₂ g₃ : Glob} (h₁ : g₁.keeps g₂) (h₂ : g₂.keeps g₃) : g₁.keeps g₃ :=
  fun a o h => h₂ a o (h₁ a o h)

theorem Glob.keeps_of_heap {g g' : Glob} (h : g'.heap = g.heap) : g.keeps g' := by
  intro a o ho; rw [h]; exact ho

theorem writeSlot_g {s s' : St} {i : Nat} {v : Value} (h : writeSlot s i v = some s') : s'.g = s.g := by
  unfold writeSlot at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp at h

/-- A heap operation other than `set` keeps every existing object. -/
theorem HeapOp.apply_keeps {op : HeapOp} (h : op.writes = false) (vs : List Value) (g : Glob) :
    g.keeps (op.apply vs g).2 := by
  cases op with
  | set k => simp [HeapOp.writes] at h
  | new t =>
    intro a o ho
    show (g.heap ++ [⟨t, vs⟩])[a]? = some o
    rw [List.getElem?_append_left (lt_of_getElem?_some ho)]; exact ho
  | get k | tag | isTag us =>
    apply Glob.keeps_of_heap
    unfold HeapOp.apply
    split <;> (try split) <;> (try split) <;> simp_all
where
  lt_of_getElem?_some {l : List Obj} {i : Nat} {o : Obj} (h : l[i]? = some o) : i < l.length := by
    rcases Nat.lt_or_ge i l.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h

mutual
/-- **No writes.** An expression that does not write keeps every existing
    object, in a write-sound program. -/
theorem Eval.no_writes {P : Prog} (hP : P.WriteSound) : ∀ {s e r s'},
    Eval P s e r s' → e.writesHeap P = false → s.g.keeps s'.g
  | _, _, _, _, .lit, _ | _, _, _, _, .local, _ | _, _, _, _, .brk, _ => Glob.keeps_refl _
  | _, _, _, _, .assign_ok h hw, hm => by
    rw [writeSlot_g hw]; exact Eval.no_writes hP h (by simpa [Expr.writesHeap] using hm)
  | _, _, _, _, .assign_bad h _, hm | _, _, _, _, .assign_stop h _, hm =>
    Eval.no_writes hP h (by simpa [Expr.writesHeap] using hm)
  | _, _, _, _, .seq_ok h₁ h₂, hm => by
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    exact Glob.keeps_trans (Eval.no_writes hP h₁ hm.1) (Eval.no_writes hP h₂ hm.2)
  | _, _, _, _, .seq_stop h _, hm => by
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    exact Eval.no_writes hP h hm.1
  | _, _, _, _, .prim_ok hl, hm | _, _, _, _, .prim_stop hl, hm =>
    EvalList.no_writes hP hl (by simpa [Expr.writesHeap] using hm)
  | _, _, _, _, .heap_ok (op := op) (vs := vs) (s₁ := s₁) hl, hm => by
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    exact Glob.keeps_trans (EvalList.no_writes hP hl hm.2) (HeapOp.apply_keeps hm.1 vs s₁.g)
  | _, _, _, _, .heap_stop hl, hm => by
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    exact EvalList.no_writes hP hl hm.2
  | _, _, _, _, .call_ok (f := f) hl hc hb, hm => by
    have ih := Eval.no_writes hP hb
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    have h₁ := EvalList.no_writes hP hl hm.2
    unfold Prog.callable at hc
    split at hc
    · next fn' hf =>
      split at hc
      · simp only [Option.some.injEq] at hc; subst hc
        rw [hf] at hm
        have hmem : fn' ∈ P.fns := List.mem_of_getElem? hf
        have h₂ := ih (hP fn' hmem hm.1)
        exact fun a o ho => h₂ a o (h₁ a o ho)
      · simp at hc
    · simp at hc
  | _, _, _, _, .call_bad hl _, hm | _, _, _, _, .call_stop hl, hm => by
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    exact EvalList.no_writes hP hl hm.2
  | _, _, _, _, .ite_ok h₁ h₂, hm => by
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    exact Glob.keeps_trans (Eval.no_writes hP h₁ hm.1.1) (Eval.no_writes hP h₂ hm.1.2)
  -- rollback: the `else` branch starts from the original state
  | _, _, _, _, .ite_fail _ h₂, hm => by
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    exact Eval.no_writes hP h₂ hm.2
  | _, _, _, _, .ite_stop h _ _, hm => by
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    exact Eval.no_writes hP h hm.1.1
  | _, _, _, _, .for_ok h₁ h₂, hm => by
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    exact Glob.keeps_trans (Eval.no_writes hP h₁ hm.1.1) (EvalFor.no_writes hP h₂ hm.1.2 hm.2)
  | _, _, _, _, .for_type h _, hm | _, _, _, _, .for_stop h _, hm => by
    simp only [Expr.writesHeap, Bool.or_eq_false_iff] at hm
    exact Eval.no_writes hP h hm.1.1
  | _, _, _, _, .loop_ok h₁ h₂, hm =>
    Glob.keeps_trans (Eval.no_writes hP h₁ (by simpa [Expr.writesHeap] using hm)) (Eval.no_writes hP h₂ hm)
  | _, _, _, _, .loop_brk h, hm | _, _, _, _, .loop_stop h _ _, hm =>
    Eval.no_writes hP h (by simpa [Expr.writesHeap] using hm)
  | _, _, _, _, .ret_ok h, hm | _, _, _, _, .ret_stop h _, hm =>
    Eval.no_writes hP h (by simpa [Expr.writesHeap] using hm)
  | _, _, _, _, .print_ok h _, hm =>
    Glob.keeps_trans (Eval.no_writes hP h (by simpa [Expr.writesHeap] using hm)) (Glob.keeps_of_heap rfl)
  | _, _, _, _, .print_bad h _, hm | _, _, _, _, .print_stop h _, hm =>
    Eval.no_writes hP h (by simpa [Expr.writesHeap] using hm)

theorem EvalList.no_writes {P : Prog} (hP : P.WriteSound) : ∀ {s es lr s'},
    EvalList P s es lr s' → Expr.writesHeapList P es = false → s.g.keeps s'.g
  | _, _, _, _, .nil, _ => Glob.keeps_refl _
  | _, _, _, _, .cons_ok h₁ h₂, hm => by
    simp only [Expr.writesHeapList, Bool.or_eq_false_iff] at hm
    exact Glob.keeps_trans (Eval.no_writes hP h₁ hm.1) (EvalList.no_writes hP h₂ hm.2)
  | _, _, _, _, .cons_stop h _, hm => by
    simp only [Expr.writesHeapList, Bool.or_eq_false_iff] at hm
    exact Eval.no_writes hP h hm.1
  | _, _, _, _, .cons_stop_tail h₁ h₂, hm => by
    simp only [Expr.writesHeapList, Bool.or_eq_false_iff] at hm
    exact Glob.keeps_trans (Eval.no_writes hP h₁ hm.1) (EvalList.no_writes hP h₂ hm.2)

theorem EvalFor.no_writes {P : Prog} (hP : P.WriteSound) : ∀ {i filt body s vs acc r s'},
    EvalFor P i filt body s vs acc r s' → filt.writesHeap P = false → body.writesHeap P = false →
    s.g.keeps s'.g
  | _, _, _, _, _, _, _, _, .done, _, _ | _, _, _, _, _, _, _, _, .bad_slot _, _, _ => Glob.keeps_refl _
  -- rollback: a failed filter restores the state after binding the element
  | _, _, _, _, _, _, _, _, .skip hw _ h, hf, hb => by
    have := EvalFor.no_writes hP h hf hb
    rwa [writeSlot_g hw] at this
  | _, _, _, _, _, _, _, _, .filt_stop hw h _ _, hf, _ => by
    have := Eval.no_writes hP h hf
    rwa [writeSlot_g hw] at this
  | _, _, _, _, _, _, _, _, .step hw h₁ h₂ h₃, hf, hb => by
    have := Glob.keeps_trans (Eval.no_writes hP h₁ hf) (Glob.keeps_trans (Eval.no_writes hP h₂ hb) (EvalFor.no_writes hP h₃ hf hb))
    rwa [writeSlot_g hw] at this
  | _, _, _, _, _, _, _, _, .body_stop hw h₁ h₂ _, hf, hb => by
    have := Glob.keeps_trans (Eval.no_writes hP h₁ hf) (Eval.no_writes hP h₂ hb)
    rwa [writeSlot_g hw] at this
end

/-- **No writes, for calls.** In a write-sound program, a call of a function
    marked as not writing, with arguments that do not write, leaves every
    existing object as it was. -/
theorem call_no_writes {P : Prog} (hP : P.WriteSound) {s f es r s' fn}
    (hf : P.fns[f]? = some fn) (hw : fn.writes = false)
    (hes : Expr.writesHeapList P es = false) (h : Eval P s (.call f es) r s') : s.g.keeps s'.g :=
  Eval.no_writes hP h (by simp [Expr.writesHeap, hf, hw, hes])

end OpenVerse
