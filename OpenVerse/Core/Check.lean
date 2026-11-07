/-
  OpenVerse — decidable checks for the hypotheses of the core theorems.

  The front end is not verified. Instead, every program it produces is
  checked with these functions before it runs or is emitted, and each check
  is proved to imply the hypothesis of a theorem:

  * `Prog.checkEffectSound P = true → P.EffectSound`, so `Eval.no_fail`
    (`<decides>` soundness) applies to every program the front end accepts;
  * `Prog.checkWellScoped P = true → P.WellScoped`, so `Eval.scoped_ok`
    (no slot or call errors, fixed-size frames) applies;
  * `Prog.checkMain P = true` gives the facts about `Main` that
    `Runs.no_fail` and `Runs.scoped_ok` need;
  * `Prog.checkWriteSound P = true → P.WriteSound`, so `Eval.no_writes`
    (functions that exclude `writes` keep every object) applies.
-/
import OpenVerse.Core.Effects
import OpenVerse.Core.Scoping
import OpenVerse.Core.Writes

namespace OpenVerse

def Prog.checkEffectSound (P : Prog) : Bool :=
  P.fns.all fun fn => fn.decides || !(fn.body.mayFail P)

theorem Prog.checkEffectSound_ok {P : Prog} (h : P.checkEffectSound = true) : P.EffectSound := by
  intro fn hmem hd
  have := List.all_eq_true.mp h fn hmem
  simp only [hd, Bool.false_or, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this

def Prog.checkWellScoped (P : Prog) : Bool :=
  P.fns.all fun fn => decide (fn.arity ≤ fn.nslots) && fn.body.scoped P fn.nslots

theorem Prog.checkWellScoped_ok {P : Prog} (h : P.checkWellScoped = true) : P.WellScoped := by
  intro fn hmem
  have := List.all_eq_true.mp h fn hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

def Prog.checkWriteSound (P : Prog) : Bool :=
  P.fns.all fun fn => fn.writes || !(fn.body.writesHeap P)

theorem Prog.checkWriteSound_ok {P : Prog} (h : P.checkWriteSound = true) : P.WriteSound := by
  intro fn hmem hw
  have := List.all_eq_true.mp h fn hmem
  simp only [hw, Bool.false_or, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this

/-- `Main` exists and takes no arguments. -/
def Prog.checkMain (P : Prog) : Bool :=
  match P.fns[P.main]? with
  | some fn => fn.arity == 0
  | none => false

/-- Everything the front end guarantees about a program it accepts. -/
def Prog.check (P : Prog) : Bool :=
  P.checkEffectSound && P.checkWellScoped && P.checkMain && P.checkWriteSound

/-- **What a checked program guarantees.** A program that passes `Prog.check`
    never raises a slot or call error, and never fails unless its `Main` is
    `<decides>`. -/
theorem Prog.check_ok {P : Prog} (h : P.check = true) {r out} (hr : Runs P r out) :
    r.scopeErr = false ∧
    (∀ fn, P.fns[P.main]? = some fn → fn.decides = false → r ≠ .fail) := by
  simp only [Prog.check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨he, hs⟩, hm⟩, -⟩ := h
  unfold Prog.checkMain at hm
  split at hm
  · next fn hf =>
    simp only [beq_iff_eq] at hm
    exact ⟨Runs.scoped_ok (checkWellScoped_ok hs) hf hm hr,
      fun fn' hf' hd => Runs.no_fail (checkEffectSound_ok he) hf' hd hr⟩
  · simp at hm

theorem Prog.check_writeSound {P : Prog} (h : P.check = true) : P.WriteSound := by
  simp only [Prog.check, Bool.and_eq_true] at h
  exact Prog.checkWriteSound_ok h.2

end OpenVerse
