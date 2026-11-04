/-
  OpenVerse — the big-step semantics of Verse Core.

  `Eval P s e r s'` : in program `P`, from state `s`, expression `e`
  evaluates to outcome `r` and leaves state `s'`.

  The state is the frame of the current call (its slots) and the output
  written so far. Both are transactional: a failure context (`if`
  condition, `for` filter) that fails restores the state it started from.
  This is Verse's rollback of speculative execution: a failed condition
  leaves no trace, not even in the output.

  Every rule is deterministic in the sense of `OpenVerse.Core.Adequacy`
  (`Eval.det`): the relation is the graph of a partial function, which the
  interpreter `OpenVerse.Core.Interp.eval` computes.
-/
import OpenVerse.Core.Prims

namespace OpenVerse

/-- Machine state: the current frame and the output (bytes). -/
structure St where
  fr  : List Value
  out : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- Read slot `i`: its value, or a slot error outside the frame. -/
def readSlot (s : St) (i : Nat) : Res :=
  match s.fr[i]? with
  | some v => .ok v
  | none => .err .slot

/-- Write slot `i`, or `none` outside the frame. -/
def writeSlot (s : St) (i : Nat) (v : Value) : Option St :=
  if i < s.fr.length then some { s with fr := s.fr.set i v } else none

/-- The function `f`, if it exists and takes `n` arguments. -/
def Prog.callable (P : Prog) (f n : Nat) : Option Fn :=
  match P.fns[f]? with
  | some fn => if fn.arity = n then some fn else none
  | none => none

/-- The initial frame of a call: the arguments, then `void` in the other slots. -/
def frameOf (fn : Fn) (vs : List Value) : List Value :=
  vs ++ List.replicate (fn.nslots - fn.arity) Value.void

/-- The outcome of a call seen by the caller: `return v` becomes `ok v`;
    a `break` that escaped its function is a control error. -/
def retOf : Res → Res
  | .ok v => .ok v
  | .ret v => .ok v
  | .fail => .fail
  | .brk => .err .control
  | .err e => .err e

/-- The bytes printed by `Print(v)`: the string, then a newline. -/
def printBytes : Value → Option (List Nat)
  | .arr vs => (asBytes vs).map (· ++ [10])
  | _ => none

mutual
/-- Big-step evaluation of one expression. -/
inductive Eval (P : Prog) : St → Expr → Res → St → Prop
  | lit {s v} : Eval P s (.lit v) (.ok v) s
  | local {s i} : Eval P s (.local i) (readSlot s i) s
  | assign_ok {s s₁ s₂ i e v} :
      Eval P s e (.ok v) s₁ → writeSlot s₁ i v = some s₂ →
      Eval P s (.assign i e) (.ok v) s₂
  | assign_bad {s s₁ i e v} :
      Eval P s e (.ok v) s₁ → writeSlot s₁ i v = none →
      Eval P s (.assign i e) (.err .slot) s₁
  | assign_stop {s s₁ i e r} :
      Eval P s e r s₁ → r.isOk = false →
      Eval P s (.assign i e) r s₁
  | seq_ok {s s₁ s₂ a b v r} :
      Eval P s a (.ok v) s₁ → Eval P s₁ b r s₂ →
      Eval P s (.seq a b) r s₂
  | seq_stop {s s₁ a b r} :
      Eval P s a r s₁ → r.isOk = false →
      Eval P s (.seq a b) r s₁
  | prim_ok {s s₁ op es vs} :
      EvalList P s es (.ok vs) s₁ →
      Eval P s (.prim op es) (op.apply vs) s₁
  | prim_stop {s s₁ op es r} :
      EvalList P s es (.stop r) s₁ →
      Eval P s (.prim op es) r s₁
  | call_ok {s s₁ s₂ f es vs fn r} :
      EvalList P s es (.ok vs) s₁ → P.callable f vs.length = some fn →
      Eval P ⟨frameOf fn vs, s₁.out⟩ fn.body r s₂ →
      Eval P s (.call f es) (retOf r) ⟨s₁.fr, s₂.out⟩
  | call_bad {s s₁ f es vs} :
      EvalList P s es (.ok vs) s₁ → P.callable f vs.length = none →
      Eval P s (.call f es) (.err .call) s₁
  | call_stop {s s₁ f es r} :
      EvalList P s es (.stop r) s₁ →
      Eval P s (.call f es) r s₁
  | ite_ok {s s₁ s₂ c t e v r} :
      Eval P s c (.ok v) s₁ → Eval P s₁ t r s₂ →
      Eval P s (.ite c t e) r s₂
  /-- Rollback: the `else` branch starts from `s`, not from where `c` failed. -/
  | ite_fail {s s₁ s₂ c t e r} :
      Eval P s c .fail s₁ → Eval P s e r s₂ →
      Eval P s (.ite c t e) r s₂
  | ite_stop {s s₁ c t e r} :
      Eval P s c r s₁ → r.isOk = false → r ≠ .fail →
      Eval P s (.ite c t e) r s₁
  | for_ok {s s₁ s₂ i it filt body vs r} :
      Eval P s it (.ok (.arr vs)) s₁ → EvalFor P i filt body s₁ vs [] r s₂ →
      Eval P s (.forE i it filt body) r s₂
  | for_type {s s₁ i it filt body v} :
      Eval P s it (.ok v) s₁ → (∀ vs, v ≠ .arr vs) →
      Eval P s (.forE i it filt body) (.err .type) s₁
  | for_stop {s s₁ i it filt body r} :
      Eval P s it r s₁ → r.isOk = false →
      Eval P s (.forE i it filt body) r s₁
  | loop_ok {s s₁ s₂ b v r} :
      Eval P s b (.ok v) s₁ → Eval P s₁ (.loop b) r s₂ →
      Eval P s (.loop b) r s₂
  | loop_brk {s s₁ b} :
      Eval P s b .brk s₁ →
      Eval P s (.loop b) (.ok .void) s₁
  | loop_stop {s s₁ b r} :
      Eval P s b r s₁ → r.isOk = false → r ≠ .brk →
      Eval P s (.loop b) r s₁
  | brk {s} : Eval P s .brk .brk s
  | ret_ok {s s₁ e v} :
      Eval P s e (.ok v) s₁ →
      Eval P s (.ret e) (.ret v) s₁
  | ret_stop {s s₁ e r} :
      Eval P s e r s₁ → r.isOk = false →
      Eval P s (.ret e) r s₁
  | print_ok {s s₁ e v bs} :
      Eval P s e (.ok v) s₁ → printBytes v = some bs →
      Eval P s (.print e) (.ok .void) { s₁ with out := s₁.out ++ bs }
  | print_bad {s s₁ e v} :
      Eval P s e (.ok v) s₁ → printBytes v = none →
      Eval P s (.print e) (.err .type) s₁
  | print_stop {s s₁ e r} :
      Eval P s e r s₁ → r.isOk = false →
      Eval P s (.print e) r s₁

/-- Big-step evaluation of an argument list, left to right. -/
inductive EvalList (P : Prog) : St → List Expr → LRes → St → Prop
  | nil {s} : EvalList P s [] (.ok []) s
  | cons_ok {s s₁ s₂ e es v vs} :
      Eval P s e (.ok v) s₁ → EvalList P s₁ es (.ok vs) s₂ →
      EvalList P s (e :: es) (.ok (v :: vs)) s₂
  | cons_stop {s s₁ e es r} :
      Eval P s e r s₁ → r.isOk = false →
      EvalList P s (e :: es) (.stop r) s₁
  | cons_stop_tail {s s₁ s₂ e es v r} :
      Eval P s e (.ok v) s₁ → EvalList P s₁ es (.stop r) s₂ →
      EvalList P s (e :: es) (.stop r) s₂

/-- The iterations of a one-generator `for`: slot `i`, filter, body, the
    elements still to visit and the results so far (in reverse). -/
inductive EvalFor (P : Prog) : Nat → Expr → Expr → St → List Value → List Value → Res → St → Prop
  | done {i filt body s acc} :
      EvalFor P i filt body s [] acc (.ok (.arr acc.reverse)) s
  | bad_slot {i filt body s v vs acc} :
      writeSlot s i v = none →
      EvalFor P i filt body s (v :: vs) acc (.err .slot) s
  /-- Rollback: a failed filter restores `s₀`, the state after binding the element. -/
  | skip {i filt body s s₀ s₁ s₂ v vs acc r} :
      writeSlot s i v = some s₀ → Eval P s₀ filt .fail s₁ →
      EvalFor P i filt body s₀ vs acc r s₂ →
      EvalFor P i filt body s (v :: vs) acc r s₂
  | filt_stop {i filt body s s₀ s₁ v vs acc r} :
      writeSlot s i v = some s₀ → Eval P s₀ filt r s₁ → r.isOk = false → r ≠ .fail →
      EvalFor P i filt body s (v :: vs) acc r s₁
  | step {i filt body s s₀ s₁ s₂ s₃ v vs acc u w r} :
      writeSlot s i v = some s₀ → Eval P s₀ filt (.ok u) s₁ →
      Eval P s₁ body (.ok w) s₂ → EvalFor P i filt body s₂ vs (w :: acc) r s₃ →
      EvalFor P i filt body s (v :: vs) acc r s₃
  | body_stop {i filt body s s₀ s₁ s₂ v vs acc u r} :
      writeSlot s i v = some s₀ → Eval P s₀ filt (.ok u) s₁ →
      Eval P s₁ body r s₂ → r.isOk = false →
      EvalFor P i filt body s (v :: vs) acc r s₂
end

/-- Running a program: call `Main()` with an empty output. The result is the
    outcome of `Main` and the bytes it printed. -/
def Prog.initSt : St := ⟨[], []⟩

/-- `P` run to completion gives outcome `r` and output `out`. -/
def Runs (P : Prog) (r : Res) (out : List Nat) : Prop :=
  ∃ fr, Eval P Prog.initSt (.call P.main []) r ⟨fr, out⟩

end OpenVerse
