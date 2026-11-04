/-
  OpenVerse — the reference interpreter of Verse Core.

  `eval P n s e` evaluates `e` with fuel `n`. It returns `none` when the fuel
  runs out and otherwise the outcome and final state. Every recursive call
  spends one unit of fuel, so the definition is structural on `n` and Lean
  checks that it terminates.

  `OpenVerse.Core.Adequacy` proves that it computes exactly the big-step
  relation `Eval`: sound for every fuel, and complete for all large enough
  fuels. The C runtime (`runtime/src/interp.c`) is a transcription of this
  file over the node table of a loaded program.
-/
import OpenVerse.Core.Semantics

namespace OpenVerse

/-- Continue with the value of a successful evaluation; pass anything else on. -/
@[inline] def bindR (x : Option (Res × St)) (k : Value → St → Option (Res × St)) :
    Option (Res × St) :=
  match x with
  | none => none
  | some (.ok v, s) => k v s
  | some (.fail, s) => some (.fail, s)
  | some (.brk, s) => some (.brk, s)
  | some (.ret v, s) => some (.ret v, s)
  | some (.err e, s) => some (.err e, s)

/-- Continue with the values of a successful list evaluation; pass a stop on. -/
@[inline] def bindL (x : Option (LRes × St)) (k : List Value → St → Option (Res × St)) :
    Option (Res × St) :=
  match x with
  | none => none
  | some (.ok vs, s) => k vs s
  | some (.stop r, s) => some (r, s)

mutual
/-- Evaluate one expression with fuel `n`. -/
def eval (P : Prog) : Nat → St → Expr → Option (Res × St)
  | 0, _, _ => none
  | _+1, s, .lit v => some (.ok v, s)
  | _+1, s, .local i => some (readSlot s i, s)
  | n+1, s, .assign i e => bindR (eval P n s e) fun v s₁ =>
      match writeSlot s₁ i v with
      | some s₂ => some (.ok v, s₂)
      | none => some (.err .slot, s₁)
  | n+1, s, .seq a b => bindR (eval P n s a) fun _ s₁ => eval P n s₁ b
  | n+1, s, .prim op es => bindL (evalList P n s es) fun vs s₁ => some (op.apply vs, s₁)
  | n+1, s, .call f es => bindL (evalList P n s es) fun vs s₁ =>
      match P.callable f vs.length with
      | none => some (.err .call, s₁)
      | some fn => match eval P n ⟨frameOf fn vs, s₁.out⟩ fn.body with
        | none => none
        | some (r, s₂) => some (retOf r, ⟨s₁.fr, s₂.out⟩)
  | n+1, s, .ite c t e => match eval P n s c with
      | none => none
      | some (.ok _, s₁) => eval P n s₁ t
      | some (.fail, _) => eval P n s e
      | some (.brk, s₁) => some (.brk, s₁)
      | some (.ret v, s₁) => some (.ret v, s₁)
      | some (.err k, s₁) => some (.err k, s₁)
  | n+1, s, .forE i it filt body => bindR (eval P n s it) fun v s₁ =>
      match v with
      | .arr vs => evalFor P n i filt body s₁ vs []
      | .int _ | .logic _ | .char _ | .tup _ | .none | .some _ => some (.err .type, s₁)
  | n+1, s, .loop b => match eval P n s b with
      | none => none
      | some (.ok _, s₁) => eval P n s₁ (.loop b)
      | some (.brk, s₁) => some (.ok .void, s₁)
      | some (.fail, s₁) => some (.fail, s₁)
      | some (.ret v, s₁) => some (.ret v, s₁)
      | some (.err k, s₁) => some (.err k, s₁)
  | _+1, s, .brk => some (.brk, s)
  | n+1, s, .ret e => bindR (eval P n s e) fun v s₁ => some (.ret v, s₁)
  | n+1, s, .print e => bindR (eval P n s e) fun v s₁ =>
      match printBytes v with
      | some bs => some (.ok .void, { s₁ with out := s₁.out ++ bs })
      | none => some (.err .type, s₁)

/-- Evaluate an argument list, left to right, with fuel `n`. -/
def evalList (P : Prog) : Nat → St → List Expr → Option (LRes × St)
  | 0, _, _ => none
  | _+1, s, [] => some (.ok [], s)
  | n+1, s, e :: es => match eval P n s e with
    | none => none
    | some (.ok v, s₁) => match evalList P n s₁ es with
      | none => none
      | some (.ok vs, s₂) => some (.ok (v :: vs), s₂)
      | some (.stop r, s₂) => some (.stop r, s₂)
    | some (.fail, s₁) => some (.stop .fail, s₁)
    | some (.brk, s₁) => some (.stop .brk, s₁)
    | some (.ret v, s₁) => some (.stop (.ret v), s₁)
    | some (.err k, s₁) => some (.stop (.err k), s₁)

/-- Run the remaining iterations of a one-generator `for`, with fuel `n`. -/
def evalFor (P : Prog) : Nat → Nat → Expr → Expr → St → List Value → List Value →
    Option (Res × St)
  | 0, _, _, _, _, _, _ => none
  | _+1, _, _, _, s, [], acc => some (.ok (.arr acc.reverse), s)
  | n+1, i, filt, body, s, v :: vs, acc => match writeSlot s i v with
    | none => some (.err .slot, s)
    | some s₀ => match eval P n s₀ filt with
      | none => none
      | some (.fail, _) => evalFor P n i filt body s₀ vs acc
      | some (.ok _, s₁) => match eval P n s₁ body with
        | none => none
        | some (.ok w, s₂) => evalFor P n i filt body s₂ vs (w :: acc)
        | some (.fail, s₂) => some (.fail, s₂)
        | some (.brk, s₂) => some (.brk, s₂)
        | some (.ret v, s₂) => some (.ret v, s₂)
        | some (.err k, s₂) => some (.err k, s₂)
      | some (.brk, s₁) => some (.brk, s₁)
      | some (.ret v, s₁) => some (.ret v, s₁)
      | some (.err k, s₁) => some (.err k, s₁)
end

/-- Run `Main()` with fuel `n`: the outcome and the output, or `none` when the
    fuel runs out (both implementations report this as `limit: fuel exhausted`). -/
def Prog.run (P : Prog) (n : Nat) : Option (Res × List Nat) :=
  (eval P n Prog.initSt (.call P.main [])).map fun (r, s) => (r, s.out)

end OpenVerse
