/-
  OpenVerse — the reference interpreter with a bound on native recursion (#97).

  `eval` (`Interp.lean`) gives each recursive call one unit less fuel, so fuel
  bounds the *depth* of an evaluation, not its length: both sides of a `seq`
  get the same fuel. The compiled interpreter's native recursion grows with
  that depth, so with `openverse run`'s default fuel a program that recurses
  forever overflows the machine stack long before its fuel runs out.

  `evalB` is `eval` with a second budget, `d`, for the calls that the compiled
  code really nests: those not in tail position (the left of a `seq`, a
  condition, the arguments of an operation or a call, a call's body, the
  pieces of a `for`, the elements of a list). Tail positions (the right of a
  `seq`, the branches of an `if`, the next iteration of a `loop` and of a
  `for`) keep `d`, as they are loops in the compiled code, and in the C
  runtime's `eval_node` (its `continue`s). When `d` runs out, `evalB` stops
  with `deep`, which `openverse run` reports as `limit: recursion depth`
  (exit 3), as `cverse` does.

  `evalB_done`: whenever `evalB` finishes, it returns exactly what `eval`
  returns. So `openverse run` computes the reference interpreter, and through
  `eval_iff` the big-step semantics; the depth bound can only turn an answer
  into a resource limit.
-/
import OpenVerse.Core.Interp

namespace OpenVerse

/-- The outcome of a depth-bounded evaluation: the reference interpreter's
    result (`none` when the fuel runs out), or `deep` when the depth budget
    runs out first. -/
inductive Bounded (α : Type) where
  | done : Option α → Bounded α
  | deep : Bounded α
  deriving Repr, Inhabited

/-- Continue with the result of a bounded evaluation; `deep` stops everything. -/
@[inline] def Bounded.bind {α β : Type} (x : Bounded α) (k : Option α → Bounded β) : Bounded β :=
  match x with
  | .done y => k y
  | .deep => .deep

/-- `bindR` for bounded evaluations. -/
@[inline] def bindRB (x : Bounded (Res × St)) (k : Value → St → Bounded (Res × St)) :
    Bounded (Res × St) :=
  match x with
  | .deep => .deep
  | .done none => .done none
  | .done (some (.ok v, s)) => k v s
  | .done (some (.fail, s)) => .done (some (.fail, s))
  | .done (some (.brk, s)) => .done (some (.brk, s))
  | .done (some (.ret v, s)) => .done (some (.ret v, s))
  | .done (some (.err e, s)) => .done (some (.err e, s))

/-- `bindL` for bounded evaluations. -/
@[inline] def bindLB (x : Bounded (LRes × St)) (k : List Value → St → Bounded (Res × St)) :
    Bounded (Res × St) :=
  match x with
  | .deep => .deep
  | .done none => .done none
  | .done (some (.ok vs, s)) => k vs s
  | .done (some (.stop r, s)) => .done (some (r, s))

mutual
/-- `eval` with fuel `n` and depth budget `d`. -/
def evalB (P : Prog) : Nat → Nat → St → Expr → Bounded (Res × St)
  | 0, _, _, _ => .done none
  | _+1, 0, _, _ => .deep
  | _+1, _+1, s, .lit v => .done (some (.ok v, s))
  | _+1, _+1, s, .local i => .done (some (readSlot s i, s))
  | n+1, d+1, s, .assign i e => bindRB (evalB P n d s e) fun v s₁ =>
      match writeSlot s₁ i v with
      | some s₂ => .done (some (.ok v, s₂))
      | none => .done (some (.err .slot, s₁))
  | n+1, d+1, s, .seq a b => bindRB (evalB P n d s a) fun _ s₁ => evalB P n (d+1) s₁ b
  | n+1, d+1, s, .prim op es => bindLB (evalListB P n d s es) fun vs s₁ => .done (some (op.apply vs, s₁))
  | n+1, d+1, s, .heap op es => bindLB (evalListB P n d s es) fun vs s₁ =>
      .done (some (St.heapStep op vs s₁))
  | n+1, d+1, s, .call f es => bindLB (evalListB P n d s es) fun vs s₁ =>
      match P.callable f vs.length with
      | none => .done (some (.err .call, s₁))
      | some fn => (evalB P n d ⟨frameOf fn vs, s₁.g⟩ fn.body).bind fun
        | none => .done none
        | some (r, s₂) => .done (some (retOf r, ⟨s₁.fr, s₂.g⟩))
  | n+1, d+1, s, .ite c t e => (evalB P n d s c).bind fun
      | none => .done none
      | some (.ok _, s₁) => evalB P n (d+1) s₁ t
      | some (.fail, _) => evalB P n (d+1) s e
      | some (.brk, s₁) => .done (some (.brk, s₁))
      | some (.ret v, s₁) => .done (some (.ret v, s₁))
      | some (.err k, s₁) => .done (some (.err k, s₁))
  | n+1, d+1, s, .forE i it filt body => bindRB (evalB P n d s it) fun v s₁ =>
      match v with
      | .arr vs => evalForB P n d i filt body s₁ vs []
      | .int _ | .logic _ | .char _ | .tup _ | .none | .some _ | .ref _ => .done (some (.err .type, s₁))
  | n+1, d+1, s, .loop b => (evalB P n d s b).bind fun
      | none => .done none
      | some (.ok _, s₁) => evalB P n (d+1) s₁ (.loop b)
      | some (.brk, s₁) => .done (some (.ok .void, s₁))
      | some (.fail, s₁) => .done (some (.fail, s₁))
      | some (.ret v, s₁) => .done (some (.ret v, s₁))
      | some (.err k, s₁) => .done (some (.err k, s₁))
  | _+1, _+1, s, .brk => .done (some (.brk, s))
  | n+1, d+1, s, .ret e => bindRB (evalB P n d s e) fun v s₁ => .done (some (.ret v, s₁))
  | n+1, d+1, s, .print e => bindRB (evalB P n d s e) fun v s₁ =>
      match printBytes v with
      | some bs => .done (some (.ok .void, { s₁ with g := { s₁.g with out := s₁.g.out ++ bs } }))
      | none => .done (some (.err .type, s₁))

/-- `evalList` with fuel `n` and depth budget `d`. -/
def evalListB (P : Prog) : Nat → Nat → St → List Expr → Bounded (LRes × St)
  | 0, _, _, _ => .done none
  | _+1, 0, _, _ => .deep
  | _+1, _+1, s, [] => .done (some (.ok [], s))
  | n+1, d+1, s, e :: es => (evalB P n d s e).bind fun
    | none => .done none
    | some (.ok v, s₁) => (evalListB P n d s₁ es).bind fun
      | none => .done none
      | some (.ok vs, s₂) => .done (some (.ok (v :: vs), s₂))
      | some (.stop r, s₂) => .done (some (.stop r, s₂))
    | some (.fail, s₁) => .done (some (.stop .fail, s₁))
    | some (.brk, s₁) => .done (some (.stop .brk, s₁))
    | some (.ret v, s₁) => .done (some (.stop (.ret v), s₁))
    | some (.err k, s₁) => .done (some (.stop (.err k), s₁))

/-- `evalFor` with fuel `n` and depth budget `d`. -/
def evalForB (P : Prog) : Nat → Nat → Nat → Expr → Expr → St → List Value → List Value →
    Bounded (Res × St)
  | 0, _, _, _, _, _, _, _ => .done none
  | _+1, 0, _, _, _, _, _, _ => .deep
  | _+1, _+1, _, _, _, s, [], acc => .done (some (.ok (.arr acc.reverse), s))
  | n+1, d+1, i, filt, body, s, v :: vs, acc => match writeSlot s i v with
    | none => .done (some (.err .slot, s))
    | some s₀ => (evalB P n d s₀ filt).bind fun
      | none => .done none
      | some (.fail, _) => evalForB P n (d+1) i filt body s₀ vs acc
      | some (.ok _, s₁) => (evalB P n d s₁ body).bind fun
        | none => .done none
        | some (.ok w, s₂) => evalForB P n (d+1) i filt body s₂ vs (w :: acc)
        | some (.fail, s₂) => .done (some (.fail, s₂))
        | some (.brk, s₂) => .done (some (.brk, s₂))
        | some (.ret v, s₂) => .done (some (.ret v, s₂))
        | some (.err k, s₂) => .done (some (.err k, s₂))
      | some (.brk, s₁) => .done (some (.brk, s₁))
      | some (.ret v, s₁) => .done (some (.ret v, s₁))
      | some (.err k, s₁) => .done (some (.err k, s₁))
end

/-- Run `Main()` with fuel `n` and depth budget `d`. -/
def Prog.runB (P : Prog) (n d : Nat) : Bounded (Res × List Nat) :=
  (evalB P n d Prog.initSt (.call P.main [])).bind fun x => .done (x.map fun (r, s) => (r, s.g.out))

/-! ### `evalB` computes `eval` whenever it finishes -/

/-- A bounded result agrees with an interpreter result: `deep` with any, `done x` with `x`. -/
def Bounded.agrees {α : Type} : Bounded α → Option α → Prop
  | .done x, y => x = y
  | .deep, _ => True

theorem bindRB_agrees {x : Bounded (Res × St)} {y : Option (Res × St)}
    {k : Value → St → Bounded (Res × St)} {k' : Value → St → Option (Res × St)}
    (hx : x.agrees y) (hk : ∀ v s, (k v s).agrees (k' v s)) : (bindRB x k).agrees (bindR y k') := by
  cases x with
  | deep => trivial
  | done z =>
    simp only [Bounded.agrees] at hx; subst hx
    rcases z with _ | ⟨r, s⟩
    · rfl
    · cases r <;> first | exact hk _ _ | rfl

theorem bindLB_agrees {x : Bounded (LRes × St)} {y : Option (LRes × St)}
    {k : List Value → St → Bounded (Res × St)} {k' : List Value → St → Option (Res × St)}
    (hx : x.agrees y) (hk : ∀ vs s, (k vs s).agrees (k' vs s)) : (bindLB x k).agrees (bindL y k') := by
  cases x with
  | deep => trivial
  | done z =>
    simp only [Bounded.agrees] at hx; subst hx
    rcases z with _ | ⟨r, s⟩
    · rfl
    · cases r <;> first | exact hk _ _ | rfl

/-- Agreement through a `bind`: from agreement of the first evaluation and of
    every continuation. -/
theorem Bounded.bind_agrees {α β : Type} {x : Bounded α} {y : Option α}
    (k : Option α → Bounded β) (k' : Option α → Option β)
    (hx : x.agrees y) (hk : ∀ z, (k z).agrees (k' z)) : (x.bind k).agrees (k' y) := by
  cases x with
  | deep => trivial
  | done z => simp only [Bounded.agrees] at hx; subst hx; exact hk z

/-- Close a goal `(.done x).agrees x`, or `.deep.agrees y`. -/
macro "agree_leaf" : tactic =>
  `(tactic| first | exact rfl | trivial | (simp_all [Bounded.agrees]; done))

theorem evalB_agrees (P : Prog) : ∀ n,
    (∀ d s e, (evalB P n d s e).agrees (eval P n s e)) ∧
    (∀ d s es, (evalListB P n d s es).agrees (evalList P n s es)) ∧
    (∀ d i filt body s vs acc,
      (evalForB P n d i filt body s vs acc).agrees (evalFor P n i filt body s vs acc))
  | 0 => ⟨fun _ _ _ => by simp only [evalB, eval]; agree_leaf,
      fun _ _ _ => by simp only [evalListB, evalList]; agree_leaf,
      fun _ _ _ _ _ _ _ => by simp only [evalForB, evalFor]; agree_leaf⟩
  | n+1 => by
    obtain ⟨ihE, ihL, ihF⟩ := evalB_agrees P n
    refine ⟨fun d s e => ?_, fun d s es => ?_, fun d i filt body s vs acc => ?_⟩
    · cases d with
      | zero => simp only [evalB]; agree_leaf
      | succ d =>
        cases e with
        | lit v => simp only [evalB, eval]; agree_leaf
        | «local» i => simp only [evalB, eval]; agree_leaf
        | assign i e =>
          simp only [evalB, eval]
          exact bindRB_agrees (ihE d s e) fun v s₁ => by split <;> agree_leaf
        | seq a b =>
          simp only [evalB, eval]
          exact bindRB_agrees (ihE d s a) fun _ s₁ => ihE (d+1) s₁ b
        | prim op es =>
          simp only [evalB, eval]
          exact bindLB_agrees (ihL d s es) fun _ _ => by agree_leaf
        | heap op es =>
          simp only [evalB, eval]
          exact bindLB_agrees (ihL d s es) fun _ _ => by agree_leaf
        | call f es =>
          simp only [evalB, eval]
          refine bindLB_agrees (ihL d s es) fun vs s₁ => ?_
          split
          · next hfn => simp only [hfn]; agree_leaf
          · next fn hfn =>
            simp only [hfn]
            refine Bounded.bind_agrees (β := Res × St) _ (fun (z : Option (Res × St)) => match z with
              | none => none
              | some (r, s₂) => some (retOf r, ⟨s₁.fr, s₂.g⟩)) (ihE d _ _) fun z => ?_
            rcases z with _ | ⟨r, s₂⟩ <;> agree_leaf
        | ite c t e =>
          simp only [evalB, eval]
          refine Bounded.bind_agrees (β := Res × St) _ (fun (z : Option (Res × St)) => match z with
            | none => none
            | some (.ok _, s₁) => eval P n s₁ t
            | some (.fail, _) => eval P n s e
            | some (.brk, s₁) => some (.brk, s₁)
            | some (.ret v, s₁) => some (.ret v, s₁)
            | some (.err k, s₁) => some (.err k, s₁)) (ihE d s c) fun z => ?_
          rcases z with _ | ⟨r, s₁⟩
          · agree_leaf
          · cases r with
            | ok v => exact ihE (d+1) s₁ t
            | fail => exact ihE (d+1) s e
            | _ => agree_leaf
        | forE i it filt body =>
          simp only [evalB, eval]
          refine bindRB_agrees (ihE d s it) fun v s₁ => ?_
          cases v <;> first | agree_leaf | exact ihF d i filt body s₁ _ []
        | loop b =>
          simp only [evalB, eval]
          refine Bounded.bind_agrees (β := Res × St) _ (fun (z : Option (Res × St)) => match z with
            | none => none
            | some (.ok _, s₁) => eval P n s₁ (.loop b)
            | some (.brk, s₁) => some (.ok .void, s₁)
            | some (.fail, s₁) => some (.fail, s₁)
            | some (.ret v, s₁) => some (.ret v, s₁)
            | some (.err k, s₁) => some (.err k, s₁)) (ihE d s b) fun z => ?_
          rcases z with _ | ⟨r, s₁⟩
          · agree_leaf
          · cases r with
            | ok v => exact ihE (d+1) s₁ (.loop b)
            | _ => agree_leaf
        | brk => simp only [evalB, eval]; agree_leaf
        | ret e =>
          simp only [evalB, eval]
          exact bindRB_agrees (ihE d s e) fun _ _ => by agree_leaf
        | print e =>
          simp only [evalB, eval]
          exact bindRB_agrees (ihE d s e) fun v s₁ => by split <;> agree_leaf
    · cases d with
      | zero => simp only [evalListB]; agree_leaf
      | succ d =>
        cases es with
        | nil => simp only [evalListB, evalList]; agree_leaf
        | cons e es =>
          simp only [evalListB, evalList]
          refine Bounded.bind_agrees (β := LRes × St) _ (fun (z : Option (Res × St)) => match z with
            | none => none
            | some (.ok v, s₁) => match evalList P n s₁ es with
              | none => none
              | some (.ok vs, s₂) => some (.ok (v :: vs), s₂)
              | some (.stop r, s₂) => some (.stop r, s₂)
            | some (.fail, s₁) => some (.stop .fail, s₁)
            | some (.brk, s₁) => some (.stop .brk, s₁)
            | some (.ret v, s₁) => some (.stop (.ret v), s₁)
            | some (.err k, s₁) => some (.stop (.err k), s₁)) (ihE d s e) fun z => ?_
          rcases z with _ | ⟨r, s₁⟩
          · agree_leaf
          · cases r with
            | ok v =>
              refine Bounded.bind_agrees (β := LRes × St) _ (fun (z : Option (LRes × St)) => match z with
                | none => none
                | some (.ok vs, s₂) => some (.ok (v :: vs), s₂)
                | some (.stop r, s₂) => some (.stop r, s₂)) (ihL d s₁ es) fun z => ?_
              rcases z with _ | ⟨r, s₂⟩
              · agree_leaf
              · cases r <;> agree_leaf
            | _ => agree_leaf
    · cases d with
      | zero => simp only [evalForB]; agree_leaf
      | succ d =>
        cases vs with
        | nil => simp only [evalForB, evalFor]; agree_leaf
        | cons v vs =>
          simp only [evalForB, evalFor]
          split
          · next hs => simp only [hs]; agree_leaf
          · next s₀ hs₀ =>
            simp only [hs₀]
            refine Bounded.bind_agrees (β := Res × St) _ (fun (z : Option (Res × St)) => match z with
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
              | some (.err k, s₁) => some (.err k, s₁)) (ihE d s₀ filt) fun z => ?_
            rcases z with _ | ⟨r, s₁⟩
            · agree_leaf
            · cases r with
              | fail => exact ihF (d+1) i filt body s₀ vs acc
              | ok u =>
                refine Bounded.bind_agrees (β := Res × St) _ (fun (z : Option (Res × St)) => match z with
                  | none => none
                  | some (.ok w, s₂) => evalFor P n i filt body s₂ vs (w :: acc)
                  | some (.fail, s₂) => some (.fail, s₂)
                  | some (.brk, s₂) => some (.brk, s₂)
                  | some (.ret v, s₂) => some (.ret v, s₂)
                  | some (.err k, s₂) => some (.err k, s₂)) (ihE d s₁ body) fun z => ?_
                rcases z with _ | ⟨r, s₂⟩
                · agree_leaf
                · cases r with
                  | ok w => exact ihF (d+1) i filt body s₂ vs (w :: acc)
                  | _ => agree_leaf
              | _ => agree_leaf

/-- **The bounded interpreter is the reference interpreter.** Whenever
    `evalB` finishes (it does not run out of depth), its result is `eval`'s. -/
theorem evalB_done {P : Prog} {n d : Nat} {s : St} {e : Expr} {x : Option (Res × St)}
    (h : evalB P n d s e = .done x) : eval P n s e = x := by
  have := (evalB_agrees P n).1 d s e
  rw [h] at this
  exact this.symm

/-- `openverse run` computes `Prog.run`: whenever `Prog.runB` finishes, its
    outcome and output are `Prog.run`'s. -/
theorem Prog.runB_done {P : Prog} {n d : Nat} {x : Option (Res × List Nat)}
    (h : P.runB n d = .done x) : P.run n = x := by
  unfold Prog.runB at h
  unfold Prog.run
  have := (evalB_agrees P n).1 d Prog.initSt (.call P.main [])
  revert h this
  cases evalB P n d Prog.initSt (.call P.main []) with
  | deep => intro h; simp [Bounded.bind] at h
  | done y =>
    intro h hy
    simp only [Bounded.bind, Bounded.done.injEq] at h
    simp only [Bounded.agrees] at hy
    rw [← hy, h]

end OpenVerse
