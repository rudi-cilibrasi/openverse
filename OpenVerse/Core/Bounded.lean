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

  `evalB_sound`: whenever `evalB` finishes, it returns exactly what `eval`
  returns. So `openverse run` computes the reference interpreter, and through
  `eval_iff` the big-step semantics; the depth bound can only turn an answer
  into a resource limit. `evalB_complete`: with a depth budget at least the
  fuel, `evalB` never stops early, so it *is* `eval` (the bound is not
  vacuous: `deep` is returned only when nesting really exceeds it).
-/
import OpenVerse.Core.Interp

namespace OpenVerse

/-- The outcome of a depth-bounded evaluation: `fuel` and `res a` are the
    reference interpreter's `none` and `some a`; `deep` means the depth budget
    ran out first. (One flat type, so that a result costs no extra allocation.) -/
inductive Bounded (α : Type) where
  | fuel : Bounded α
  | res : α → Bounded α
  | deep : Bounded α
  deriving Repr, Inhabited

/-- The bounded result that is the interpreter's result. -/
def Bounded.ofOption {α : Type} : Option α → Bounded α
  | none => .fuel
  | some a => .res a

/-- Continue with the result of a bounded evaluation; `deep` stops everything. -/
@[inline] def Bounded.bind {α β : Type} (x : Bounded α) (k : Option α → Bounded β) : Bounded β :=
  match x with
  | .fuel => k none
  | .res a => k (some a)
  | .deep => .deep

/-- `bindR` for bounded evaluations. -/
@[inline] def bindRB (x : Bounded (Res × St)) (k : Value → St → Bounded (Res × St)) :
    Bounded (Res × St) :=
  match x with
  | .deep => .deep
  | .fuel => .fuel
  | .res (.ok v, s) => k v s
  | .res (.fail, s) => .res (.fail, s)
  | .res (.brk, s) => .res (.brk, s)
  | .res (.ret v, s) => .res (.ret v, s)
  | .res (.err e, s) => .res (.err e, s)

/-- `bindL` for bounded evaluations. -/
@[inline] def bindLB (x : Bounded (LRes × St)) (k : List Value → St → Bounded (Res × St)) :
    Bounded (Res × St) :=
  match x with
  | .deep => .deep
  | .fuel => .fuel
  | .res (.ok vs, s) => k vs s
  | .res (.stop r, s) => .res (r, s)

mutual
/-- `eval` with fuel `n` and depth budget `d`. -/
def evalB (P : Prog) : Nat → Nat → St → Expr → Bounded (Res × St)
  | 0, _, _, _ => .fuel
  | _+1, 0, _, _ => .deep
  | _+1, _+1, s, .lit v => .res (.ok v, s)
  | _+1, _+1, s, .local i => .res (readSlot s i, s)
  | n+1, d+1, s, .assign i e => bindRB (evalB P n d s e) fun v s₁ =>
      match writeSlot s₁ i v with
      | some s₂ => .res (.ok v, s₂)
      | none => .res (.err .slot, s₁)
  | n+1, d+1, s, .seq a b => bindRB (evalB P n d s a) fun _ s₁ => evalB P n (d+1) s₁ b
  | n+1, d+1, s, .prim op es => bindLB (evalListB P n d s es) fun vs s₁ =>
      if n < op.cost vs then .fuel else .res (op.apply vs, s₁)
  | n+1, d+1, s, .heap op es => bindLB (evalListB P n d s es) fun vs s₁ =>
      .res (St.heapStep op vs s₁)
  | n+1, d+1, s, .call f es => bindLB (evalListB P n d s es) fun vs s₁ =>
      match P.callable f vs.length with
      | none => .res (.err .call, s₁)
      | some fn => (evalB P n d ⟨frameOf fn vs, s₁.g⟩ fn.body).bind fun
        | none => .fuel
        | some (r, s₂) => .res (retOf r, ⟨s₁.fr, s₂.g⟩)
  | n+1, d+1, s, .ite c t e => (evalB P n d s c).bind fun
      | none => .fuel
      | some (.ok _, s₁) => evalB P n (d+1) s₁ t
      | some (.fail, _) => evalB P n (d+1) s e
      | some (.brk, s₁) => .res (.brk, s₁)
      | some (.ret v, s₁) => .res (.ret v, s₁)
      | some (.err k, s₁) => .res (.err k, s₁)
  | n+1, d+1, s, .forE i it filt body => bindRB (evalB P n d s it) fun v s₁ =>
      match v with
      | .arr vs => evalForB P n d i filt body s₁ vs.toList []
      | .int _ | .logic _ | .char _ | .float _ | .tup _ | .none | .some _ | .ref _ => .res (.err .type, s₁)
  | n+1, d+1, s, .loop b => (evalB P n d s b).bind fun
      | none => .fuel
      | some (.ok _, s₁) => evalB P n (d+1) s₁ (.loop b)
      | some (.brk, s₁) => .res (.ok .void, s₁)
      | some (.fail, s₁) => .res (.fail, s₁)
      | some (.ret v, s₁) => .res (.ret v, s₁)
      | some (.err k, s₁) => .res (.err k, s₁)
  | _+1, _+1, s, .brk => .res (.brk, s)
  | n+1, d+1, s, .ret e => bindRB (evalB P n d s e) fun v s₁ => .res (.ret v, s₁)
  | n+1, d+1, s, .print e => bindRB (evalB P n d s e) fun v s₁ =>
      match printBytes v with
      | some bs => .res (.ok .void, { s₁ with g := { s₁.g with out := s₁.g.out ++ bs } })
      | none => .res (.err .type, s₁)

/-- `evalList` with fuel `n` and depth budget `d`. -/
def evalListB (P : Prog) : Nat → Nat → St → List Expr → Bounded (LRes × St)
  | 0, _, _, _ => .fuel
  | _+1, 0, _, _ => .deep
  | _+1, _+1, s, [] => .res (.ok [], s)
  | n+1, d+1, s, e :: es => (evalB P n d s e).bind fun
    | none => .fuel
    | some (.ok v, s₁) => (evalListB P n d s₁ es).bind fun
      | none => .fuel
      | some (.ok vs, s₂) => .res (.ok (v :: vs), s₂)
      | some (.stop r, s₂) => .res (.stop r, s₂)
    | some (.fail, s₁) => .res (.stop .fail, s₁)
    | some (.brk, s₁) => .res (.stop .brk, s₁)
    | some (.ret v, s₁) => .res (.stop (.ret v), s₁)
    | some (.err k, s₁) => .res (.stop (.err k), s₁)

/-- `evalFor` with fuel `n` and depth budget `d`. -/
def evalForB (P : Prog) : Nat → Nat → Nat → Expr → Expr → St → List Value → List Value →
    Bounded (Res × St)
  | 0, _, _, _, _, _, _, _ => .fuel
  | _+1, 0, _, _, _, _, _, _ => .deep
  | _+1, _+1, _, _, _, s, [], acc => .res (.ok (Value.ofArray acc.reverse.toArray), s)
  | n+1, d+1, i, filt, body, s, v :: vs, acc => match writeSlot s i v with
    | none => .res (.err .slot, s)
    | some s₀ => (evalB P n d s₀ filt).bind fun
      | none => .fuel
      | some (.fail, _) => evalForB P n (d+1) i filt body s₀ vs acc
      | some (.ok _, s₁) => (evalB P n d s₁ body).bind fun
        | none => .fuel
        | some (.ok w, s₂) => evalForB P n (d+1) i filt body s₂ vs (w :: acc)
        | some (.fail, s₂) => .res (.fail, s₂)
        | some (.brk, s₂) => .res (.brk, s₂)
        | some (.ret v, s₂) => .res (.ret v, s₂)
        | some (.err k, s₂) => .res (.err k, s₂)
      | some (.brk, s₁) => .res (.brk, s₁)
      | some (.ret v, s₁) => .res (.ret v, s₁)
      | some (.err k, s₁) => .res (.err k, s₁)
end

/-- Run `Main()` with fuel `n` and depth budget `d`. -/
def Prog.runB (P : Prog) (n d : Nat) : Bounded (Res × List Nat) :=
  match evalB P n d Prog.initSt (.call P.main []) with
  | .fuel => .fuel
  | .res (r, s) => .res (r, s.g.out)
  | .deep => .deep

/-! ### `evalB` is `eval`, up to stopping early -/

/-- `x.rel strict y`: the bounded result `x` is the interpreter's result `y`;
    `deep` relates to every `y` unless `strict`. -/
def Bounded.rel {α : Type} (strict : Bool) : Bounded α → Option α → Prop
  | .fuel, y => y = none
  | .res a, y => y = some a
  | .deep, _ => strict = false

theorem bindRB_rel {b : Bool} {x : Bounded (Res × St)} {y : Option (Res × St)}
    {k : Value → St → Bounded (Res × St)} {k' : Value → St → Option (Res × St)}
    (hx : x.rel b y) (hk : ∀ v s, (k v s).rel b (k' v s)) : (bindRB x k).rel b (bindR y k') := by
  cases x with
  | deep => exact hx
  | fuel => simp only [Bounded.rel] at hx; subst hx; rfl
  | res z =>
    simp only [Bounded.rel] at hx; subst hx
    rcases z with ⟨r, s⟩
    cases r <;> first | exact hk _ _ | rfl

theorem bindLB_rel {b : Bool} {x : Bounded (LRes × St)} {y : Option (LRes × St)}
    {k : List Value → St → Bounded (Res × St)} {k' : List Value → St → Option (Res × St)}
    (hx : x.rel b y) (hk : ∀ vs s, (k vs s).rel b (k' vs s)) : (bindLB x k).rel b (bindL y k') := by
  cases x with
  | deep => exact hx
  | fuel => simp only [Bounded.rel] at hx; subst hx; rfl
  | res z =>
    simp only [Bounded.rel] at hx; subst hx
    rcases z with ⟨r, s⟩
    cases r <;> first | exact hk _ _ | rfl

/-- Through a `bind`: from the first evaluation and every continuation. -/
theorem Bounded.bind_rel {α β : Type} {b : Bool} {x : Bounded α} {y : Option α}
    (k : Option α → Bounded β) (k' : Option α → Option β)
    (hx : x.rel b y) (hk : ∀ z, (k z).rel b (k' z)) : (x.bind k).rel b (k' y) := by
  cases x with
  | deep => exact hx
  | fuel => simp only [Bounded.rel] at hx; subst hx; exact hk none
  | res a => simp only [Bounded.rel] at hx; subst hx; exact hk (some a)

/-- A related result that did not stop early is the interpreter's result. -/
theorem Bounded.eq_ofOption {α : Type} {b : Bool} {x : Bounded α} {y : Option α}
    (h : x.rel b y) (hx : x ≠ .deep) : x = .ofOption y := by
  cases x with
  | deep => exact absurd rfl hx
  | fuel => simp only [Bounded.rel] at h; subst h; rfl
  | res a => simp only [Bounded.rel] at h; subst h; rfl

/-- Close a goal `(.res x).rel b (some x)`, `.fuel.rel b none`, or one that the
    hypotheses of a `split` settle. -/
macro "agree_leaf" : tactic =>
  `(tactic| first | exact rfl | trivial | (simp_all [Bounded.rel]; done))

theorem evalB_rel (P : Prog) (b : Bool) : ∀ n,
    (∀ d, (b = true → n ≤ d) → ∀ s e, (evalB P n d s e).rel b (eval P n s e)) ∧
    (∀ d, (b = true → n ≤ d) → ∀ s es, (evalListB P n d s es).rel b (evalList P n s es)) ∧
    (∀ d, (b = true → n ≤ d) → ∀ i filt body s vs acc,
      (evalForB P n d i filt body s vs acc).rel b (evalFor P n i filt body s vs acc))
  | 0 => ⟨fun _ _ _ _ => by simp only [evalB, eval]; agree_leaf,
      fun _ _ _ _ => by simp only [evalListB, evalList]; agree_leaf,
      fun _ _ _ _ _ _ _ _ => by simp only [evalForB, evalFor]; agree_leaf⟩
  | n+1 => by
    obtain ⟨ihE', ihL', ihF'⟩ := evalB_rel P b n
    -- the entry check `| _+1, 0, …` cannot fire under the strict hypothesis
    have deep_ok : ∀ {α} {y : Option α}, (b = true → n + 1 ≤ 0) → (Bounded.deep).rel b y := by
      intro _ _ h; cases b
      · rfl
      · exact absurd (h rfl) (by omega)
    refine ⟨fun d hd s e => ?_, fun d hd s es => ?_, fun d hd i filt body s vs acc => ?_⟩
    · cases d with
      | zero => simp only [evalB]; exact deep_ok hd
      | succ d =>
        have ihE := fun d' (h : d ≤ d') => ihE' d' (fun hb => by have := hd hb; omega)
        have ihL := fun d' (h : d ≤ d') => ihL' d' (fun hb => by have := hd hb; omega)
        have ihF := fun d' (h : d ≤ d') => ihF' d' (fun hb => by have := hd hb; omega)
        cases e with
        | lit v => simp only [evalB, eval]; agree_leaf
        | «local» i => simp only [evalB, eval]; agree_leaf
        | assign i e =>
          simp only [evalB, eval]
          exact bindRB_rel (ihE d (Nat.le_refl _) s e) fun v s₁ => by split <;> agree_leaf
        | seq a b =>
          simp only [evalB, eval]
          exact bindRB_rel (ihE d (Nat.le_refl _) s a) fun _ s₁ => ihE (d+1) (Nat.le_succ _) s₁ b
        | prim op es =>
          simp only [evalB, eval]
          exact bindLB_rel (ihL d (Nat.le_refl _) s es) fun _ _ => by split <;> agree_leaf
        | heap op es =>
          simp only [evalB, eval]
          exact bindLB_rel (ihL d (Nat.le_refl _) s es) fun _ _ => by agree_leaf
        | call f es =>
          simp only [evalB, eval]
          refine bindLB_rel (ihL d (Nat.le_refl _) s es) fun vs s₁ => ?_
          split
          · next hfn => simp only [hfn]; agree_leaf
          · next fn hfn =>
            simp only [hfn]
            refine Bounded.bind_rel (β := Res × St) _ (fun (z : Option (Res × St)) => match z with
              | none => none
              | some (r, s₂) => some (retOf r, ⟨s₁.fr, s₂.g⟩)) (ihE d (Nat.le_refl _) _ _) fun z => ?_
            rcases z with _ | ⟨r, s₂⟩ <;> agree_leaf
        | ite c t e =>
          simp only [evalB, eval]
          refine Bounded.bind_rel (β := Res × St) _ (fun (z : Option (Res × St)) => match z with
            | none => none
            | some (.ok _, s₁) => eval P n s₁ t
            | some (.fail, _) => eval P n s e
            | some (.brk, s₁) => some (.brk, s₁)
            | some (.ret v, s₁) => some (.ret v, s₁)
            | some (.err k, s₁) => some (.err k, s₁)) (ihE d (Nat.le_refl _) s c) fun z => ?_
          rcases z with _ | ⟨r, s₁⟩
          · agree_leaf
          · cases r with
            | ok v => exact ihE (d+1) (Nat.le_succ _) s₁ t
            | fail => exact ihE (d+1) (Nat.le_succ _) s e
            | _ => agree_leaf
        | forE i it filt body =>
          simp only [evalB, eval]
          refine bindRB_rel (ihE d (Nat.le_refl _) s it) fun v s₁ => ?_
          cases v <;> first | agree_leaf | exact ihF d (Nat.le_refl _) i filt body s₁ _ []
        | loop b =>
          simp only [evalB, eval]
          refine Bounded.bind_rel (β := Res × St) _ (fun (z : Option (Res × St)) => match z with
            | none => none
            | some (.ok _, s₁) => eval P n s₁ (.loop b)
            | some (.brk, s₁) => some (.ok .void, s₁)
            | some (.fail, s₁) => some (.fail, s₁)
            | some (.ret v, s₁) => some (.ret v, s₁)
            | some (.err k, s₁) => some (.err k, s₁)) (ihE d (Nat.le_refl _) s b) fun z => ?_
          rcases z with _ | ⟨r, s₁⟩
          · agree_leaf
          · cases r with
            | ok v => exact ihE (d+1) (Nat.le_succ _) s₁ (.loop b)
            | _ => agree_leaf
        | brk => simp only [evalB, eval]; agree_leaf
        | ret e =>
          simp only [evalB, eval]
          exact bindRB_rel (ihE d (Nat.le_refl _) s e) fun _ _ => by agree_leaf
        | print e =>
          simp only [evalB, eval]
          exact bindRB_rel (ihE d (Nat.le_refl _) s e) fun v s₁ => by split <;> agree_leaf
    · cases d with
      | zero => simp only [evalListB]; exact deep_ok hd
      | succ d =>
        have ihE := fun d' (h : d ≤ d') => ihE' d' (fun hb => by have := hd hb; omega)
        have ihL := fun d' (h : d ≤ d') => ihL' d' (fun hb => by have := hd hb; omega)
        have ihF := fun d' (h : d ≤ d') => ihF' d' (fun hb => by have := hd hb; omega)
        cases es with
        | nil => simp only [evalListB, evalList]; agree_leaf
        | cons e es =>
          simp only [evalListB, evalList]
          refine Bounded.bind_rel (β := LRes × St) _ (fun (z : Option (Res × St)) => match z with
            | none => none
            | some (.ok v, s₁) => match evalList P n s₁ es with
              | none => none
              | some (.ok vs, s₂) => some (.ok (v :: vs), s₂)
              | some (.stop r, s₂) => some (.stop r, s₂)
            | some (.fail, s₁) => some (.stop .fail, s₁)
            | some (.brk, s₁) => some (.stop .brk, s₁)
            | some (.ret v, s₁) => some (.stop (.ret v), s₁)
            | some (.err k, s₁) => some (.stop (.err k), s₁)) (ihE d (Nat.le_refl _) s e) fun z => ?_
          rcases z with _ | ⟨r, s₁⟩
          · agree_leaf
          · cases r with
            | ok v =>
              refine Bounded.bind_rel (β := LRes × St) _ (fun (z : Option (LRes × St)) => match z with
                | none => none
                | some (.ok vs, s₂) => some (.ok (v :: vs), s₂)
                | some (.stop r, s₂) => some (.stop r, s₂)) (ihL d (Nat.le_refl _) s₁ es) fun z => ?_
              rcases z with _ | ⟨r, s₂⟩
              · agree_leaf
              · cases r <;> agree_leaf
            | _ => agree_leaf
    · cases d with
      | zero => simp only [evalForB]; exact deep_ok hd
      | succ d =>
        have ihE := fun d' (h : d ≤ d') => ihE' d' (fun hb => by have := hd hb; omega)
        have ihL := fun d' (h : d ≤ d') => ihL' d' (fun hb => by have := hd hb; omega)
        have ihF := fun d' (h : d ≤ d') => ihF' d' (fun hb => by have := hd hb; omega)
        cases vs with
        | nil => simp only [evalForB, evalFor]; agree_leaf
        | cons v vs =>
          simp only [evalForB, evalFor]
          split
          · next hs => simp only [hs]; agree_leaf
          · next s₀ hs₀ =>
            simp only [hs₀]
            refine Bounded.bind_rel (β := Res × St) _ (fun (z : Option (Res × St)) => match z with
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
              | some (.err k, s₁) => some (.err k, s₁)) (ihE d (Nat.le_refl _) s₀ filt) fun z => ?_
            rcases z with _ | ⟨r, s₁⟩
            · agree_leaf
            · cases r with
              | fail => exact ihF (d+1) (Nat.le_succ _) i filt body s₀ vs acc
              | ok u =>
                refine Bounded.bind_rel (β := Res × St) _ (fun (z : Option (Res × St)) => match z with
                  | none => none
                  | some (.ok w, s₂) => evalFor P n i filt body s₂ vs (w :: acc)
                  | some (.fail, s₂) => some (.fail, s₂)
                  | some (.brk, s₂) => some (.brk, s₂)
                  | some (.ret v, s₂) => some (.ret v, s₂)
                  | some (.err k, s₂) => some (.err k, s₂)) (ihE d (Nat.le_refl _) s₁ body) fun z => ?_
                rcases z with _ | ⟨r, s₂⟩
                · agree_leaf
                · cases r with
                  | ok w => exact ihF (d+1) (Nat.le_succ _) i filt body s₂ vs (w :: acc)
                  | _ => agree_leaf
              | _ => agree_leaf

/-- **`openverse run` computes the reference interpreter.** Whenever `evalB`
    does not stop for depth, its result is exactly `eval`'s. -/
theorem evalB_sound {P : Prog} {n d : Nat} {s : St} {e : Expr} (h : evalB P n d s e ≠ .deep) :
    evalB P n d s e = .ofOption (eval P n s e) :=
  Bounded.eq_ofOption ((evalB_rel P false n).1 d (fun h => nomatch h) s e) h

/-- **The depth bound is not vacuous.** With a budget at least the fuel,
    `evalB` never stops early: it is `eval`. -/
theorem evalB_complete {P : Prog} {n d : Nat} {s : St} {e : Expr} (hd : n ≤ d) :
    evalB P n d s e = .ofOption (eval P n s e) := by
  have h := (evalB_rel P true n).1 d (fun _ => hd) s e
  refine Bounded.eq_ofOption h fun hdeep => ?_
  rw [hdeep] at h
  exact absurd h (by simp [Bounded.rel])

theorem Prog.runB_ofOption {P : Prog} {n d : Nat}
    (h : evalB P n d Prog.initSt (.call P.main []) = .ofOption (eval P n Prog.initSt (.call P.main []))) :
    P.runB n d = .ofOption (P.run n) := by
  unfold Prog.runB Prog.run
  rw [h]
  rcases eval P n Prog.initSt (.call P.main []) with _ | ⟨r, s⟩ <;> rfl

/-- Whenever `openverse run` does not stop for depth, its outcome and output
    are `Prog.run`'s. -/
theorem Prog.runB_sound {P : Prog} {n d : Nat} (h : P.runB n d ≠ .deep) :
    P.runB n d = .ofOption (P.run n) := by
  refine Prog.runB_ofOption (evalB_sound fun hd => h ?_)
  unfold Prog.runB; rw [hd]

/-- With a depth budget at least the fuel, `openverse run` is `Prog.run`. -/
theorem Prog.runB_complete {P : Prog} {n d : Nat} (hd : n ≤ d) :
    P.runB n d = .ofOption (P.run n) :=
  Prog.runB_ofOption (evalB_complete hd)

end OpenVerse
