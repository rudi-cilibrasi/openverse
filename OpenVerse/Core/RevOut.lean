/-
  OpenVerse — the bounded interpreter with an output that costs its own length (#782).

  The state's output is a list of bytes, oldest first, and a `Print` appends
  to it (`out ++ bs` in `Eval`, `eval` and `evalB`). Compiled, that append
  copies everything printed so far, so a run that printed `k` bytes spent
  `k²` steps on them: 32,000 `Print`s took two minutes.

  `evalR` is `evalB` on states whose output is kept *newest byte first*: a
  `Print` conses its bytes onto the list (`bs.reverseAux out`), which costs
  the length of `bs` alone and shares the rest, so that a failure context
  still rolls its output back by returning to the state it kept. Nothing
  else differs. `evalR_rev` proves it: on the reversed state `evalR` gives
  `evalB`'s result with the output reversed. `Prog.runR` runs `evalR` and
  reverses the output once at the end, and `Prog.runB_eq_runR` (`@[csimp]`)
  proves it equal to `Prog.runB`, which the compiler therefore replaces by
  it: `openverse run` executes `evalR`, and every theorem about `runB`
  (`Prog.runB_sound`, `Prog.runB_complete`) is about what it executes. The
  semantics, `eval` and `evalB` are untouched.
-/
import OpenVerse.Core.Bounded

namespace OpenVerse

mutual
/-- `evalB` on a state whose output is kept newest byte first: a `Print` conses its bytes. -/
def evalR (P : Prog) : Nat → Nat → St → Expr → Bounded (Res × St)
  | 0, _, _, _ => .fuel
  | _+1, 0, _, _ => .deep
  | _+1, _+1, s, .lit v => .res (.ok v, s)
  | _+1, _+1, s, .local i => .res (readSlot s i, s)
  | n+1, d+1, s, .assign i e => bindRB (evalR P n d s e) fun v s₁ =>
      match writeSlot s₁ i v with
      | some s₂ => .res (.ok v, s₂)
      | none => .res (.err .slot, s₁)
  | n+1, d+1, s, .seq a b => bindRB (evalR P n d s a) fun _ s₁ => evalR P n (d+1) s₁ b
  | n+1, d+1, s, .prim op es => bindLB (evalListR P n d s es) fun vs s₁ =>
      if n < op.cost vs then .fuel else .res (op.apply vs, s₁)
  | n+1, d+1, s, .heap op es => bindLB (evalListR P n d s es) fun vs s₁ =>
      .res (St.heapStep op vs s₁)
  | n+1, d+1, s, .call f es => bindLB (evalListR P n d s es) fun vs s₁ =>
      match P.callable f vs.length with
      | none => .res (.err .call, s₁)
      | some fn => (evalR P n d ⟨frameOf fn vs, s₁.g⟩ fn.body).bind fun
        | none => .fuel
        | some (r, s₂) => .res (retOf r, ⟨s₁.fr, s₂.g⟩)
  | n+1, d+1, s, .ite c t e => (evalR P n d s c).bind fun
      | none => .fuel
      | some (.ok _, s₁) => evalR P n (d+1) s₁ t
      | some (.fail, _) => evalR P n (d+1) s e
      | some (.brk, s₁) => .res (.brk, s₁)
      | some (.ret v, s₁) => .res (.ret v, s₁)
      | some (.err k, s₁) => .res (.err k, s₁)
  | n+1, d+1, s, .forE i it filt body => bindRB (evalR P n d s it) fun v s₁ =>
      match v with
      | .arr vs => evalForR P n d i filt body s₁ vs.toList []
      | .int _ | .logic _ | .char _ | .float _ | .tup _ | .none | .some _ | .ref _ => .res (.err .type, s₁)
  | n+1, d+1, s, .loop b => (evalR P n d s b).bind fun
      | none => .fuel
      | some (.ok _, s₁) => evalR P n (d+1) s₁ (.loop b)
      | some (.brk, s₁) => .res (.ok .void, s₁)
      | some (.fail, s₁) => .res (.fail, s₁)
      | some (.ret v, s₁) => .res (.ret v, s₁)
      | some (.err k, s₁) => .res (.err k, s₁)
  | _+1, _+1, s, .brk => .res (.brk, s)
  | n+1, d+1, s, .ret e => bindRB (evalR P n d s e) fun v s₁ => .res (.ret v, s₁)
  | n+1, d+1, s, .print e => bindRB (evalR P n d s e) fun v s₁ =>
      match printBytes v with
      | some bs => .res (.ok .void, { s₁ with g := { s₁.g with out := bs.reverseAux s₁.g.out } })
      | none => .res (.err .type, s₁)

/-- `evalListB`, likewise. -/
def evalListR (P : Prog) : Nat → Nat → St → List Expr → Bounded (LRes × St)
  | 0, _, _, _ => .fuel
  | _+1, 0, _, _ => .deep
  | _+1, _+1, s, [] => .res (.ok [], s)
  | n+1, d+1, s, e :: es => (evalR P n d s e).bind fun
    | none => .fuel
    | some (.ok v, s₁) => (evalListR P n d s₁ es).bind fun
      | none => .fuel
      | some (.ok vs, s₂) => .res (.ok (v :: vs), s₂)
      | some (.stop r, s₂) => .res (.stop r, s₂)
    | some (.fail, s₁) => .res (.stop .fail, s₁)
    | some (.brk, s₁) => .res (.stop .brk, s₁)
    | some (.ret v, s₁) => .res (.stop (.ret v), s₁)
    | some (.err k, s₁) => .res (.stop (.err k), s₁)

/-- `evalForB`, likewise. -/
def evalForR (P : Prog) : Nat → Nat → Nat → Expr → Expr → St → List Value → List Value →
    Bounded (Res × St)
  | 0, _, _, _, _, _, _, _ => .fuel
  | _+1, 0, _, _, _, _, _, _ => .deep
  | _+1, _+1, _, _, _, s, [], acc => .res (.ok (Value.ofArray acc.reverse.toArray), s)
  | n+1, d+1, i, filt, body, s, v :: vs, acc => match writeSlot s i v with
    | none => .res (.err .slot, s)
    | some s₀ => (evalR P n d s₀ filt).bind fun
      | none => .fuel
      | some (.fail, _) => evalForR P n (d+1) i filt body s₀ vs acc
      | some (.ok _, s₁) => (evalR P n d s₁ body).bind fun
        | none => .fuel
        | some (.ok w, s₂) => evalForR P n (d+1) i filt body s₂ vs (w :: acc)
        | some (.fail, s₂) => .res (.fail, s₂)
        | some (.brk, s₂) => .res (.brk, s₂)
        | some (.ret v, s₂) => .res (.ret v, s₂)
        | some (.err k, s₂) => .res (.err k, s₂)
      | some (.brk, s₁) => .res (.brk, s₁)
      | some (.ret v, s₁) => .res (.ret v, s₁)
      | some (.err k, s₁) => .res (.err k, s₁)
end

/-- Run `Main()` with `evalR`; the output is put oldest first at the end. -/
def Prog.runR (P : Prog) (n d : Nat) : Bounded (Res × List Nat) :=
  match evalR P n d Prog.initSt (.call P.main []) with
  | .fuel => .fuel
  | .res (r, s) => .res (r, s.g.out.reverse)
  | .deep => .deep

/-! ### `evalR` is `evalB` on reversed outputs -/

/-- The state with its output reversed. -/
def St.rev (s : St) : St := ⟨s.fr, ⟨s.g.out.reverse, s.g.heap⟩⟩

/-- A bounded result with the output of its state reversed. -/
def Bounded.revSt {α : Type} : Bounded (α × St) → Bounded (α × St)
  | .fuel => .fuel
  | .res (a, s) => .res (a, s.rev)
  | .deep => .deep

theorem readSlot_rev (s : St) (i : Nat) : readSlot s.rev i = readSlot s i := rfl

theorem writeSlot_rev (s : St) (i : Nat) (v : Value) :
    writeSlot s.rev i v = (writeSlot s i v).map St.rev := by
  simp only [writeSlot, St.rev]; split <;> simp [*, St.rev]

/-- A heap operation neither reads nor writes the output. -/
theorem HeapOp.apply_out (op : HeapOp) (vs : List Value) (out out' : List Nat) (heap : Array Obj) :
    op.apply vs ⟨out', heap⟩ =
      ((op.apply vs ⟨out, heap⟩).1, ⟨out', (op.apply vs ⟨out, heap⟩).2.heap⟩) := by
  cases op <;> rcases vs with _ | ⟨v, _ | ⟨w, _ | ⟨u, t⟩⟩⟩ <;> (try cases v) <;>
    simp only [HeapOp.apply] <;> (repeat' split) <;> rfl

theorem St.heapStep_rev (op : HeapOp) (vs : List Value) (s : St) :
    St.heapStep op vs s.rev = ((St.heapStep op vs s).1, (St.heapStep op vs s).2.rev) := by
  rcases s with ⟨fr, ⟨out, heap⟩⟩
  simp only [St.heapStep_eq, St.rev]
  rw [HeapOp.apply_out op vs out out.reverse heap, HeapOp.apply_out op vs out out heap]

theorem bindRB_rev {x y : Bounded (Res × St)} {k k' : Value → St → Bounded (Res × St)}
    (hx : x = y.revSt) (hk : ∀ v s, k v s.rev = (k' v s).revSt) :
    bindRB x k = (bindRB y k').revSt := by
  subst hx
  cases y with
  | fuel => rfl
  | deep => rfl
  | res z => rcases z with ⟨r, s⟩; cases r <;> first | exact hk _ _ | rfl

theorem bindLB_rev {x y : Bounded (LRes × St)} {k k' : List Value → St → Bounded (Res × St)}
    (hx : x = y.revSt) (hk : ∀ vs s, k vs s.rev = (k' vs s).revSt) :
    bindLB x k = (bindLB y k').revSt := by
  subst hx
  cases y with
  | fuel => rfl
  | deep => rfl
  | res z => rcases z with ⟨r, s⟩; cases r <;> first | exact hk _ _ | rfl

/-- Through a `bind`: from the first evaluation and every continuation. -/
theorem Bounded.bind_rev {α β : Type} {x y : Bounded (α × St)}
    {k k' : Option (α × St) → Bounded (β × St)}
    (hx : x = y.revSt) (hn : k none = (k' none).revSt)
    (hs : ∀ a s, k (some (a, s.rev)) = (k' (some (a, s))).revSt) :
    x.bind k = (y.bind k').revSt := by
  subst hx
  cases y with
  | fuel => exact hn
  | deep => rfl
  | res z => rcases z with ⟨a, s⟩; exact hs a s

theorem evalR_rev (P : Prog) : ∀ n,
    (∀ d s e, evalR P n d s.rev e = (evalB P n d s e).revSt) ∧
    (∀ d s es, evalListR P n d s.rev es = (evalListB P n d s es).revSt) ∧
    (∀ d i filt body s vs acc,
      evalForR P n d i filt body s.rev vs acc = (evalForB P n d i filt body s vs acc).revSt)
  | 0 => ⟨fun _ _ _ => by simp only [evalR, evalB]; rfl,
      fun _ _ _ => by simp only [evalListR, evalListB]; rfl,
      fun _ _ _ _ _ _ _ => by simp only [evalForR, evalForB]; rfl⟩
  | n+1 => by
    obtain ⟨ihE, ihL, ihF⟩ := evalR_rev P n
    refine ⟨fun d s e => ?_, fun d s es => ?_, fun d i filt body s vs acc => ?_⟩
    · cases d with
      | zero => simp only [evalR, evalB]; rfl
      | succ d =>
        cases e with
        | lit v => simp only [evalR, evalB]; rfl
        | «local» i => simp only [evalR, evalB]; rfl
        | assign i e =>
          simp only [evalR, evalB]
          refine bindRB_rev (ihE d s e) fun v s₁ => ?_
          rw [writeSlot_rev]
          cases writeSlot s₁ i v <;> rfl
        | seq a b =>
          simp only [evalR, evalB]
          exact bindRB_rev (ihE d s a) fun _ s₁ => ihE (d+1) s₁ b
        | prim op es =>
          simp only [evalR, evalB]
          exact bindLB_rev (ihL d s es) fun _ _ => by split <;> rfl
        | heap op es =>
          simp only [evalR, evalB]
          exact bindLB_rev (ihL d s es) fun vs s₁ => by rw [St.heapStep_rev]; rfl
        | call f es =>
          simp only [evalR, evalB]
          refine bindLB_rev (ihL d s es) fun vs s₁ => ?_
          cases P.callable f vs.length with
          | none => rfl
          | some fn =>
            refine Bounded.bind_rev (ihE d ⟨frameOf fn vs, s₁.g⟩ fn.body) ?_ fun r s₂ => ?_ <;> rfl
        | ite c t e =>
          simp only [evalR, evalB]
          refine Bounded.bind_rev (ihE d s c) rfl fun r s₁ => ?_
          cases r with
          | ok v => exact ihE (d+1) s₁ t
          | fail => exact ihE (d+1) s e
          | _ => rfl
        | forE i it filt body =>
          simp only [evalR, evalB]
          refine bindRB_rev (ihE d s it) fun v s₁ => ?_
          cases v <;> first | rfl | exact ihF d i filt body s₁ _ []
        | loop b =>
          simp only [evalR, evalB]
          refine Bounded.bind_rev (ihE d s b) rfl fun r s₁ => ?_
          cases r with
          | ok v => exact ihE (d+1) s₁ (.loop b)
          | _ => rfl
        | brk => simp only [evalR, evalB]; rfl
        | ret e =>
          simp only [evalR, evalB]
          exact bindRB_rev (ihE d s e) fun _ _ => rfl
        | print e =>
          simp only [evalR, evalB]
          refine bindRB_rev (ihE d s e) fun v s₁ => ?_
          cases printBytes v with
          | none => rfl
          | some bs =>
            simp only [Bounded.revSt, St.rev, List.reverseAux_eq, List.reverse_append]
    · cases d with
      | zero => simp only [evalListR, evalListB]; rfl
      | succ d =>
        cases es with
        | nil => simp only [evalListR, evalListB]; rfl
        | cons e es =>
          simp only [evalListR, evalListB]
          refine Bounded.bind_rev (ihE d s e) rfl fun r s₁ => ?_
          cases r with
          | ok v =>
            refine Bounded.bind_rev (ihL d s₁ es) rfl fun r s₂ => ?_
            cases r <;> rfl
          | _ => rfl
    · cases d with
      | zero => simp only [evalForR, evalForB]; rfl
      | succ d =>
        cases vs with
        | nil => simp only [evalForR, evalForB]; rfl
        | cons v vs =>
          simp only [evalForR, evalForB]
          rw [writeSlot_rev]
          cases writeSlot s i v with
          | none => rfl
          | some s₀ =>
            refine Bounded.bind_rev (ihE d s₀ filt) rfl fun r s₁ => ?_
            cases r with
            | fail => exact ihF (d+1) i filt body s₀ vs acc
            | ok u =>
              refine Bounded.bind_rev (ihE d s₁ body) rfl fun r s₂ => ?_
              cases r with
              | ok w => exact ihF (d+1) i filt body s₂ vs (w :: acc)
              | _ => rfl
            | _ => rfl

/-- **`openverse run` executes `Prog.runR`.** It is `Prog.runB`: the compiler
    replaces the one by the other, and the output costs its own length. -/
@[csimp] theorem Prog.runB_eq_runR : @Prog.runB = @Prog.runR := by
  funext P n d
  have h := (evalR_rev P n).1 d Prog.initSt (.call P.main [])
  have h0 : Prog.initSt.rev = Prog.initSt := rfl
  rw [h0] at h
  unfold Prog.runB Prog.runR
  rw [h]
  cases evalB P n d Prog.initSt (.call P.main []) with
  | fuel => rfl
  | deep => rfl
  | res z => rcases z with ⟨r, ⟨fr, ⟨out, heap⟩⟩⟩; simp [Bounded.revSt, St.rev]

end OpenVerse
