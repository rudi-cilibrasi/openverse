/-
  OpenVerse — derived surface forms and their rollback laws.

  The Book of Verse (ch. 4 "Operators", ch. 8 "Failure") describes these
  constructs; here each is a definition in terms of Verse Core, followed by
  the theorems that say it behaves as the book states:

  * `not e` succeeds exactly when `e` fails, and *always* discards the
    effects of `e` ("`not e` always throws away `e`'s effects").
  * `a or b` gives `a`'s value if `a` succeeds, else `b`'s, with the effects
    of a failed `a` rolled back.
  * `option{e}` is `some v` when `e` succeeds with `v` and the empty option
    (with no effects) when it fails.
  * `logic{e}` is `true` / `false` in the same way.
  * A failed `if` condition leaves no trace: the `else` branch behaves
    exactly as if the condition had never run.
  * A choice `a₀ | … | aₙ₋₁` (#208) in a context that takes its first
    success is its first alternative that succeeds, with the alternatives
    before it rolled back (`firstE_chooseFirst_ok`), and fails when none
    does (`firstE_chooseFirst_fail`).
-/
import OpenVerse.Core.Adequacy

namespace OpenVerse

/-- `not e` (the result of a successful `not` is `void`). -/
def Expr.notE (e : Expr) : Expr := .ite e (.prim .fail []) (.lit .void)
/-- `a or b`; slot `t` is a fresh temporary of the elaborator. -/
def Expr.orE (t : Nat) (a b : Expr) : Expr := .ite (.assign t a) (.local t) b
/-- `a and b`: the value of `b`. -/
def Expr.andE (a b : Expr) : Expr := .seq a b
/-- `option{e}`; slot `t` is a fresh temporary. -/
def Expr.optionE (t : Nat) (e : Expr) : Expr :=
  .ite (.assign t e) (.prim .mkSome [.local t]) (.lit .none)
/-- `logic{e}`. -/
def Expr.logicE (e : Expr) : Expr := .ite e (.lit (.logic true)) (.lit (.logic false))

/-! ### Small inversion helpers -/

theorem Eval.lit_inv {P s v r s'} (h : Eval P s (.lit v) r s') : r = .ok v ∧ s' = s := by
  cases h; exact ⟨rfl, rfl⟩

theorem Eval.fail_inv {P s r s'} (h : Eval P s (.prim .fail []) r s') : r = .fail ∧ s' = s := by
  cases h with
  | prim_ok hl => cases hl; exact ⟨rfl, rfl⟩
  | prim_stop hl => cases hl

/-! ### Failure contexts roll back -/

/-- **Rollback of `if`.** Once the condition has failed, the whole `if`
    behaves as its `else` branch run from the *original* state. -/
theorem ite_rollback {P s s₁ c t e r s'} (hc : Eval P s c .fail s₁) :
    Eval P s (.ite c t e) r s' ↔ Eval P s e r s' := by
  constructor
  · intro h
    cases h with
    | ite_ok h1 _ => exact absurd (Eval.det h1 hc).1 (by simp)
    | ite_fail _ h2 => exact h2
    | ite_stop h1 _ hf => exact absurd (Eval.det h1 hc).1 hf
  · intro h; exact .ite_fail hc h

/-- **`not` discards effects.** A successful `not e` returns `void` and
    leaves the state exactly as it found it. -/
theorem notE_ok {P s e v s'} (h : Eval P s (Expr.notE e) (.ok v) s') :
    v = .void ∧ s' = s ∧ ∃ s₁, Eval P s e .fail s₁ := by
  unfold Expr.notE at h
  cases h with
  | ite_ok _ h2 => exact absurd (Eval.fail_inv h2).1 (by simp)
  | ite_fail h1 h2 =>
    obtain ⟨hv, hs⟩ := Eval.lit_inv h2
    cases hv; exact ⟨rfl, hs, _, h1⟩
  | ite_stop _ hr _ => simp at hr

/-- `not e` fails when `e` succeeds. -/
theorem notE_of_ok {P s e v s₁} (h : Eval P s e (.ok v) s₁) :
    Eval P s (Expr.notE e) .fail s₁ :=
  .ite_ok h (.prim_ok .nil)

/-- `not e` succeeds, with no effect, when `e` fails. -/
theorem notE_of_fail {P s e s₁} (h : Eval P s e .fail s₁) :
    Eval P s (Expr.notE e) (.ok .void) s :=
  .ite_fail h .lit

/-- **`not not e` is a pure test**: it succeeds exactly when `e` succeeds,
    and never changes the state. -/
theorem notE_notE_ok {P s e v s'} (h : Eval P s (Expr.notE (Expr.notE e)) (.ok v) s') :
    s' = s ∧ ∃ u s₁, Eval P s e (.ok u) s₁ := by
  obtain ⟨-, hs, s₁, hf⟩ := notE_ok h
  refine ⟨hs, ?_⟩
  unfold Expr.notE at hf
  cases hf with
  | ite_ok h1 h2 => exact ⟨_, _, h1⟩
  | ite_fail _ h2 => exact absurd (Eval.lit_inv h2).1 (by simp)
  | ite_stop _ _ hf' => exact absurd rfl hf'

/-- `mkSome` never produces the empty option. -/
theorem Eval.mkSome_ne_none {P s e r s'} (h : Eval P s (.prim .mkSome [e]) r s')
    (hr : r = .ok .none) : False := by
  cases h with
  | prim_ok hl =>
    cases hl with
    | cons_ok _ hl' => cases hl'; simp [Prim.apply] at hr
  | prim_stop hl =>
    cases hl with
    | cons_stop _ h' => subst hr; simp at h'
    | cons_stop_tail _ hl' => cases hl'

/-- **`option{}` of a failure is empty and effect-free.** -/
theorem optionE_none {P s t e s'} (h : Eval P s (Expr.optionE t e) (.ok .none) s') : s' = s := by
  unfold Expr.optionE at h
  cases h with
  | ite_ok _ h2 => exact (Eval.mkSome_ne_none h2 rfl).elim
  | ite_fail _ h2 => exact (Eval.lit_inv h2).2
  | ite_stop _ hr _ => simp at hr

/-- `option{e}` of a success with `v` is `some v`. -/
theorem optionE_some {P s t e v s₁ s₂} (h : Eval P s e (.ok v) s₁) (hw : writeSlot s₁ t v = some s₂) :
    Eval P s (Expr.optionE t e) (.ok (.some v)) s₂ := by
  unfold Expr.optionE
  have hread : readSlot s₂ t = .ok v := by
    unfold writeSlot at hw
    split at hw
    · next hlt =>
      simp only [Option.some.injEq] at hw; subst hw
      simp [readSlot, List.getElem?_set_self hlt]
    · simp at hw
  have := Eval.prim_ok (P := P) (op := .mkSome)
    (EvalList.cons_ok (hread ▸ Eval.local) EvalList.nil)
  exact .ite_ok (.assign_ok h hw) (by simpa [Prim.apply] using this)

/-- `option{e}` of a failure is the empty option. -/
theorem optionE_of_fail {P s t e s₁} (h : Eval P s e .fail s₁) :
    Eval P s (Expr.optionE t e) (.ok .none) s :=
  .ite_fail (.assign_stop h rfl) .lit

/-- `a or b` with a failing `a` is `b` from the original state. -/
theorem orE_right {P s s₁ t a b r s'} (ha : Eval P s a .fail s₁) :
    Eval P s (Expr.orE t a b) r s' ↔ Eval P s b r s' :=
  ite_rollback (.assign_stop ha rfl)

/-- `logic{e}` is `false`, with no effect, when `e` fails. -/
theorem logicE_of_fail {P s e s₁} (h : Eval P s e .fail s₁) :
    Eval P s (Expr.logicE e) (.ok (.logic false)) s :=
  .ite_fail h .lit

/-- `logic{e}` never fails. -/
theorem logicE_ne_fail {P s e s'} (h : Eval P s (Expr.logicE e) .fail s') : False := by
  unfold Expr.logicE at h
  cases h with
  | ite_ok _ h2 => exact absurd (Eval.lit_inv h2).1 (by simp)
  | ite_fail _ h2 => exact absurd (Eval.lit_inv h2).1 (by simp)
  | ite_stop _ _ hf => exact hf rfl

/-! ### Choice (#208)

`a₀ | … | aₙ₋₁` is not a construct of Verse Core: in a failure context, the
front end compiles it to iteration over the indices of its alternatives, in
the Verse Calculus's spatial order (alternative `0` first). Slot `k` holds
the index of the alternative being tried, and `altE` selects it.

* In a `for`, a binding `X := a₀ | …` is a generator over `choiceIdx n`
  whose filter starts with `X := altE k as`, so each alternative is tried in
  order and a failing one is skipped and rolled back (`EvalFor.skip`).
* In a context that takes the first success (an `if` condition, `first{}`),
  `chooseFirst` tries the alternatives in order, each followed by the rest
  of the clauses, which `break` once they all succeed; `firstE` makes the
  context fail when no alternative did. A nested choice is a `chooseFirst`
  in the rest of the clauses, so in the *filter* of the outer one: when all
  its alternatives fail, the outer alternative is rolled back too. -/

/-- Alternative `i` of `as` when slot `k` holds `j + i`. -/
def Expr.altFrom (k j : Nat) : List Expr → Expr
  | [] => .prim .fail []
  | [a] => a
  | a :: as => .ite (.prim .eq [.local k, .lit (.int j)]) a (Expr.altFrom k (j + 1) as)

/-- The alternative of `as` that slot `k` selects. -/
def Expr.altE (k : Nat) (as : List Expr) : Expr := Expr.altFrom k 0 as

/-- The indices of `n` alternatives. -/
def choiceIdx (n : Nat) : Array Value :=
  ((List.range n).map fun (j : Nat) => Value.int (j : Int)).toArray

/-- Try the alternatives `as` in order: bind each to slot `x`, then run
    `inner`, the clauses after the choice, which `break` when they succeed. -/
def Expr.chooseFirst (k x : Nat) (as : List Expr) (inner : Expr) : Expr :=
  .forE k (.lit (.arr (choiceIdx as.length)))
    (.seq (.assign x (Expr.altE k as)) (.seq inner (.prim .fail []))) (.lit .void)

/-- The first success of `c`, code that `break`s when it succeeds and ends
    normally when it does not. -/
def Expr.firstE (c : Expr) : Expr := .loop (.seq c (.prim .fail []))

/-- The state with slot `k` set to `v`. -/
def St.setSlot (s : St) (k : Nat) (v : Value) : St := ⟨s.fr.set k v, s.g⟩

theorem choiceIdx_toList (n : Nat) :
    (choiceIdx n).toList = (List.range n).map fun (j : Nat) => Value.int (j : Int) := by
  simp [choiceIdx]

/-- The test of `altFrom`, `k = j`, when slot `k` holds `v`. -/
theorem Eval.eq_slot {P s k v} (j : Int) (hk : readSlot s k = .ok v) :
    Eval P s (.prim .eq [.local k, .lit (.int j)]) (cmpRes (decide (v = .int j)) v) s := by
  have h := Eval.prim_ok (P := P) (op := .eq)
    (EvalList.cons_ok (hk ▸ (Eval.local (P := P) (s := s) (i := k)))
      (EvalList.cons_ok (Eval.lit (v := .int j)) .nil))
  simpa [Prim.apply] using h

/-- **Selecting an alternative.** When slot `k` holds `j + i`, `altFrom k j
    as` behaves exactly as `as[i]`. -/
theorem altFrom_sel {P s k} : ∀ {as : List Expr} {j i : Nat} (hi : i < as.length),
    readSlot s k = .ok (.int ((j : Int) + (i : Int))) →
    ∀ {r s'}, (Eval P s (Expr.altFrom k j as) r s' ↔ Eval P s as[i] r s')
  | [], _, _, hi, _, _, _ => absurd hi (by simp)
  | [a], j, i, hi, _, _, _ => by
    have : i = 0 := by simp at hi; omega
    subst this; simp [Expr.altFrom]
  | a :: b :: as, j, i, hi, hk, r, s' => by
    have htest := Eval.eq_slot (P := P) (j : Int) hk
    cases i with
    | zero =>
      have hok : Eval P s (.prim .eq [.local k, .lit (.int j)]) (.ok (.int ((j : Int) + ((0 : Nat) : Int)))) s := by
        simpa [cmpRes] using htest
      simp only [Expr.altFrom, List.getElem_cons_zero]
      constructor
      · intro h
        cases h with
        | ite_ok h1 h2 => obtain ⟨-, rfl⟩ := Eval.det h1 hok; exact h2
        | ite_fail h1 _ => exact absurd (Eval.det h1 hok).1 (by simp)
        | ite_stop h1 _ hf => exact absurd (Eval.det h1 hok).1 (by intro h; subst h; simp_all)
      · intro h; exact .ite_ok hok h
    | succ i =>
      have hfail : Eval P s (.prim .eq [.local k, .lit (.int j)]) .fail s := by
        have hne : ¬ (Value.int ((j : Int) + ((i + 1 : Nat) : Int)) = .int (j : Int)) := by
          intro h; injection h with h; omega
        have hne' : ¬ ((j : Int) + ((i : Int) + 1) = (j : Int)) := by omega
        simpa [cmpRes, hne'] using htest
      have hk' : readSlot s k = .ok (.int (((j + 1 : Nat) : Int) + (i : Int))) := by
        rw [hk]; congr 2; push_cast; omega
      have ih := altFrom_sel (P := P) (as := b :: as) (j := j + 1) (i := i) (by simp at hi ⊢; omega) hk'
        (r := r) (s' := s')
      simp only [Expr.altFrom] at ih ⊢
      rw [List.getElem_cons_succ, ← ih]
      constructor
      · intro h
        cases h with
        | ite_ok h1 _ => exact absurd (Eval.det h1 hfail).1 (by simp)
        | ite_fail _ h2 => exact h2
        | ite_stop h1 _ hf => exact absurd (Eval.det h1 hfail).1 hf
      · intro h; exact .ite_fail hfail h

/-- `altE k as` is `as[i]` when slot `k` holds `i`. -/
theorem altE_sel {P : Prog} {s : St} {k : Nat} {as : List Expr} {i : Nat} (hi : i < as.length) (hk : readSlot s k = .ok (.int (i : Int))) {r s'} :
    Eval P s (Expr.altE k as) r s' ↔ Eval P s as[i] r s' :=
  altFrom_sel hi (by simpa using hk)

/-- A binding followed by more code depends only on the outcomes of the
    bound expression. -/
theorem Eval.seq_assign_of {P s x e e' G r s'} (h : ∀ {r s'}, Eval P s e r s' → Eval P s e' r s')
    (he : Eval P s (.seq (.assign x e) G) r s') : Eval P s (.seq (.assign x e') G) r s' := by
  cases he with
  | seq_ok ha hb =>
    cases ha with
    | assign_ok h1 h2 => exact .seq_ok (.assign_ok (h h1) h2) hb
    | assign_stop _ hr => simp at hr
  | seq_stop ha hr =>
    cases ha with
    | assign_ok h1 h2 => simp at hr
    | assign_bad h1 h2 => exact .seq_stop (.assign_bad (h h1) h2) hr
    | assign_stop h1 h2 => exact .seq_stop (.assign_stop (h h1) h2) hr

theorem Eval.seq_assign_congr {P s x e e' G r s'} (h : ∀ {r s'}, Eval P s e r s' ↔ Eval P s e' r s') :
    Eval P s (.seq (.assign x e) G) r s' ↔ Eval P s (.seq (.assign x e') G) r s' :=
  ⟨Eval.seq_assign_of h.mp, Eval.seq_assign_of h.mpr⟩

/-- Writing slot `k` of a state whose frame agrees with `s`'s except at `k`. -/
theorem writeSlot_like {s t : St} {k : Nat} (v : Value) (hk : k < s.fr.length) (hg : t.g = s.g)
    (hset : ∀ v, t.fr.set k v = s.fr.set k v) (hlen : t.fr.length = s.fr.length) :
    writeSlot t k v = some (s.setSlot k v) := by
  rcases t with ⟨fr, g⟩
  simp only at hg hset hlen
  subst hg
  have hk' : k < fr.length := by omega
  simp [writeSlot, St.setSlot, hk', hset]

/-- The iterations of a `for` over the indices `m, …, m+c-1`, of which `j`
    is the first whose filter `break`s: the earlier ones fail. -/
theorem evalFor_firstBrk {P : Prog} {k : Nat} {F B : Expr} {s s' : St} {j : Nat} (hk : k < s.fr.length)
    (hfail : ∀ i, i < j → ∃ s₁, Eval P (s.setSlot k (.int i)) F .fail s₁)
    (hbrk : Eval P (s.setSlot k (.int j)) F .brk s') :
    ∀ (c m : Nat) (t : St) (acc : List Value), m ≤ j → j < m + c → t.g = s.g →
      (∀ v, t.fr.set k v = s.fr.set k v) → t.fr.length = s.fr.length →
      EvalFor P k F B t ((List.range' m c).map fun (i : Nat) => Value.int (i : Int)) acc .brk s'
  | 0, m, _, _, h1, h2, _, _, _ => absurd h2 (by omega)
  | c + 1, m, t, acc, h1, h2, hg, hset, hlen => by
    have hw := writeSlot_like (.int m) hk hg hset hlen
    simp only [List.range'_succ, List.map_cons]
    by_cases hm : m = j
    · subst hm
      exact .filt_stop hw hbrk rfl (by simp)
    · obtain ⟨s₁, hf⟩ := hfail m (by omega)
      refine .skip hw hf ?_
      exact evalFor_firstBrk hk hfail hbrk c (m + 1) _ acc (by omega) (by omega) rfl
        (fun v => by simp [St.setSlot]) (by simp [St.setSlot])

/-- The iterations of a `for` over the indices `m, …, m+c-1` (all below
    `n`) whose filters all fail: no value, and the `for` ends normally. -/
theorem evalFor_allFail {P : Prog} {k : Nat} {F B : Expr} {s : St} {n : Nat} (hk : k < s.fr.length)
    (hfail : ∀ i, i < n → ∃ s₁, Eval P (s.setSlot k (.int i)) F .fail s₁) :
    ∀ (c m : Nat) (t : St), m + c ≤ n → t.g = s.g → (∀ v, t.fr.set k v = s.fr.set k v) →
      t.fr.length = s.fr.length →
      ∃ t', EvalFor P k F B t ((List.range' m c).map fun (i : Nat) => Value.int (i : Int))
        [] (.ok (.arr #[])) t'
  | 0, _, t, _, _, _, _ =>
    ⟨t, by simpa using EvalFor.done (P := P) (i := k) (filt := F) (body := B) (s := t) (acc := [])⟩
  | c + 1, m, t, hmc, hg, hset, hlen => by
    have hw := writeSlot_like (.int m) hk hg hset hlen
    obtain ⟨s₁, hf⟩ := hfail m (by omega)
    obtain ⟨t', ht⟩ := evalFor_allFail hk hfail c (m + 1) (s.setSlot k (.int m)) (by omega) rfl
      (fun v => by simp [St.setSlot]) (by simp [St.setSlot])
    exact ⟨t', by simpa [List.range'_succ] using EvalFor.skip hw hf ht⟩

/-- The filter of `chooseFirst` at alternative `i` is alternative `i`
    itself, bound to `x`, then the rest. -/
theorem chooseFirst_filt {P : Prog} {s : St} {k x : Nat} {as : List Expr} {inner : Expr} {i : Nat} (hk : k < s.fr.length) (hi : i < as.length) {r s'} :
    Eval P (s.setSlot k (.int i)) (.seq (.assign x (Expr.altE k as)) (.seq inner (.prim .fail []))) r s' ↔
      Eval P (s.setSlot k (.int i)) (.seq (.assign x as[i]) (.seq inner (.prim .fail []))) r s' :=
  Eval.seq_assign_congr (altE_sel hi (by simp [readSlot, St.setSlot, List.getElem?_set_self hk]))

/-- **A choice takes its first success.** If the alternatives before `j`
    fail (each one, bound to `x`, then the rest of the clauses `inner`,
    started from `s` with slot `k` set to its index: the effects of the
    earlier ones are rolled back) and alternative `j` succeeds (`inner`
    breaks), the context succeeds in the state alternative `j` left. The
    alternatives after `j` never run. -/
theorem firstE_chooseFirst_ok {P : Prog} {s : St} {k x : Nat} {as : List Expr} {inner : Expr} {j : Nat} {s' : St} (hk : k < s.fr.length) (hj : j < as.length)
    (hbefore : ∀ i (hi : i < j), ∃ s₁, Eval P (s.setSlot k (.int i))
      (.seq (.assign x (as[i]'(Nat.lt_trans hi hj))) (.seq inner (.prim .fail []))) .fail s₁)
    (hbrk : Eval P (s.setSlot k (.int j)) (.seq (.assign x as[j]) (.seq inner (.prim .fail []))) .brk s') :
    Eval P s (Expr.firstE (Expr.chooseFirst k x as inner)) (.ok .void) s' := by
  unfold Expr.firstE Expr.chooseFirst
  refine .loop_brk (.seq_stop (.for_ok .lit ?_) rfl)
  rw [choiceIdx_toList, List.range_eq_range']
  refine evalFor_firstBrk hk (j := j) (fun i hi => ?_) ((chooseFirst_filt hk hj).mpr hbrk)
    as.length 0 s [] (by omega) (by omega) rfl (fun _ => rfl) rfl
  obtain ⟨s₁, h⟩ := hbefore i hi
  exact ⟨s₁, (chooseFirst_filt hk (Nat.lt_trans hi hj)).mpr h⟩

/-- **A choice with no success fails** (and the enclosing failure context
    rolls its effects back, `ite_rollback`). -/
theorem firstE_chooseFirst_fail {P : Prog} {s : St} {k x : Nat} {as : List Expr} {inner : Expr} (hk : k < s.fr.length)
    (hall : ∀ i (hi : i < as.length), ∃ s₁, Eval P (s.setSlot k (.int i))
      (.seq (.assign x as[i]) (.seq inner (.prim .fail []))) .fail s₁) :
    ∃ s', Eval P s (Expr.firstE (Expr.chooseFirst k x as inner)) .fail s' := by
  unfold Expr.firstE Expr.chooseFirst
  have hf : ∀ i, i < as.length → ∃ s₁, Eval P (s.setSlot k (.int i))
      (.seq (.assign x (Expr.altE k as)) (.seq inner (.prim .fail []))) .fail s₁ := by
    intro i hi
    obtain ⟨s₁, h⟩ := hall i hi
    exact ⟨s₁, (chooseFirst_filt hk hi).mpr h⟩
  obtain ⟨t', ht⟩ := evalFor_allFail (B := .lit .void) hk hf as.length 0 s (by omega) rfl (fun _ => rfl) rfl
  rw [← List.range_eq_range', ← choiceIdx_toList] at ht
  exact ⟨t', .loop_stop (.seq_ok (.for_ok .lit ht) (.prim_ok .nil)) rfl (by simp)⟩

end OpenVerse
