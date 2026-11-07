/-
  OpenVerse — a decidable type checker for Verse Core, proved sound.

  The front end hands each elaborated program to `Prog.checkTypes` together
  with a certificate it knows from elaboration: the signature of every
  function and the type of every slot. `Prog.checkTypes_sound` proves that a
  program passing the check is `ProgTyped`, so type safety (`Runs.typed`)
  applies to every program the front end accepts.

  `tc e m` is bidirectional: with `m = none` it infers a type of `e`, with
  `m = some τ` it checks `e` against `τ` (needed for the polymorphic forms:
  `false` and `array{}` literals, `break`, `return`, `false?`, `Err()`).
  Every recursive call is on a strict subterm, so the soundness proof
  `tc_sound` follows the definition case by case.
-/
import OpenVerse.Core.TypeSafety

namespace OpenVerse

mutual
/-- The type of a literal, when it determines one. -/
def litTy : Value → Option VTy
  | .int _ => some .int
  | .logic _ => some .logic
  | .char c => if c < 256 then some .char else none
  | .arr [] => none
  | .arr (v :: vs) => match litTy v with
    | some t => if allTy [] vs t then some (.arr t) else none
    | none => none
  | .tup vs => (litTys vs).map .tup
  | .none => none
  | .some v => (litTy v).map .opt
  | .ref _ => none
def litTys : List Value → Option (List VTy)
  | [] => some []
  | v :: vs => match litTy v, litTys vs with
    | some t, some ts => some (t :: ts)
    | _, _ => none
end

mutual
theorem litTy_sound : ∀ {v : Value} {t : VTy}, litTy v = some t → hasTy [] v t = true
  | .ref _, _, h => by simp [litTy] at h
  | .int _, t, h => by simp [litTy] at h; subst h; rfl
  | .logic _, t, h => by simp [litTy] at h; subst h; rfl
  | .char c, t, h => by
    simp only [litTy] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [hasTy, *]
    · simp at h
  | .arr [], _, h => by simp [litTy] at h
  | .arr (v :: vs), t, h => by
    simp only [litTy] at h
    split at h
    · next t' hv =>
      split at h
      · next hall => simp only [Option.some.injEq] at h; subst h; simp [hasTy, allTy, litTy_sound hv, hall]
      · simp at h
    · simp at h
  | .tup vs, t, h => by
    simp only [litTy] at h
    rcases hl : litTys vs with _ | ts
    · simp [hl] at h
    · simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
      simp [hasTy, litTys_sound hl]
  | .none, _, h => by simp [litTy] at h
  | .some v, t, h => by
    simp only [litTy] at h
    rcases hl : litTy v with _ | t'
    · simp [hl] at h
    · simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
      simp [hasTy, litTy_sound hl]
theorem litTys_sound : ∀ {vs : List Value} {ts : List VTy}, litTys vs = some ts → allTys [] vs ts = true
  | [], ts, h => by simp [litTys] at h; subst h; rfl
  | v :: vs, ts, h => by
    simp only [litTys] at h
    split at h
    · next t ts' hv hvs =>
      simp only [Option.some.injEq] at h; subst h; simp [allTys, litTy_sound hv, litTys_sound hvs]
    · simp at h
end

/-- In check mode, the type must be the expected one. -/
def expect : Option VTy → VTy → Option VTy
  | none, t => some t
  | some τ, t => if τ = t then some t else none

theorem expect_sound {m : Option VTy} {t τ : VTy} (h : expect m t = some τ) :
    τ = t ∧ ∀ τ', m = some τ' → τ = τ' := by
  cases m with
  | none => simp [expect] at h; subst h; simp
  | some τ' =>
    simp only [expect] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; subst_vars; simp
    · simp at h

mutual
/-- Bind type variables by first-order matching of `p` against `a` (no
    proof obligation: `tc` checks the call against whatever this proposes). -/
def VTy.bindVars : VTy → VTy → List (Nat × VTy) → List (Nat × VTy)
  | .var j, a, acc => if (acc.lookup j).isSome then acc else (j, a) :: acc
  | .arr p, .arr a, acc => VTy.bindVars p a acc
  | .opt p, .opt a, acc => VTy.bindVars p a acc
  | .tup ps, .tup as, acc => VTy.bindVarsL ps as acc
  | _, _, acc => acc
def VTy.bindVarsL : List VTy → List VTy → List (Nat × VTy) → List (Nat × VTy)
  | p :: ps, a :: as, acc => VTy.bindVarsL ps as (VTy.bindVars p a acc)
  | _, _, acc => acc
end

mutual
/-- Whether `p` mentions a type variable that `acc` does not bind. -/
def VTy.unbound (acc : List (Nat × VTy)) : VTy → Bool
  | .var j => (acc.lookup j).isNone
  | .arr t => VTy.unbound acc t
  | .opt t => VTy.unbound acc t
  | .tup ts => VTy.unboundL acc ts
  | _ => false
def VTy.unboundL (acc : List (Nat × VTy)) : List VTy → Bool
  | [] => false
  | t :: ts => VTy.unbound acc t || VTy.unboundL acc ts
end

/-- `expect`, but a reference also has every type with more classes. -/
def expectSub : Option VTy → VTy → Option VTy
  | some (.ref us), .ref ts => if ts.all us.contains then some (.ref us) else none
  | m, t => expect m t

theorem expectSub_sound {m : Option VTy} {t τ : VTy} (h : expectSub m t = some τ) :
    ((τ = t ∧ ∀ τ', m = some τ' → τ = τ') ∨
      ∃ ts us, t = .ref ts ∧ τ = .ref us ∧ m = some τ ∧ ∀ u ∈ ts, u ∈ us) := by
  unfold expectSub at h
  split at h
  · next us ts =>
    split at h
    · next hsub =>
      simp only [Option.some.injEq] at h; subst h
      simp only [List.all_eq_true, List.contains_iff_mem] at hsub
      exact .inr ⟨ts, us, rfl, rfl, rfl, hsub⟩
    · simp at h
  · exact .inl (expect_sound h)

/-- The type of `new t` in mode `m`: a reference to any classes including `t`. -/
def expectNew : Option VTy → Nat → Option VTy
  | some (.ref ts), t => if ts.contains t then some (.ref ts) else none
  | some _, _ => none
  | none, t => some (.ref [t])

theorem expectNew_sound {m : Option VTy} {t : Nat} {τ : VTy} (h : expectNew m t = some τ) :
    ∃ ts, τ = .ref ts ∧ t ∈ ts ∧ ∀ τ', m = some τ' → τ = τ' := by
  unfold expectNew at h
  split at h
  · next ts =>
    split at h
    · next ht => simp only [Option.some.injEq] at h; subst h; exact ⟨ts, rfl, by simpa using ht, by simp⟩
    · simp at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨[t], rfl, by simp, by simp⟩

/-- The type of field `k` of the classes `ts`, when they all have one, the
    same, without type variables (`FieldTy`). -/
def fieldTy (S : Sigs) (ts : List Nat) (k : Nat) : Option VTy :=
  match ts with
  | [] => none
  | t :: _ => match S.classes[t]?.bind (·[k]?) with
    | some τ =>
      if τ.closed && ts.all (fun u => decide (S.classes[u]?.bind (·[k]?) = some τ)) then some τ
      else none
    | none => none

theorem fieldTy_sound {S : Sigs} {ts : List Nat} {k : Nat} {τ : VTy} (h : fieldTy S ts k = some τ) :
    FieldTy S ts k τ := by
  unfold fieldTy at h
  split at h
  · simp at h
  · split at h
    · next τ' _ =>
      split at h
      · next hc =>
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
        refine ⟨hc.1, fun u hu => ?_⟩
        obtain ⟨fs, hfs, hk⟩ := Option.bind_eq_some_iff.mp (hc.2 u hu)
        exact ⟨fs, hfs, hk⟩
      · simp at h
    · simp at h

/-- The instantiation `tc` proposes for a call with result type `t`: the
    bindings `acc` from the arguments, completed from the expected type. -/
def callInst (acc : List (Nat × VTy)) (t : VTy) (m : Option VTy) : Nat → VTy :=
  let acc := match m with
    | some τ => if t.unbound acc then t.bindVars τ acc else acc
    | none => acc
  fun j => (acc.lookup j).getD (.var j)

section
variable (S : Sigs) (Γ : List VTy) (ρ : VTy)

mutual
/-- `tc e none` infers a type of `e`; `tc e (some τ)` checks `e` against `τ`. -/
def tc : Expr → Option VTy → Option VTy
  | .lit v, some τ => if hasTy [] v τ then some τ else none
  | .lit v, none => litTy v
  | .local i, m => match Γ[i]? with
    | some t => expectSub m t
    | none => none
  | .assign i e, m => match Γ[i]? with
    | some t => if (tc e (some t)).isSome then expect m t else none
    | none => none
  | .seq a b, m => if (tc a none).isSome || (tc a (some VTy.void)).isSome then tc b m else none
  | .call f es, m => match S.fns[f]? with
    | some (ps, t) =>
      -- propose an instantiation (from the arguments, then the expected type),
      -- then check against it: only the check needs a proof
      let θ := callInst (bindArgs ps es []) t m
      if tcL es (ps.map (VTy.subst θ)) then expect m (t.subst θ) else none
    | none => none
  | .ite c t e, m =>
    if (tc c none).isSome || (tc c (some VTy.void)).isSome then
      match m with
      | some τ => if (tc t (some τ)).isSome && (tc e (some τ)).isSome then some τ else none
      | none => match tc t none with
        | some τ => if (tc e (some τ)).isSome then some τ else none
        | none => match tc e none with
          | some τ => if (tc t (some τ)).isSome then some τ else none
          | none => none
    else none
  | .forE i it filt body, m => match Γ[i]? with
    | some te =>
      if (tc it (some (.arr te))).isSome &&
          ((tc filt none).isSome || (tc filt (some VTy.void)).isSome) then
        match m with
        | some (.arr tb) => if (tc body (some tb)).isSome then some (.arr tb) else none
        | some _ => none
        | none => (tc body none).map .arr
      else none
    | none => none
  | .loop b, m =>
    if (tc b none).isSome || (tc b (some VTy.void)).isSome then expect m VTy.void else none
  | .brk, some τ => some τ
  | .brk, none => none
  | .ret e, some τ => if (tc e (some ρ)).isSome then some τ else none
  | .ret _, none => none
  | .print e, m => if (tc e (some VTy.str)).isSome then expect m VTy.void else none
  | .heap (.new t) es, m => match S.classes[t]? with
    | some fs =>
      if tcL es fs then expectNew m t else none
    | none => none
  | .heap (.get k) [e], m => match tc e none with
    | some (.ref ts) => match fieldTy S ts k with
      | some τ => expect m τ
      | none => none
    | _ => none
  | .heap (.set k) [e, v], m => match tc e none with
    | some (.ref ts) => match fieldTy S ts k with
      | some τ => if (tc v (some τ)).isSome then expect m τ else none
      | none => none
    | _ => none
  | .heap .tag [e], m => match tc e none with
    | some (.ref _) => expect m .int
    | _ => none
  | .heap (.isTag us) [e], m => match tc e none with
    | some (.ref _) => expect m (.ref us)
    | _ => none
  | .heap _ _, _ => none
  | .prim op es, m => tcPrim op es m
/-- `tc` for a primitive application. -/
def tcPrim : Prim → List Expr → Option VTy → Option VTy
  | .add, [a, b], m | .sub, [a, b], m | .mul, [a, b], m | .floorDiv, [a, b], m
  | .ceilDiv, [a, b], m | .quotient, [a, b], m | .modulo, [a, b], m =>
    if (tc a (some .int)).isSome && (tc b (some .int)).isSome then expect m .int else none
  | .neg, [a], m | .abs, [a], m => if (tc a (some .int)).isSome then expect m .int else none
  | .lt, [a, b], m | .le, [a, b], m | .gt, [a, b], m | .ge, [a, b], m => match tc a none with
    | some .int => if (tc b (some .int)).isSome then expect m .int else none
    | some .char => if (tc b (some .char)).isSome then expect m .char else none
    | _ => none
  -- the right operand is checked against the left's type first, so that
  -- `O = false` and `E = array{}` type-check (`PrimTy.eq` allows any types)
  | .eq, [a, b], m | .ne, [a, b], m => match tc a m with
    | some ta =>
      if (tc b (some ta)).isSome || (tc b none).isSome || (tc b (some VTy.void)).isSome then some ta
      else none
    | none => none
  | .query, [a], none => match tc a none with
    | some .logic => some .logic
    | some (.opt t) => some t
    | _ => none
  | .query, [a], some τ => if (tc a (some (.opt τ))).isSome then some τ else none
  | .mkArr, es, some (.arr t) => if tcAll es t then some (.arr t) else none
  | .mkArr, a :: rest, none => match tc a none with
    | some t => if tcAll rest t then some (.arr t) else none
    | none => none
  | .mkTup, es, some (.tup ts) => if tcL es ts then some (.tup ts) else none
  | .mkTup, es, none => (inferL es).map .tup
  | .mkSome, [a], some (.opt t) => if (tc a (some t)).isSome then some (.opt t) else none
  | .mkSome, [a], none => (tc a none).map .opt
  | .concat, [a, b], some (.arr t) =>
    if (tc a (some (.arr t))).isSome && (tc b (some (.arr t))).isSome then some (.arr t) else none
  | .concat, [a, b], none => match tc a none with
    | some (.arr t) => if (tc b (some (.arr t))).isSome then some (.arr t) else none
    | _ => match tc b none with
      | some (.arr t) => if (tc a (some (.arr t))).isSome then some (.arr t) else none
      | _ => none
  | .index, [a, i], m => match tc a none with
    | some (.arr t) => if (tc i (some .int)).isSome then expect m t else none
    | _ => none
  | .len, [a], m => match tc a none with
    | some (.arr _) => expect m .int
    | _ => none
  | .arrSet, [a, i, v], m => match tc a none with
    | some (.arr t) =>
      if (tc i (some .int)).isSome && (tc v (some t)).isSome then expect m (.arr t) else none
    | _ => none
  | .flatten, [a], m => match tc a none with
    | some (.arr (.arr t)) => expect m (.arr t)
    | _ => none
  | .range, [a, b], m =>
    if (tc a (some .int)).isSome && (tc b (some .int)).isSome then expect m (.arr .int) else none
  | .tupGet k, [a], m => match tc a none with
    | some (.tup ts) => match ts[k]? with
      | some t => expect m t
      | none => none
    | _ => none
  | .toStr, [a], m => match tc a none with
    | some .int => expect m VTy.str
    | some .char => expect m VTy.str
    | some (.arr .char) => expect m VTy.str
    | _ => none
  | .fail, [], some τ => some τ
  | .userErr, [], some τ => some τ
  | _, _, _ => none
/-- Check a list against a list of types. -/
def tcL : List Expr → List VTy → Bool
  | [], [] => true
  | e :: es, t :: ts => (tc e (some t)).isSome && tcL es ts
  | _, _ => false
/-- Check every element of a list against one type. -/
def tcAll : List Expr → VTy → Bool
  | [], _ => true
  | e :: es, t => (tc e (some t)).isSome && tcAll es t
/-- Bind the type variables of parameter types `ps` from arguments `es`,
    right to left, inferring an argument only while its parameter type has an
    unbound variable. A generic function's hidden arguments come last and
    bind them all, and a call of a function without type variables infers
    nothing, so each argument is checked once. -/
def bindArgs : List VTy → List Expr → List (Nat × VTy) → List (Nat × VTy)
  | p :: ps, e :: es, acc =>
    let acc := bindArgs ps es acc
    if p.unbound acc then
      match tc e none with
      | some a => p.bindVars a acc
      | none => acc
    else acc
  | _, _, acc => acc
/-- Infer the types of a list. -/
def inferL : List Expr → Option (List VTy)
  | [] => some []
  | e :: es => match tc e none, inferL es with
    | some t, some ts => some (t :: ts)
    | _, _ => none
end
end

end OpenVerse

namespace OpenVerse
section
variable {S : Sigs} {Γ : List VTy} {ρ : VTy}

/-- What `tc` promises about one expression. -/
def TcOK (S : Sigs) (Γ : List VTy) (ρ : VTy) (e : Expr) : Prop :=
  ∀ m τ, tc S Γ ρ e m = some τ → Typed S Γ ρ e τ ∧ ∀ τ', m = some τ' → τ = τ'

theorem typed_of_check {e t} (ih : TcOK S Γ ρ e) (h : (tc S Γ ρ e (some t)).isSome = true) :
    Typed S Γ ρ e t := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨ht, heq⟩ := ih _ _ hτ
  rw [heq t rfl] at ht
  exact ht

theorem typed_of_wt {e} (ih : TcOK S Γ ρ e)
    (h : ((tc S Γ ρ e none).isSome || (tc S Γ ρ e (some VTy.void)).isSome) = true) :
    ∃ σ, Typed S Γ ρ e σ := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h
    exact ⟨τ, (ih _ _ hτ).1⟩
  · exact ⟨_, typed_of_check ih h⟩

theorem tcL_sound_of : ∀ {es : List Expr} {ts}, (∀ e ∈ es, TcOK S Γ ρ e) →
    tcL S Γ ρ es ts = true → TypedL S Γ ρ es ts
  | [], [], _, _ => .nil
  | e :: es, t :: ts, ih, h => by
    simp only [tcL, Bool.and_eq_true] at h
    exact .cons (typed_of_check (ih e (by simp)) h.1)
      (tcL_sound_of (fun e' he' => ih e' (by simp [he'])) h.2)
  | [], _ :: _, _, h => by simp [tcL] at h
  | _ :: _, [], _, h => by simp [tcL] at h

theorem tcAll_sound_of : ∀ {es : List Expr} {t}, (∀ e ∈ es, TcOK S Γ ρ e) →
    tcAll S Γ ρ es t = true → TypedL S Γ ρ es (es.map fun _ => t)
  | [], _, _, _ => .nil
  | e :: es, t, ih, h => by
    simp only [tcAll, Bool.and_eq_true] at h
    exact .cons (typed_of_check (ih e (by simp)) h.1)
      (tcAll_sound_of (fun e' he' => ih e' (by simp [he'])) h.2)

theorem inferL_sound_of : ∀ {es : List Expr} {ts}, (∀ e ∈ es, TcOK S Γ ρ e) →
    inferL S Γ ρ es = some ts → TypedL S Γ ρ es ts
  | [], ts, _, h => by simp [inferL] at h; subst h; exact .nil
  | e :: es, ts, ih, h => by
    simp only [inferL] at h
    split at h
    · next t ts' he hes =>
      simp only [Option.some.injEq] at h; subst h
      exact .cons (ih e (by simp) _ _ he).1 (inferL_sound_of (fun e' he' => ih e' (by simp [he'])) hes)
    · simp at h

theorem map_const_eq {es : List Expr} {t : VTy} : ∀ u ∈ es.map (fun _ => t), u = t := by
  intro u hu; simp at hu; exact hu.2.symm

/-- `tcPrim` is sound, given that `tc` is sound on the arguments. -/
theorem tcPrim_sound_of {op : Prim} {es : List Expr} {m τ} (ih : ∀ e ∈ es, TcOK S Γ ρ e)
    (h : tcPrim S Γ ρ op es m = some τ) :
    Typed S Γ ρ (.prim op es) τ ∧ ∀ τ', m = some τ' → τ = τ' := by
  have chk : ∀ {e t}, e ∈ es → (tc S Γ ρ e (some t)).isSome = true → Typed S Γ ρ e t :=
    fun he h => typed_of_check (ih _ he) h
  have inf : ∀ {e t}, e ∈ es → tc S Γ ρ e none = some t → Typed S Γ ρ e t :=
    fun he h => (ih _ he _ _ h).1
  have wt : ∀ {e}, e ∈ es → ((tc S Γ ρ e none).isSome || (tc S Γ ρ e (some VTy.void)).isSome) = true →
      ∃ σ, Typed S Γ ρ e σ := fun he h => typed_of_wt (ih _ he) h
  -- the two-int-argument operations
  have arith2 : ∀ {a b}, es = [a, b] →
      (if (tc S Γ ρ a (some .int)).isSome && (tc S Γ ρ b (some .int)).isSome then expect m .int else none)
        = some τ → TypedL S Γ ρ es [.int, .int] ∧ τ = .int ∧ ∀ τ', m = some τ' → τ = τ' := by
    intro a b hes hh
    subst hes
    split at hh
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      obtain ⟨h1, h2⟩ := expect_sound hh
      exact ⟨.cons (chk (by simp) hc.1) (.cons (chk (by simp) hc.2) .nil), h1, h2⟩
    · simp at hh
  cases op with
  | add | sub | mul | floorDiv | ceilDiv | quotient | modulo =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp only [tcPrim] at h <;> try (simp at h; done)
    all_goals
      obtain ⟨hl, rfl, hm⟩ := arith2 rfl h
      exact ⟨.prim hl (.arith (by simp)), hm⟩
  | neg | abs =>
    rcases es with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [tcPrim] at h <;> try (simp at h; done)
    all_goals
      split at h
      · next hc =>
        obtain ⟨rfl, hm⟩ := expect_sound h
        exact ⟨.prim (.cons (chk (by simp) hc) .nil) (.unary (by simp)), hm⟩
      · simp at h
  | lt | le | gt | ge =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp only [tcPrim] at h <;> try (simp at h; done)
    all_goals
      split at h
      · next ha =>
        split at h
        · next hb =>
          obtain ⟨rfl, hm⟩ := expect_sound h
          exact ⟨.prim (.cons (inf (by simp) ha) (.cons (chk (by simp) hb) .nil)) (.cmpInt (by simp)), hm⟩
        · simp at h
      · next ha =>
        split at h
        · next hb =>
          obtain ⟨rfl, hm⟩ := expect_sound h
          exact ⟨.prim (.cons (inf (by simp) ha) (.cons (chk (by simp) hb) .nil)) (.cmpChar (by simp)), hm⟩
        · simp at h
      · simp at h
  | eq | ne =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp only [tcPrim] at h <;> try (simp at h; done)
    all_goals
      split at h
      · next ta ha =>
        split at h
        · next hb =>
          simp only [Option.some.injEq] at h; subst h
          have hb' : ∃ σ, Typed S Γ ρ b σ := by
            simp only [Bool.or_eq_true] at hb
            rcases hb with (hb | hb) | hb
            · exact ⟨_, chk (by simp) hb⟩
            · exact wt (by simp) (by simp [hb])
            · exact wt (by simp) (by simp [hb])
          obtain ⟨σ, hσ⟩ := hb'
          obtain ⟨hta, hm⟩ := ih a (by simp) _ _ ha
          first
          | exact ⟨.prim (.cons hta (.cons hσ .nil)) .eq, hm⟩
          | exact ⟨.prim (.cons hta (.cons hσ .nil)) .ne, hm⟩
        · simp at h
      · simp at h
  | query =>
    rcases es with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> try (simp [tcPrim] at h; done)
    cases m with
    | none =>
      simp only [tcPrim] at h
      split at h
      · next ha => simp only [Option.some.injEq] at h; subst h
                   exact ⟨.prim (.cons (inf (by simp) ha) .nil) .queryLogic, by simp⟩
      · next t ha => simp only [Option.some.injEq] at h; subst h
                     exact ⟨.prim (.cons (inf (by simp) ha) .nil) .queryOpt, by simp⟩
      · simp at h
    | some τ' =>
      simp only [tcPrim] at h
      split at h
      · next hc => simp only [Option.some.injEq] at h; subst h
                   exact ⟨.prim (.cons (chk (by simp) hc) .nil) .queryOpt, by simp⟩
      · simp at h
  | mkArr =>
    cases m with
    | none =>
      rcases es with _ | ⟨a, rest⟩
      · simp [tcPrim] at h
      · simp only [tcPrim] at h
        split at h
        · next t ha =>
          split at h
          · next hr =>
            simp only [Option.some.injEq] at h; subst h
            have hl := tcAll_sound_of (fun e he => ih e (by simp [he])) hr
            exact ⟨.prim (.cons (inf (by simp) ha) hl) (.mkArr (by
              intro u hu; simp at hu; rcases hu with rfl | ⟨_, _, rfl⟩ <;> rfl)), by simp⟩
          · simp at h
        · simp at h
    | some τ' =>
      cases τ' with
      | arr t =>
        simp only [tcPrim] at h
        split at h
        · next hc =>
          simp only [Option.some.injEq] at h; subst h
          exact ⟨.prim (tcAll_sound_of ih hc) (.mkArr map_const_eq), by simp⟩
        · simp at h
      | _ => rcases es with _ | ⟨a, rest⟩ <;> simp [tcPrim] at h
  | mkTup =>
    cases m with
    | none =>
      simp only [tcPrim] at h
      rcases hl : inferL S Γ ρ es with _ | ts
      · simp [hl] at h
      · simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
        exact ⟨.prim (inferL_sound_of ih hl) .mkTup, by simp⟩
    | some τ' =>
      cases τ' with
      | tup ts =>
        simp only [tcPrim] at h
        split at h
        · next hc =>
          simp only [Option.some.injEq] at h; subst h
          exact ⟨.prim (tcL_sound_of ih hc) .mkTup, by simp⟩
        · simp at h
      | _ => simp [tcPrim] at h
  | mkSome =>
    rcases es with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> try (cases m <;> simp [tcPrim] at h; done)
    cases m with
    | none =>
      simp only [tcPrim] at h
      rcases ha : tc S Γ ρ a none with _ | t
      · simp [ha] at h
      · simp only [ha, Option.map_some, Option.some.injEq] at h; subst h
        exact ⟨.prim (.cons (inf (by simp) ha) .nil) .mkSome, by simp⟩
    | some τ' =>
      cases τ' with
      | opt t =>
        simp only [tcPrim] at h
        split at h
        · next hc =>
          simp only [Option.some.injEq] at h; subst h
          exact ⟨.prim (.cons (chk (by simp) hc) .nil) .mkSome, by simp⟩
        · simp at h
      | _ => simp [tcPrim] at h
  | concat =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> try (cases m <;> simp [tcPrim] at h; done)
    cases m with
    | none =>
      simp only [tcPrim] at h
      split at h
      · next t ha =>
        split at h
        · next hb =>
          simp only [Option.some.injEq] at h; subst h
          exact ⟨.prim (.cons (inf (by simp) ha) (.cons (chk (by simp) hb) .nil)) .concat, by simp⟩
        · simp at h
      · split at h
        · next t hb =>
          split at h
          · next ha =>
            simp only [Option.some.injEq] at h; subst h
            exact ⟨.prim (.cons (chk (by simp) ha) (.cons (inf (by simp) hb) .nil)) .concat, by simp⟩
          · simp at h
        · simp at h
    | some τ' =>
      cases τ' with
      | arr t =>
        simp only [tcPrim] at h
        split at h
        · next hc =>
          simp only [Bool.and_eq_true] at hc
          simp only [Option.some.injEq] at h; subst h
          exact ⟨.prim (.cons (chk (by simp) hc.1) (.cons (chk (by simp) hc.2) .nil)) .concat, by simp⟩
        · simp at h
      | _ => simp [tcPrim] at h
  | index =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp only [tcPrim] at h <;> try (simp at h; done)
    split at h
    · next t ha =>
      split at h
      · next hb =>
        obtain ⟨rfl, hm⟩ := expect_sound h
        exact ⟨.prim (.cons (inf (by simp) ha) (.cons (chk (by simp) hb) .nil)) .index, hm⟩
      · simp at h
    · simp at h
  | len =>
    rcases es with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [tcPrim] at h <;> try (simp at h; done)
    split at h
    · next t ha =>
      obtain ⟨rfl, hm⟩ := expect_sound h
      exact ⟨.prim (.cons (inf (by simp) ha) .nil) .len, hm⟩
    · simp at h
  | arrSet =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp only [tcPrim] at h <;>
      try (simp at h; done)
    split at h
    · next t ha =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true] at hc
        obtain ⟨rfl, hm⟩ := expect_sound h
        exact ⟨.prim (.cons (inf (by simp) ha) (.cons (chk (by simp) hc.1) (.cons (chk (by simp) hc.2) .nil)))
          .arrSet, hm⟩
      · simp at h
    · simp at h
  | flatten =>
    rcases es with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [tcPrim] at h <;> try (simp at h; done)
    split at h
    · next t ha =>
      obtain ⟨rfl, hm⟩ := expect_sound h
      exact ⟨.prim (.cons (inf (by simp) ha) .nil) .flatten, hm⟩
    · simp at h
  | range =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp only [tcPrim] at h <;> try (simp at h; done)
    split at h
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      obtain ⟨rfl, hm⟩ := expect_sound h
      exact ⟨.prim (.cons (chk (by simp) hc.1) (.cons (chk (by simp) hc.2) .nil)) .range, hm⟩
    · simp at h
  | tupGet k =>
    rcases es with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [tcPrim] at h <;> try (simp at h; done)
    split at h
    · next ts ha =>
      split at h
      · next t hk =>
        obtain ⟨rfl, hm⟩ := expect_sound h
        exact ⟨.prim (.cons (inf (by simp) ha) .nil) (.tupGet hk), hm⟩
      · simp at h
    · simp at h
  | toStr =>
    rcases es with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [tcPrim] at h <;> try (simp at h; done)
    split at h
    · next ha =>
      obtain ⟨rfl, hm⟩ := expect_sound h
      exact ⟨.prim (.cons (inf (by simp) ha) .nil) .toStrInt, hm⟩
    · next ha =>
      obtain ⟨rfl, hm⟩ := expect_sound h
      exact ⟨.prim (.cons (inf (by simp) ha) .nil) .toStrChar, hm⟩
    · next ha =>
      obtain ⟨rfl, hm⟩ := expect_sound h
      exact ⟨.prim (.cons (inf (by simp) ha) .nil) .toStrStr, hm⟩
    · simp at h
  | fail =>
    rcases es with _ | ⟨a, rest⟩ <;> cases m <;> simp [tcPrim] at h
    subst h; exact ⟨.prim .nil .fail, by simp⟩
  | userErr =>
    rcases es with _ | ⟨a, rest⟩ <;> cases m <;> simp [tcPrim] at h
    subst h; exact ⟨.prim .nil .userErr, by simp⟩

/-- `tc` is sound on a heap operation, given that it is on the arguments. -/
theorem tcHeap_sound_of {op : HeapOp} {es : List Expr} {m τ} (ih : ∀ e ∈ es, TcOK S Γ ρ e)
    (h : tc S Γ ρ (.heap op es) m = some τ) :
    Typed S Γ ρ (.heap op es) τ ∧ ∀ τ', m = some τ' → τ = τ' := by
  have inf : ∀ {e t}, e ∈ es → tc S Γ ρ e none = some t → Typed S Γ ρ e t :=
    fun he h => (ih _ he _ _ h).1
  cases op with
  | new t =>
    simp only [tc] at h
    split at h
    · next fs hc =>
      split at h
      · next hes =>
        obtain ⟨ts, rfl, ht, hm⟩ := expectNew_sound h
        exact ⟨.heap_new hc ht (tcL_sound_of ih hes), hm⟩
      · simp at h
    · simp at h
  | get k =>
    rcases es with _ | ⟨e, _ | ⟨_, _⟩⟩ <;> simp only [tc] at h <;> try (simp at h; done)
    split at h
    · next ts he =>
      split at h
      · next τ' hf =>
        obtain ⟨rfl, hm⟩ := expect_sound h
        exact ⟨.heap_get (inf (by simp) he) (fieldTy_sound hf), hm⟩
      · simp at h
    · simp at h
  | set k =>
    rcases es with _ | ⟨e, _ | ⟨v, _ | ⟨_, _⟩⟩⟩ <;> simp only [tc] at h <;> try (simp at h; done)
    split at h
    · next ts he =>
      split at h
      · next τ' hf =>
        split at h
        · next hv =>
          obtain ⟨rfl, hm⟩ := expect_sound h
          exact ⟨.heap_set (inf (by simp) he) (fieldTy_sound hf)
            (typed_of_check (ih v (by simp)) hv), hm⟩
        · simp at h
      · simp at h
    · simp at h
  | tag =>
    rcases es with _ | ⟨e, _ | ⟨_, _⟩⟩ <;> simp only [tc] at h <;> try (simp at h; done)
    split at h
    · next ts he =>
      obtain ⟨rfl, hm⟩ := expect_sound h
      exact ⟨.heap_tag (inf (by simp) he), hm⟩
    · simp at h
  | isTag us =>
    rcases es with _ | ⟨e, _ | ⟨_, _⟩⟩ <;> simp only [tc] at h <;> try (simp at h; done)
    split at h
    · next ts he =>
      obtain ⟨rfl, hm⟩ := expect_sound h
      exact ⟨.heap_isTag (inf (by simp) he), hm⟩
    · simp at h

end
end OpenVerse

namespace OpenVerse
section
variable {S : Sigs} {Γ : List VTy} {ρ : VTy}

theorem sizeOf_lt_of_mem_args {e : Expr} {es : List Expr} {op : Prim} (h : e ∈ es) :
    sizeOf e < sizeOf (Expr.prim op es) := by
  have := List.sizeOf_lt_of_mem h; simp; omega

theorem sizeOf_lt_of_mem_call {e : Expr} {es : List Expr} {f : Nat} (h : e ∈ es) :
    sizeOf e < sizeOf (Expr.call f es) := by
  have := List.sizeOf_lt_of_mem h; simp; omega

theorem sizeOf_lt_of_mem_heap {e : Expr} {es : List Expr} {op : HeapOp} (h : e ∈ es) :
    sizeOf e < sizeOf (Expr.heap op es) := by
  have := List.sizeOf_lt_of_mem h; simp; omega

theorem tc_sound_aux : ∀ (n : Nat) (e : Expr), sizeOf e < n → TcOK S Γ ρ e := by
  intro n
  induction n with
  | zero => intro e h; omega
  | succ n ih =>
    intro e hsz m τ h
    have IH : ∀ e', sizeOf e' < sizeOf e → TcOK S Γ ρ e' := fun e' h' => ih e' (by omega)
    cases e with
    | lit v =>
      cases m with
      | none => simp only [tc] at h; exact ⟨.lit (litTy_sound h), by simp⟩
      | some τ' =>
        simp only [tc] at h; split at h
        · next hv => simp only [Option.some.injEq] at h; subst h; exact ⟨.lit hv, by simp⟩
        · simp at h
    | «local» i =>
      simp only [tc] at h; split at h
      · next t hi =>
        rcases expectSub_sound h with ⟨rfl, hm⟩ | ⟨ts, us, rfl, rfl, rfl, hsub⟩
        · exact ⟨.local hi, hm⟩
        · exact ⟨.local_sub hi hsub, by simp⟩
      · simp at h
    | assign i e =>
      simp only [tc] at h; split at h
      · next t hi =>
        split at h
        · next hc =>
          obtain ⟨rfl, hm⟩ := expect_sound h
          exact ⟨.assign hi (typed_of_check (IH e (by simp <;> omega)) hc), hm⟩
        · simp at h
      · simp at h
    | seq a b =>
      simp only [tc] at h; split at h
      · next hw =>
        obtain ⟨σ, hσ⟩ := typed_of_wt (IH a (by simp <;> omega)) hw
        obtain ⟨hb, hm⟩ := IH b (by simp <;> omega) _ _ h
        exact ⟨.seq hσ hb, hm⟩
      · simp at h
    | call f es =>
      simp only [tc] at h; split at h
      · next ps t hf =>
        split at h
        · next hc =>
          obtain ⟨rfl, hm⟩ := expect_sound h
          exact ⟨.call _ hf (tcL_sound_of (fun e he => IH e (sizeOf_lt_of_mem_call he)) hc), hm⟩
        · simp at h
      · simp at h
    | ite c t e =>
      have Ic := IH c (by simp <;> omega)
      have It := IH t (by simp <;> omega)
      have Ie := IH e (by simp <;> omega)
      cases m with
      | some τ' =>
        simp only [tc] at h; split at h
        · next hw =>
          obtain ⟨σ, hσ⟩ := typed_of_wt Ic hw
          split at h
          · next hc =>
            simp only [Bool.and_eq_true] at hc
            simp only [Option.some.injEq] at h; subst h
            exact ⟨.ite hσ (typed_of_check It hc.1) (typed_of_check Ie hc.2), by simp⟩
          · simp at h
        · simp at h
      | none =>
        simp only [tc] at h; split at h
        · next hw =>
          obtain ⟨σ, hσ⟩ := typed_of_wt Ic hw
          split at h
          · next τ1 ht1 =>
            split at h
            · next hc =>
              simp only [Option.some.injEq] at h; subst h
              exact ⟨.ite hσ (It _ _ ht1).1 (typed_of_check Ie hc), by simp⟩
            · simp at h
          · split at h
            · next τ1 he1 =>
              split at h
              · next hc =>
                simp only [Option.some.injEq] at h; subst h
                exact ⟨.ite hσ (typed_of_check It hc) (Ie _ _ he1).1, by simp⟩
              · simp at h
            · simp at h
        · simp at h
    | forE i it filt body =>
      have Iit := IH it (by simp <;> omega)
      have If := IH filt (by simp <;> omega)
      have Ib := IH body (by simp <;> omega)
      -- the shared part: the slot, the source and the filter
      have common : ∀ te, Γ[i]? = some te →
          ((tc S Γ ρ it (some (.arr te))).isSome &&
            ((tc S Γ ρ filt none).isSome || (tc S Γ ρ filt (some VTy.void)).isSome)) = true →
          Typed S Γ ρ it (.arr te) ∧ ∃ σ, Typed S Γ ρ filt σ := by
        intro te _ hc
        simp only [Bool.and_eq_true] at hc
        exact ⟨typed_of_check Iit hc.1, typed_of_wt If hc.2⟩
      cases m with
      | none =>
        simp only [tc] at h; split at h
        · next te hi =>
          split at h
          · next hc =>
            obtain ⟨hit, σ, hσ⟩ := common te hi hc
            rcases hb : tc S Γ ρ body none with _ | tb
            · simp [hb] at h
            · simp only [hb, Option.map_some, Option.some.injEq] at h; subst h
              exact ⟨.forE hi hit hσ (Ib _ _ hb).1, by simp⟩
          · simp at h
        · simp at h
      | some τ' =>
        cases τ' with
        | arr tb =>
          simp only [tc] at h; split at h
          · next te hi =>
            split at h
            · next hc =>
              obtain ⟨hit, σ, hσ⟩ := common te hi hc
              split at h
              · next hb =>
                simp only [Option.some.injEq] at h; subst h
                exact ⟨.forE hi hit hσ (typed_of_check Ib hb), by simp⟩
              · simp at h
            · simp at h
          · simp at h
        | _ =>
          simp only [tc] at h; split at h
          · split at h <;> simp at h
          · simp at h
    | loop b =>
      simp only [tc] at h; split at h
      · next hw =>
        obtain ⟨σ, hσ⟩ := typed_of_wt (IH b (by simp <;> omega)) hw
        obtain ⟨rfl, hm⟩ := expect_sound h
        exact ⟨.loop hσ, hm⟩
      · simp at h
    | brk =>
      cases m with
      | none => simp [tc] at h
      | some τ' => simp only [tc, Option.some.injEq] at h; subst h; exact ⟨.brk, by simp⟩
    | ret e =>
      cases m with
      | none => simp [tc] at h
      | some τ' =>
        simp only [tc] at h; split at h
        · next hc =>
          simp only [Option.some.injEq] at h; subst h
          exact ⟨.ret (typed_of_check (IH e (by simp <;> omega)) hc), by simp⟩
        · simp at h
    | heap op es =>
      exact tcHeap_sound_of (fun e he => IH e (sizeOf_lt_of_mem_heap he)) h
    | print e =>
      simp only [tc] at h; split at h
      · next hc =>
        obtain ⟨rfl, hm⟩ := expect_sound h
        exact ⟨.print (typed_of_check (IH e (by simp <;> omega)) hc), hm⟩
      · simp at h
    | prim op es =>
      simp only [tc] at h
      exact tcPrim_sound_of (fun e he => IH e (sizeOf_lt_of_mem_args he)) h

/-- **The checker is sound**: whatever `tc` accepts is typed. -/
theorem tc_sound {e : Expr} {m τ} (h : tc S Γ ρ e m = some τ) : Typed S Γ ρ e τ :=
  (tc_sound_aux _ e (Nat.lt_succ_self _) m τ h).1

end

/-! ### Programs -/

mutual
/-- `d` is a default expression of type `t` (`DefaultE a Γ d t`). -/
def checkDefault (a : Nat) (Γ : List VTy) : Expr → VTy → Bool
  | .lit v, t => hasTy [] v t
  | .local i, t => decide (i < a) && decide (Γ[i]? = some t)
  | .prim .mkTup ds, .tup ts => checkDefaultL a Γ ds ts
  | _, _ => false
def checkDefaultL (a : Nat) (Γ : List VTy) : List Expr → List VTy → Bool
  | [], [] => true
  | d :: ds, t :: ts => checkDefault a Γ d t && checkDefaultL a Γ ds ts
  | _, _ => false
end

mutual
theorem checkDefault_sound {a : Nat} {Γ : List VTy} : ∀ (d : Expr) (t : VTy),
    checkDefault a Γ d t = true → DefaultE a Γ d t
  | .lit v, t, h => .lit (by simpa [checkDefault] using h)
  | .local i, t, h => by
    simp only [checkDefault, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .param h.1 h.2
  | .prim op ds, t, h => by
    cases op <;> try (simp [checkDefault] at h; done)
    cases t <;> try (simp [checkDefault] at h; done)
    rename_i ts
    simp only [checkDefault] at h
    exact .tup (checkDefaultL_sound ds ts h)
  | .assign .., _, h | .seq .., _, h | .call .., _, h | .ite .., _, h | .forE .., _, h
  | .loop _, _, h | .brk, _, h | .ret _, _, h | .print _, _, h => by simp [checkDefault] at h
theorem checkDefaultL_sound {a : Nat} {Γ : List VTy} : ∀ (ds : List Expr) (ts : List VTy),
    checkDefaultL a Γ ds ts = true → DefaultEL a Γ ds ts
  | [], [], _ => .nil
  | d :: ds, t :: ts, h => by
    simp only [checkDefaultL, Bool.and_eq_true] at h
    exact .cons (checkDefault_sound d t h.1) (checkDefaultL_sound ds ts h.2)
  | [], _ :: _, h | _ :: _, [], h => by simp [checkDefaultL] at h
end

/-- Recognise the initialisation prefix of slots `k, …` of types `ts`, in a
    function with `a` parameters and slot types `Γ`: the default expressions
    and the rest of the body. -/
def stripPrefix (a : Nat) (Γ : List VTy) (k : Nat) : List VTy → Expr → Option (List Expr × Expr)
  | [], e => some ([], e)
  | t :: ts, e => match e with
    | .seq (.assign i d) rest =>
      if i = k && checkDefault a Γ d t then
        (stripPrefix a Γ (k + 1) ts rest).map fun (ds, b) => (d :: ds, b)
      else none
    | _ => none

theorem stripPrefix_sound {a : Nat} {Γ : List VTy} : ∀ (ts : List VTy) (k : Nat) (e b : Expr) (ds : List Expr),
    stripPrefix a Γ k ts e = some (ds, b) → e = initPrefixE k ds b ∧ DefaultEL a Γ ds ts
  | [], k, e, b, ds, h => by
    simp only [stripPrefix, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, .nil⟩
  | t :: ts, k, e, b, ds, h => by
    simp only [stripPrefix] at h
    split at h
    · next i d rest =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨rfl, hd⟩ := hc
        obtain ⟨⟨ds', b'⟩, hrest, heq⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨hb, hds⟩ := stripPrefix_sound ts (i + 1) rest _ ds' hrest
        exact ⟨by rw [hb]; rfl, .cons (checkDefault_sound d t hd) hds⟩
      · simp at h
    · simp at h

/-- Check one function against its signature and slot types. -/
def checkFn (S : Sigs) (fn : Fn) (ps : List VTy) (τ : VTy) (Γ : List VTy) : Bool :=
  decide (fn.arity = ps.length) && decide (Γ.length = fn.nslots) && decide (Γ.take fn.arity = ps) &&
  match stripPrefix fn.arity Γ fn.arity (Γ.drop fn.arity) fn.body with
  | some (_, b) => (tc S Γ τ b (some τ)).isSome
  | none => false

theorem checkFn_sound {S fn ps τ Γ} (h : checkFn S fn ps τ Γ = true) : FnTyped S fn ps τ Γ := by
  unfold checkFn at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha, hs⟩, hp⟩, hb⟩ := h
  split at hb
  · next ds b hstrip =>
    obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp hb
    have ht := (tc_sound_aux _ b (Nat.lt_succ_self _) _ _ hτ')
    rw [ht.2 τ rfl] at ht
    obtain ⟨hbody, hds⟩ := stripPrefix_sound _ _ _ _ _ hstrip
    exact ⟨ha, hs, hp, b, ds, hbody, hds, ht.1⟩
  · simp at hb

/-- Check a whole program against signatures `S` and slot types `Γs`. -/
def Prog.checkTypes (P : Prog) (S : Sigs) (Γs : List (List VTy)) : Bool :=
  S.classes.all (·.all VTy.closed) &&
  decide (P.fns.length = S.fns.length) &&
  (List.range P.fns.length).all fun f =>
    match P.fns[f]?, S.fns[f]?, Γs[f]? with
    | some fn, some (ps, τ), some Γ => checkFn S fn ps τ Γ
    | _, _, _ => false

/-- **Translation validation for types**: a program that passes
    `checkTypes` is typed, so `Runs.typed` applies to it. -/
theorem Prog.checkTypes_sound {P : Prog} {S : Sigs} {Γs} (h : P.checkTypes S Γs = true) :
    ProgTyped P S := by
  unfold Prog.checkTypes at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨fun t fs hc f hf => h.1.1 fs (List.mem_of_getElem? hc) f hf, h.1.2,
    fun f fn ps τ hf hs => ?_⟩
  have hlt := lt_of_getElem?_some hf
  have := h.2 f hlt
  rw [hf, hs] at this
  split at this
  · next fn' ps' τ' Γ heq1 heq2 heq3 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at heq1 heq2
    obtain ⟨rfl, rfl⟩ := heq2
    subst heq1
    exact ⟨Γ, checkFn_sound this⟩
  · simp at this

end OpenVerse
