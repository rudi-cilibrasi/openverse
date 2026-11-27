/-
  OpenVerse Core — the bounded interpreter on a persistent heap (#780).

  The semantics keeps the heap in an array (`Glob.heap`). A failure context
  holds the state it may roll back to, so the first write or allocation
  inside it copies the whole array: a program that takes N values through
  failure contexts, each allocating, costs about N² on `evalB`.

  `evalP` is `evalB` on a state whose heap is a persistent map from
  addresses to objects, with its size (`PHeap`): a write shares all of the
  map but the path to one entry, so holding the old state costs nothing.
  `evalP_toSt` proves that it gives `evalB`'s results, read through the
  array the map stands for, and `Prog.runB_eq_runP` puts it in `runB`'s
  place in compiled code. The semantics, `eval` and `evalB` are untouched.
-/
import Std.Data.TreeMap
import OpenVerse.Core.Bounded

namespace OpenVerse

/-- A heap as a persistent map: the object at each address below `size`. -/
structure PHeap where
  map : Std.TreeMap Nat Obj
  size : Nat

namespace PHeap

def empty : PHeap := ⟨{}, 0⟩

/-- The object at `a`, as `Array`'s `[a]?`. -/
@[inline] def get? (h : PHeap) (a : Nat) : Option Obj :=
  if a < h.size then some (h.map[a]?.getD default) else none

/-- `Array.push`. -/
@[inline] def push (h : PHeap) (o : Obj) : PHeap := ⟨h.map.insert h.size o, h.size + 1⟩

/-- `Array.setIfInBounds`. -/
@[inline] def set (h : PHeap) (a : Nat) (o : Obj) : PHeap :=
  if a < h.size then ⟨h.map.insert a o, h.size⟩ else h

/-- The array the map stands for. -/
def toArray (h : PHeap) : Array Obj := Array.ofFn (n := h.size) fun i => h.map[i.val]?.getD default

end PHeap

/-- `Glob` with a persistent heap. -/
structure GlobP where
  outRev : List Nat
  heap : PHeap

def GlobP.toGlob (g : GlobP) : Glob := ⟨g.outRev, g.heap.toArray⟩

/-- `St` with a persistent heap. -/
structure StP where
  fr : List Value
  g : GlobP

def StP.toSt (s : StP) : St := ⟨s.fr, s.g.toGlob⟩

/-- `HeapOp.apply` on a persistent heap. -/
def HeapOp.applyP : HeapOp → List Value → GlobP → Res × GlobP
  | .new t, vs, ⟨out, heap⟩ => (.ok (.ref heap.size), ⟨out, heap.push ⟨t, vs⟩⟩)
  | .get k, [.ref a], g => match g.heap.get? a with
    | some o => match o.fields[k]? with
      | some v => (.ok v, g)
      | none => (.err .type, g)
    | none => (.err .type, g)
  | .set k, [.ref a, v], ⟨out, heap⟩ => match heap.get? a with
    | some o =>
      if k < o.fields.length then
        (.ok v, ⟨out, heap.set a { o with fields := o.fields.set k v }⟩)
      else (.err .type, ⟨out, heap⟩)
    | none => (.err .type, ⟨out, heap⟩)
  | .tag, [.ref a], g => match g.heap.get? a with
    | some o => (.ok (.int o.tag), g)
    | none => (.err .type, g)
  | .isTag us, [.ref a], g => match g.heap.get? a with
    | some o => (if us.contains o.tag then .ok (.ref a) else .fail, g)
    | none => (.err .type, g)
  | _, _, g => (.err .type, g)

/-- `St.heapStep`. -/
def StP.heapStep (op : HeapOp) (vs : List Value) : StP → Res × StP
  | ⟨fr, g⟩ => match op.applyP vs g with
    | (r, g') => (r, ⟨fr, g'⟩)

/-- `readSlot`. -/
def readSlotP (s : StP) (i : Nat) : Res :=
  match s.fr[i]? with
  | some v => .ok v
  | none => .err .slot

/-- `writeSlot`. -/
def writeSlotP (s : StP) (i : Nat) (v : Value) : Option StP :=
  if i < s.fr.length then some { s with fr := s.fr.set i v } else none

mutual
/-- `evalB` on a state with a persistent heap. -/
def evalP (P : Prog) : Nat → Nat → StP → Expr → Bounded (Res × StP)
  | 0, _, _, _ => .fuel
  | _+1, 0, _, _ => .deep
  | _+1, _+1, s, .lit v => .res (.ok v, s)
  | _+1, _+1, s, .local i => .res (readSlotP s i, s)
  | n+1, d+1, s, .assign i e => bindRB (evalP P n d s e) fun v s₁ =>
      match writeSlotP s₁ i v with
      | some s₂ => .res (.ok v, s₂)
      | none => .res (.err .slot, s₁)
  | n+1, d+1, s, .seq a b => bindRB (evalP P n d s a) fun _ s₁ => evalP P n (d+1) s₁ b
  | n+1, d+1, s, .prim op es => bindLB (evalListP P n d s es) fun vs s₁ =>
      if n < op.cost vs then .fuel else .res (op.apply vs, s₁)
  | n+1, d+1, s, .heap op es => bindLB (evalListP P n d s es) fun vs s₁ =>
      .res (StP.heapStep op vs s₁)
  | n+1, d+1, s, .call f es => bindLB (evalListP P n d s es) fun vs s₁ =>
      match P.callable f vs.length with
      | none => .res (.err .call, s₁)
      | some fn => (evalP P n d ⟨frameOf fn vs, s₁.g⟩ fn.body).bind fun
        | none => .fuel
        | some (r, s₂) => .res (retOf r, ⟨s₁.fr, s₂.g⟩)
  | n+1, d+1, s, .ite c t e => (evalP P n d s c).bind fun
      | none => .fuel
      | some (.ok _, s₁) => evalP P n (d+1) s₁ t
      | some (.fail, _) => evalP P n (d+1) s e
      | some (.brk, s₁) => .res (.brk, s₁)
      | some (.ret v, s₁) => .res (.ret v, s₁)
      | some (.err k, s₁) => .res (.err k, s₁)
  | n+1, d+1, s, .forE i it filt body => bindRB (evalP P n d s it) fun v s₁ =>
      match v with
      | .arr vs => evalForP P n d i filt body s₁ vs.toList []
      | .int _ | .logic _ | .char _ | .float _ | .tup _ | .none | .some _ | .ref _ => .res (.err .type, s₁)
  | n+1, d+1, s, .loop b => (evalP P n d s b).bind fun
      | none => .fuel
      | some (.ok _, s₁) => evalP P n (d+1) s₁ (.loop b)
      | some (.brk, s₁) => .res (.ok .void, s₁)
      | some (.fail, s₁) => .res (.fail, s₁)
      | some (.ret v, s₁) => .res (.ret v, s₁)
      | some (.err k, s₁) => .res (.err k, s₁)
  | _+1, _+1, s, .brk => .res (.brk, s)
  | n+1, d+1, s, .ret e => bindRB (evalP P n d s e) fun v s₁ => .res (.ret v, s₁)
  | n+1, d+1, s, .print e => bindRB (evalP P n d s e) fun v s₁ =>
      match printBytes v with
      | some bs => .res (.ok .void, { s₁ with g := { s₁.g with outRev := bs.reverse ++ s₁.g.outRev } })
      | none => .res (.err .type, s₁)

/-- `evalListB` on a state with a persistent heap. -/
def evalListP (P : Prog) : Nat → Nat → StP → List Expr → Bounded (LRes × StP)
  | 0, _, _, _ => .fuel
  | _+1, 0, _, _ => .deep
  | _+1, _+1, s, [] => .res (.ok [], s)
  | n+1, d+1, s, e :: es => (evalP P n d s e).bind fun
    | none => .fuel
    | some (.ok v, s₁) => (evalListP P n d s₁ es).bind fun
      | none => .fuel
      | some (.ok vs, s₂) => .res (.ok (v :: vs), s₂)
      | some (.stop r, s₂) => .res (.stop r, s₂)
    | some (.fail, s₁) => .res (.stop .fail, s₁)
    | some (.brk, s₁) => .res (.stop .brk, s₁)
    | some (.ret v, s₁) => .res (.stop (.ret v), s₁)
    | some (.err k, s₁) => .res (.stop (.err k), s₁)

/-- `evalForB` on a state with a persistent heap. -/
def evalForP (P : Prog) : Nat → Nat → Nat → Expr → Expr → StP → List Value → List Value →
    Bounded (Res × StP)
  | 0, _, _, _, _, _, _, _ => .fuel
  | _+1, 0, _, _, _, _, _, _ => .deep
  | _+1, _+1, _, _, _, s, [], acc => .res (.ok (Value.ofArray acc.reverse.toArray), s)
  | n+1, d+1, i, filt, body, s, v :: vs, acc => match writeSlotP s i v with
    | none => .res (.err .slot, s)
    | some s₀ => (evalP P n d s₀ filt).bind fun
      | none => .fuel
      | some (.fail, _) => evalForP P n (d+1) i filt body s₀ vs acc
      | some (.ok _, s₁) => (evalP P n d s₁ body).bind fun
        | none => .fuel
        | some (.ok w, s₂) => evalForP P n (d+1) i filt body s₂ vs (w :: acc)
        | some (.fail, s₂) => .res (.fail, s₂)
        | some (.brk, s₂) => .res (.brk, s₂)
        | some (.ret v, s₂) => .res (.ret v, s₂)
        | some (.err k, s₂) => .res (.err k, s₂)
      | some (.brk, s₁) => .res (.brk, s₁)
      | some (.ret v, s₁) => .res (.ret v, s₁)
      | some (.err k, s₁) => .res (.err k, s₁)
end


/-! ### `evalP` gives `evalB`'s results -/

namespace PHeap

@[simp] theorem toArray_size (h : PHeap) : h.toArray.size = h.size := by simp [toArray]

theorem toArray_getElem? (h : PHeap) (a : Nat) : h.toArray[a]? = h.get? a := by
  unfold toArray get?
  by_cases ha : a < h.size
  · simp [ha]
  · simp [ha]

@[simp] theorem toArray_empty : PHeap.empty.toArray = #[] := by simp [toArray, empty]

theorem toArray_push (h : PHeap) (o : Obj) : (h.push o).toArray = h.toArray.push o := by
  apply Array.ext_getElem?
  intro i
  rw [toArray_getElem?, Array.getElem?_push, toArray_getElem?, toArray_size]
  unfold get? push
  simp only [Std.TreeMap.getElem?_insert]
  by_cases h1 : i = h.size
  · subst h1; simp
  · by_cases h2 : i < h.size
    · have : compare h.size i ≠ .eq := by simp [Nat.compare_eq_eq]; omega
      simp [h1, h2, this]; omega
    · simp [h1, h2]; omega

theorem toArray_set (h : PHeap) (a : Nat) (o : Obj) :
    (h.set a o).toArray = h.toArray.setIfInBounds a o := by
  apply Array.ext_getElem?
  intro i
  rw [toArray_getElem?, Array.getElem?_setIfInBounds, toArray_getElem?, toArray_size]
  unfold set
  by_cases ha : a < h.size
  · simp only [ha, if_true]
    unfold get?
    simp only [Std.TreeMap.getElem?_insert]
    by_cases h1 : a = i
    · subst h1; simp [ha]
    · have : compare a i ≠ .eq := by simp [Nat.compare_eq_eq]; exact h1
      simp [h1, this]
  · simp only [ha, if_false]
    by_cases h1 : a = i
    · subst h1; simp [get?, ha]
    · simp [h1]

end PHeap

theorem HeapOp.applyP_toGlob (op : HeapOp) (vs : List Value) (g : GlobP) :
    ((op.applyP vs g).1, (op.applyP vs g).2.toGlob) = op.apply vs g.toGlob := by
  rcases g with ⟨out, heap⟩
  cases op with
  | new t => simp [HeapOp.applyP, HeapOp.apply, GlobP.toGlob, PHeap.toArray_push]
  | get k =>
    match vs with
    | [.ref a] =>
      simp only [HeapOp.applyP, HeapOp.apply, GlobP.toGlob, PHeap.toArray_getElem?]
      cases heap.get? a with
      | none => rfl
      | some o => simp only []; cases o.fields[k]? <;> rfl
    | [] | [.int _] | [.logic _] | [.char _] | [.float _] | [.arr _] | [.tup _] | [.none] | [.some _]
    | _ :: _ :: _ => simp [HeapOp.applyP, HeapOp.apply, GlobP.toGlob]
  | set k =>
    match vs with
    | [.ref a, v] =>
      simp only [HeapOp.applyP, HeapOp.apply, GlobP.toGlob, PHeap.toArray_getElem?]
      cases heap.get? a with
      | none => rfl
      | some o =>
        simp only []
        by_cases hk : k < o.fields.length <;> simp [hk, PHeap.toArray_set]
    | [] | [_] | _ :: _ :: _ :: _
    | [.int _, _] | [.logic _, _] | [.char _, _] | [.float _, _] | [.arr _, _] | [.tup _, _] | [.none, _]
    | [.some _, _] => simp [HeapOp.applyP, HeapOp.apply, GlobP.toGlob]
  | tag =>
    match vs with
    | [.ref a] =>
      simp only [HeapOp.applyP, HeapOp.apply, GlobP.toGlob, PHeap.toArray_getElem?]
      cases heap.get? a <;> rfl
    | [] | [.int _] | [.logic _] | [.char _] | [.float _] | [.arr _] | [.tup _] | [.none] | [.some _]
    | _ :: _ :: _ => simp [HeapOp.applyP, HeapOp.apply, GlobP.toGlob]
  | isTag us =>
    match vs with
    | [.ref a] =>
      simp only [HeapOp.applyP, HeapOp.apply, GlobP.toGlob, PHeap.toArray_getElem?]
      cases heap.get? a <;> rfl
    | [] | [.int _] | [.logic _] | [.char _] | [.float _] | [.arr _] | [.tup _] | [.none] | [.some _]
    | _ :: _ :: _ => simp [HeapOp.applyP, HeapOp.apply, GlobP.toGlob]

theorem StP.heapStep_toSt (op : HeapOp) (vs : List Value) (s : StP) :
    ((s.heapStep op vs).1, (s.heapStep op vs).2.toSt) = St.heapStep op vs s.toSt := by
  rcases s with ⟨fr, g⟩
  have h := HeapOp.applyP_toGlob op vs g
  simp only [StP.heapStep, St.heapStep, StP.toSt]
  rw [← h]

theorem readSlotP_toSt (s : StP) (i : Nat) : readSlotP s i = readSlot s.toSt i := rfl

theorem writeSlotP_toSt (s : StP) (i : Nat) (v : Value) :
    (writeSlotP s i v).map StP.toSt = writeSlot s.toSt i v := by
  unfold writeSlotP writeSlot
  by_cases h : i < s.fr.length <;> simp [h, StP.toSt]

/-- A bounded result with a function applied to its value. -/
def Bounded.map {α β : Type} (f : α → β) : Bounded α → Bounded β
  | .fuel => .fuel
  | .res a => .res (f a)
  | .deep => .deep

/-- An outcome and state, the state read through its heap's array. -/
def StP.tr {ρ : Type} (p : ρ × StP) : ρ × St := (p.1, p.2.toSt)

theorem bindRB_tr {x : Bounded (Res × StP)} {k : Value → StP → Bounded (Res × StP)}
    {k' : Value → St → Bounded (Res × St)} (hk : ∀ v s, (k v s).map StP.tr = k' v s.toSt) :
    (bindRB x k).map StP.tr = bindRB (x.map StP.tr) k' := by
  cases x with
  | fuel => rfl
  | deep => rfl
  | res z =>
    rcases z with ⟨r, s⟩
    cases r <;> first | exact hk _ _ | rfl

theorem bindLB_tr {x : Bounded (LRes × StP)} {k : List Value → StP → Bounded (Res × StP)}
    {k' : List Value → St → Bounded (Res × St)} (hk : ∀ vs s, (k vs s).map StP.tr = k' vs s.toSt) :
    (bindLB x k).map StP.tr = bindLB (x.map StP.tr) k' := by
  cases x with
  | fuel => rfl
  | deep => rfl
  | res z =>
    rcases z with ⟨r, s⟩
    cases r <;> first | exact hk _ _ | rfl

theorem Bounded.bind_tr {α β α' β' : Type} {f : α → α'} {g : β → β'} {x : Bounded α}
    {k : Option α → Bounded β} {k' : Option α' → Bounded β'}
    (hk : ∀ z, (k z).map g = k' (z.map f)) : (x.bind k).map g = (x.map f).bind k' := by
  cases x with
  | fuel => exact hk none
  | deep => rfl
  | res a => exact hk (some a)

/-- Close a goal about results that the hypotheses of a `split` settle. -/
macro "tr_leaf" : tactic =>
  `(tactic| first | rfl | (simp_all [Bounded.map, StP.tr, StP.toSt, GlobP.toGlob]; done))

/-- **`evalP` is `evalB`**: on a state with a persistent heap it gives
    `evalB`'s outcome, and `evalB`'s state when its heap is read as an array. -/
theorem evalP_toSt (P : Prog) : ∀ n,
    (∀ d s e, (evalP P n d s e).map StP.tr = evalB P n d s.toSt e) ∧
    (∀ d s es, (evalListP P n d s es).map StP.tr = evalListB P n d s.toSt es) ∧
    (∀ d i filt body s vs acc,
      (evalForP P n d i filt body s vs acc).map StP.tr = evalForB P n d i filt body s.toSt vs acc)
  | 0 => ⟨fun _ _ _ => by simp only [evalP, evalB]; rfl,
      fun _ _ _ => by simp only [evalListP, evalListB]; rfl,
      fun _ _ _ _ _ _ _ => by simp only [evalForP, evalForB]; rfl⟩
  | n+1 => by
    obtain ⟨ihE, ihL, ihF⟩ := evalP_toSt P n
    refine ⟨fun d s e => ?_, fun d s es => ?_, fun d i filt body s vs acc => ?_⟩
    · cases d with
      | zero => simp only [evalP, evalB]; rfl
      | succ d =>
        cases e with
        | lit v => simp only [evalP, evalB]; rfl
        | «local» i => simp only [evalP, evalB]; rfl
        | assign i e =>
          simp only [evalP, evalB]
          rw [← ihE]
          refine bindRB_tr fun v s₁ => ?_
          rw [← writeSlotP_toSt]
          cases writeSlotP s₁ i v <;> rfl
        | seq a b =>
          simp only [evalP, evalB]
          rw [← ihE]
          exact bindRB_tr fun _ s₁ => ihE (d+1) s₁ b
        | prim op es =>
          simp only [evalP, evalB]
          rw [← ihL]
          refine bindLB_tr fun vs s₁ => ?_
          split <;> rfl
        | heap op es =>
          simp only [evalP, evalB]
          rw [← ihL]
          refine bindLB_tr fun vs s₁ => ?_
          rw [← StP.heapStep_toSt]; rfl
        | call f es =>
          simp only [evalP, evalB]
          rw [← ihL]
          refine bindLB_tr fun vs s₁ => ?_
          cases P.callable f vs.length with
          | none => rfl
          | some fn =>
            simp only []
            have h := ihE d ⟨frameOf fn vs, s₁.g⟩ fn.body
            simp only [StP.toSt] at h ⊢
            rw [← h]
            refine Bounded.bind_tr (f := StP.tr) fun z => ?_
            rcases z with _ | ⟨r, s₂⟩ <;> rfl
        | ite c t e =>
          simp only [evalP, evalB]
          rw [← ihE]
          refine Bounded.bind_tr (f := StP.tr) fun z => ?_
          rcases z with _ | ⟨r, s₁⟩
          · rfl
          · cases r <;> first | exact ihE (d+1) _ _ | rfl
        | forE i it filt body =>
          simp only [evalP, evalB]
          rw [← ihE]
          refine bindRB_tr fun v s₁ => ?_
          cases v <;> first | exact ihF d i filt body s₁ _ _ | rfl
        | loop b =>
          simp only [evalP, evalB]
          rw [← ihE]
          refine Bounded.bind_tr (f := StP.tr) fun z => ?_
          rcases z with _ | ⟨r, s₁⟩
          · rfl
          · cases r <;> first | exact ihE (d+1) _ _ | rfl
        | brk => simp only [evalP, evalB]; rfl
        | ret e =>
          simp only [evalP, evalB]
          rw [← ihE]
          exact bindRB_tr fun v s₁ => rfl
        | print e =>
          simp only [evalP, evalB]
          rw [← ihE]
          refine bindRB_tr fun v s₁ => ?_
          cases printBytes v <;> rfl
    · cases d with
      | zero => simp only [evalListP, evalListB]; rfl
      | succ d =>
        cases es with
        | nil => simp only [evalListP, evalListB]; rfl
        | cons e es =>
          simp only [evalListP, evalListB]
          rw [← ihE]
          refine Bounded.bind_tr (f := StP.tr) fun z => ?_
          rcases z with _ | ⟨r, s₁⟩
          · rfl
          · cases r with
            | ok v =>
              simp only [Option.map, StP.tr]
              rw [← ihL]
              refine Bounded.bind_tr (f := StP.tr) fun z => ?_
              rcases z with _ | ⟨r, s₂⟩
              · rfl
              · cases r <;> rfl
            | _ => rfl
    · cases d with
      | zero => simp only [evalForP, evalForB]; rfl
      | succ d =>
        cases vs with
        | nil => simp only [evalForP, evalForB]; rfl
        | cons v vs =>
          simp only [evalForP, evalForB]
          rw [← writeSlotP_toSt]
          cases writeSlotP s i v with
          | none => rfl
          | some s₀ =>
            simp only [Option.map]
            rw [← ihE]
            refine Bounded.bind_tr (f := StP.tr) fun z => ?_
            rcases z with _ | ⟨r, s₁⟩
            · rfl
            · cases r with
              | fail => exact ihF (d+1) i filt body s₀ vs acc
              | ok w =>
                simp only [Option.map, StP.tr]
                rw [← ihE]
                refine Bounded.bind_tr (f := StP.tr) fun z => ?_
                rcases z with _ | ⟨r, s₂⟩
                · rfl
                · cases r <;> first | exact ihF (d+1) i filt body s₂ vs _ | rfl
              | _ => rfl

/-- `Prog.runB` on a persistent heap. -/
def Prog.runP (P : Prog) (n d : Nat) : Bounded (Res × List Nat) :=
  match evalP P n d ⟨[], ⟨[], PHeap.empty⟩⟩ (.call P.main []) with
  | .fuel => .fuel
  | .res (r, s) => .res (r, s.g.outRev.reverse)
  | .deep => .deep

/-- **The runner on a persistent heap is the runner**: compiled code runs
    `Prog.runP` wherever `Prog.runB` is written. -/
@[csimp] theorem Prog.runB_eq_runP : @Prog.runB = @Prog.runP := by
  funext P n d
  have h := (evalP_toSt P n).1 d ⟨[], ⟨[], PHeap.empty⟩⟩ (.call P.main [])
  have h0 : (⟨[], ⟨[], PHeap.empty⟩⟩ : StP).toSt = Prog.initSt := by
    simp [StP.toSt, GlobP.toGlob, Prog.initSt]
  rw [h0] at h
  unfold Prog.runB Prog.runP
  rw [← h]
  cases evalP P n d ⟨[], ⟨[], PHeap.empty⟩⟩ (.call P.main []) with
  | fuel => rfl
  | deep => rfl
  | res z => rfl

end OpenVerse
