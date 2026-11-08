/-
  OpenVerse front end — lowering `<suspends>` functions to Verse Core (#156).

  Verse Core has no suspension, so the front end compiles each `<suspends>`
  function `g` into a *frame* class and three ordinary functions:

  - `g$new(params…)` allocates a frame holding the arguments;
  - `g$init(frame, params…)` resets a frame for another call (a call site
    keeps its callee's frame, so a loop of calls allocates once);
  - `g$resume(frame, sched, params…)` runs `g`'s body from the suspension
    point the frame records to the next one (result 0: pending) or to the
    end (result 1: done; the value is in the frame's `?result` field). The
    parameters are passed again only so that the slots' initial values
    (`DefaultE`) can still refer to them.

  This file is the Core-to-Core pass that turns `g`'s elaborated body into
  `g$resume`'s:
  1. its slots move up by two (slot 0 is the frame, slot 1 the scheduler),
     and `return e` stores `e` in the frame and returns 1;
  2. each call of a suspends function becomes a statement of its own: the
     values computed before it in the same expression go to temporaries
     first (A-normal form), typed by the Core checker;
  3. the statements are guarded so that a resumption skips to the
     suspension point it left from: a flag `R` is set while seeking it, and
     a statement that cannot contain it is skipped while `R` is set. `if`
     picks the branch holding it instead of testing its condition; `loop`s
     stay loops; a `for` whose body suspends becomes a `loop` over an index.
  At each suspension point, a pending callee makes the function store all
  its slots in the frame and return 0; resuming reloads them.

  `sync` and `race` (marked by calls of `$syncMark` / `$raceMark` on the
  array of their arms) are suspension points whose arms become functions of
  their own over the same frame (each with its program counter and a done
  flag in the frame): the enclosing code resumes them in order, storing its
  slots before and reloading them after. A `race`'s winner cancels the arms
  that started and are pending. Each region (the body, or an arm) also gets
  a cancel function, which cancels the callee or the arms at its current
  suspension point, then runs the `defer:` blocks active there (which the
  elaborator records in a branch that never runs, `withDeferMark`).

  Failure contexts never contain a suspension (`<suspends>` excludes
  `<decides>`, and the elaborator rejects a suspending call in a condition
  or filter), so rollback never spans a resumption. Since the result is
  ordinary Verse Core, `Prog.checkTypes` checks it like any other code.
-/
import OpenVerse.Core.TypeCheck

namespace OpenVerse.Front.Suspend
open OpenVerse

/-- What a call of a suspends function needs of it: its frame class and
    functions. -/
structure Callee where
  tag : Nat
  newFn : Nat
  initFn : Nat
  resumeFn : Nat
  /-- Unwinds a frame (none: nothing to do, as for `Sleep`). -/
  cancelFn : Option Nat
  /-- The frame fields `resume` and `cancel` take after the frame and the
      scheduler. -/
  passFields : List Nat
  /-- The frame's result field; none when the call's value is `void`. -/
  resField : Option Nat
  /-- A generic callee's frame has type arguments: it is kept in an option
      field, unwrapped (and resumed) in a condition. Another's is kept in a
      field of type `ref [tag, sched] []`, first the scheduler, and resumed
      by a test of its class (`Typed.dispatch`), outside any condition. -/
  generic : Bool := false
  /-- `new` takes the scheduler first (to fill its frame's child fields). -/
  newSched : Bool := false
  /-- A non-generic callee's result getter, `g$result(frame)`. -/
  resultFn : Option Nat := none
  deriving Inhabited

/-- Slots of a resume function: the frame, the scheduler. -/
def frS : Nat := 0
def schS : Nat := 1

/-- Frame fields: the suspension point the body is at (0: not started), the
    result, one field per suspension point (a callee's `?frame`), two per arm
    of a `sync` or `race` (its suspension point, whether it is done), then
    the slots. -/
def pcF : Nat := 0
def resF : Nat := 1
def childF (k : Nat) : Nat := 2 + (k - 1)
def armPcF (sites a : Nat) : Nat := 2 + sites + 2 * a
def armDoneF (sites a : Nat) : Nat := 2 + sites + 2 * a + 1
def slotBaseOf (sites arms : Nat) : Nat := 2 + sites + 2 * arms

/-- Placeholders for "store every slot in the frame" and "reload every slot
    from it", filled in once the number of slots is known. -/
def spillMark : Expr := .heap (.get 1000000007) []
def reloadMark : Expr := .heap (.get 1000000009) []
/-- "Stop the function's branches", filled in once they are known. -/
def killMark : Expr := .heap (.get 1000000011) []

def int (i : Int) : Expr := .lit (.int i)
def vd : Expr := .lit .void
def fr : Expr := .local frS
def fget (f : Nat) : Expr := .heap (.get f) [fr]
def fset (f : Nat) (v : Expr) : Expr := .heap (.set f) [fr, v]

/-- Statements in sequence, of type `void`. -/
def seqVoid (ss : List Expr) : Expr := ss.foldr .seq vd

/-- A condition that holds when every one of `cs` does. -/
def allOf : List Expr → Expr
  | [] => vd
  | [c] => c
  | c :: cs => .seq c (allOf cs)

/-- `e` with its slots moved up by `d`. -/
partial def shift (d : Nat) : Expr → Expr
  | .local i => .local (i + d)
  | .assign i e => .assign (i + d) (shift d e)
  | .forE i it f b => .forE (i + d) (shift d it) (shift d f) (shift d b)
  | .seq a b => .seq (shift d a) (shift d b)
  | .prim p es => .prim p (es.map (shift d))
  | .call f es => .call f (es.map (shift d))
  | .heap op es => .heap op (es.map (shift d))
  | .ite c t e => .ite (shift d c) (shift d t) (shift d e)
  | .loop b => .loop (shift d b)
  | .ret e => .ret (shift d e)
  | .print e => .print (shift d e)
  | e => e

/-- `return e` as: store `e` as the result, return 1 (done). -/
partial def retToDone : Expr → Expr
  | .ret e => .seq (fset resF (retToDone e)) (.seq killMark (.ret (int 1)))
  | .assign i e => .assign i (retToDone e)
  | .forE i it f b => .forE i (retToDone it) (retToDone f) (retToDone b)
  | .seq a b => .seq (retToDone a) (retToDone b)
  | .prim p es => .prim p (es.map retToDone)
  | .call f es => .call f (es.map retToDone)
  | .heap op es => .heap op (es.map retToDone)
  | .ite c t e => .ite (retToDone c) (retToDone t) (retToDone e)
  | .loop b => .loop (retToDone b)
  | .print e => .print (retToDone e)
  | e => e

/-- Whether `e` contains a suspension point (a call of a function that
    `isS` holds of). -/
partial def hasSusp (isS : Nat → Bool) : Expr → Bool
  | .call f es => isS f || es.any (hasSusp isS)
  | .assign _ e | .ret e | .print e | .loop e => hasSusp isS e
  | .seq a b => hasSusp isS a || hasSusp isS b
  | .prim _ es | .heap _ es => es.any (hasSusp isS)
  | .ite c t e => hasSusp isS c || hasSusp isS t || hasSusp isS e
  | .forE _ it f b => hasSusp isS it || hasSusp isS f || hasSusp isS b
  | _ => false

/-- The number of suspension points in `e`; `own`: not counting those in
    the arms of a `sync` or `race` (a mark `m`). -/
partial def countSusp (isS : Nat → Bool) (m : Nat → Bool := fun _ => false) (own : Bool := false)
    (sk : Nat → Bool := fun _ => false) : Expr → Nat
  | .call f es =>
    if sk f then 0 else
    (if isS f then 1 else 0) + (if own && m f then 0 else (es.map (countSusp isS m own sk)).sum)
  | .assign _ e | .ret e | .print e | .loop e => countSusp isS m own sk e
  | .seq a b => countSusp isS m own sk a + countSusp isS m own sk b
  | .prim _ es | .heap _ es => (es.map (countSusp isS m own sk)).sum
  | .ite c t e => countSusp isS m own sk c + countSusp isS m own sk t + countSusp isS m own sk e
  | .forE _ it f b => countSusp isS m own sk it + countSusp isS m own sk f + countSusp isS m own sk b
  | _ => 0

/-- The `spawn`s (calls of the mark `m` on `array{F(…), T}`) in `e`, in the
    order the lowering meets them: the callee, its arguments, `T`'s slot. -/
partial def spawnSites (m : Nat) : Expr → List (Nat × List Expr × Nat)
  | .call f es =>
    match f == m, es with
    | true, [.prim .mkArr [.seq (.call g gs) _, .seq (.local t) _]] => [(g, gs, t)]
    | _, _ => (es.map (spawnSites m)).flatten
  | .assign _ e | .ret e | .print e | .loop e => spawnSites m e
  | .seq a b => spawnSites m a ++ spawnSites m b
  | .prim _ es | .heap _ es => (es.map (spawnSites m)).flatten
  | .ite c t e => spawnSites m c ++ spawnSites m t ++ spawnSites m e
  | .forE _ it f b => spawnSites m it ++ spawnSites m f ++ spawnSites m b
  | _ => []

/-- The number of arms of the `sync`s and `race`s (marks `m`) in `e`. -/
partial def countArms (m : Nat → Bool) : Expr → Nat
  | .call f es =>
    (match f, es with
      | f, [.prim .mkArr arms] => if m f then arms.length else 0
      | _, _ => 0) + (es.map (countArms m)).sum
  | .assign _ e | .ret e | .print e | .loop e => countArms m e
  | .seq a b => countArms m a + countArms m b
  | .prim _ es | .heap _ es => (es.map (countArms m)).sum
  | .ite c t e => countArms m c + countArms m t + countArms m e
  | .forE _ it f b => countArms m it + countArms m f + countArms m b
  | _ => 0

/-- Split `k` slot initialisations off the front of a function body
    (`initPrefixE`). -/
def stripInits : Nat → Expr → Option (List Expr × Expr)
  | 0, e => some ([], e)
  | k + 1, .seq (.assign _ d) rest => (stripInits k rest).map fun (ds, b) => (d :: ds, b)
  | _, _ => none

/-- An initial value of type `τ` in a function whose parameters have types
    `params` (`DefaultE`): a parameter of a subtype, a default literal, a
    prototype, a new object built from such values, or a tuple of them. -/
partial def coreDefault (S : Sigs) (params : List VTy) (depth : Nat) (τ : VTy) : Option Expr :=
  if depth > 12 then none else
  match params.findIdx? (fun p => p.sub τ) with
  | some i => some (.local i)
  | none =>
    match τ with
    | .int | .logic | .char | .float | .arr _ | .opt _ => some (.lit τ.default)
    | .tup ts => (ts.mapM (coreDefault S params (depth + 1))).map (.prim .mkTup ·)
    | .var _ => none
    | .ref ts args =>
      match (S.protos.zipIdx.find? fun ((t, a), _) => ts.contains t && decide (a = args)) with
      | some (_, addr) => some (.lit (.ref addr))
      | none => ts.findSome? fun t => do
          let fs ← S.classes[t]?
          if !VTy.pinsOK (S.pinsOf t) args then none
          let ds ← (fs.map (VTy.inst args)).mapM (coreDefault S params (depth + 1))
          some (.heap (.new t) ds)

/-- What a suspension point waits for, for cancelling it. -/
inductive Waits where
  /-- A callee's frame (for a non-generic callee: the slot its frame is read
      into, and the slots holding its arguments). -/
  | callee (k : Nat) (c : Callee) (y : Nat) (as : List Nat)
  /-- The arms of a `sync` or `race`: each one's resume and cancel functions
      and its two fields. -/
  | arms (as : List (Nat × Nat × Nat × Nat))

structure Site where
  id : Nat
  waits : Waits
  /-- The `defer:` blocks active there, last registered first. -/
  defers : Expr

structure Env where
  /-- The signatures, for inferring types: each suspends function's own,
      and its `new` and `init`. -/
  S : Sigs
  /-- The function's result type. -/
  ρ : VTy
  callee : Nat → Option Callee
  syncMark : Nat
  raceMark : Nat
  rushMark : Nat
  /-- The function's parameters (slots 2 …), passed on to its arms. -/
  arity : Nat
  /-- Suspension points and arms in the whole function. -/
  sites : Nat
  armsTotal : Nat
  /-- The index of the function's first arm function. -/
  fnBase : Nat
  /-- The scheduler's class. -/
  schedTag : Nat
  /-- The `spawn` mark, and for each `spawn` in the function, in order, its
      root's `new` and `start` functions. -/
  spawnMark : Nat
  spawns : Array (Nat × Nat)
  /-- The `branch` mark, and for each `branch` in the function, in order,
      its wrapper's `start` and `stop` functions and class. -/
  branchMark : Nat
  branches : Array (Nat × Nat × Nat)
  /-- The region being lowered: the field of its suspension point, the flag
      set while seeking it, and its own suspension points. -/
  pcFld : Nat
  rS : Nat
  regionTotal : Nat

structure St where
  /-- The functions' slot types (shared by the body and its arms). -/
  Γ : Array VTy
  /-- Which slots are transient: used only within one resumption (so real
      slots), not kept in the frame. -/
  trans : Array Bool := #[]
  /-- Suspension points numbered so far, in order (from 1). -/
  next : Nat := 0
  /-- The region's own suspension points so far. -/
  regionNext : Nat := 0
  /-- Each suspension point's field type. -/
  children : Array VTy := #[]
  /-- Arms numbered so far, and their (resume, cancel) bodies. -/
  armsNext : Nat := 0
  arms : Array (Expr × Expr) := #[]
  /-- The region's suspension points, for its cancel function. -/
  sites : Array Site := #[]
  /-- The `defer:` blocks active at the suspension points being lowered. -/
  defers : Expr := vd
  /-- `spawn`s met so far. -/
  spawnNext : Nat := 0
  /-- `branch`es met so far; for each, what stopping it needs (its wrapper's
      field, class, `stop` function, a slot to read the wrapper into, the
      arm's fields and cancel function) and what its trampoline needs (the
      arm's resume function and done field). -/
  branchNext : Nat := 0
  kills : Array (Nat × Nat × Nat × Nat × Nat × Nat × Nat) := #[]
  /-- By the order the `branch`es (and `rush` arms) are numbered in: each
      one's arm resume function, done field, and whether its wrapper runs
      it at once (a `branch`) or only registers it (a `rush` loser). -/
  branchArms : Array (Nat × Nat × Bool) := #[]

abbrev M := ReaderT Env (StateT St (Except String))

/-- A new slot whose value is kept across suspension points (in the frame). -/
def fresh (τ : VTy) : M Nat :=
  modifyGet fun st => (st.Γ.size, { st with Γ := st.Γ.push τ, trans := st.trans.push false })

/-- A new slot used only within one resumption. -/
def freshT (τ : VTy) : M Nat :=
  modifyGet fun st => (st.Γ.size, { st with Γ := st.Γ.push τ, trans := st.trans.push true })

def infer (e : Expr) : M VTy := do
  let env ← read
  match tc env.S (← get).Γ.toList env.ρ e none with
  | some τ => pure τ
  | none => throw "internal error: lowering a <suspends> function: cannot infer the type of a value kept across a suspension point"

def isMark (env : Env) (f : Nat) : Bool := f == env.syncMark || f == env.raceMark || f == env.rushMark

def hasS (e : Expr) : M Bool := do
  let env ← read
  return hasSusp (fun f => (env.callee f).isSome || isMark env f || f == env.spawnMark || f == env.branchMark) e

/-- The region's suspension point, `lo ≤ pc ≤ hi`, as a condition. -/
def inRange (lo hi : Nat) : M Expr := do
  let pc := fget (← read).pcFld
  return .seq (.prim .le [int lo, pc]) (.prim .le [pc, int hi])

def seeking : M Expr := do return .prim .eq [.local (← read).rS, int 1]

/-- Run `prod`, a statement, and guard it so that it is skipped while
    seeking a suspension point outside it. No guard is needed when none of
    the region's suspension points follows it. -/
def emitWith (prod : M (Expr × α)) : M (Expr × α) := do
  let lo := (← get).next + 1
  let (s, x) ← prod
  let hi := (← get).next
  let env ← read
  if (← get).regionNext < env.regionTotal then
    let sk ← seeking
    let ir ← inRange lo hi
    let run : Expr :=
      if lo ≤ hi then .ite sk (.ite ir (int 1) (int 0)) (int 1)
      else .ite sk (int 0) (int 1)
    return (.ite (.prim .eq [run, int 1]) (.seq s vd) vd, x)
  else return (.seq s vd, x)

def emit (prod : M Expr) : M Expr :=
  return (← emitWith (do return ((← prod), ()))).1

def app (k : Option (Expr → Expr)) (e : Expr) : Expr :=
  match k with
  | some k => k e
  | none => e

/-- Literals and the frame and scheduler slots: the same when evaluated
    again, so never moved to a temporary. -/
def stable : Expr → Bool
  | .lit _ => true
  | .local i => i == frS || i == schS
  | _ => false

/-- A new suspension point of the region. -/
def newSite (fieldTy : VTy) : M Nat := do
  let k := (← get).next + 1
  modify fun st => { st with next := k, regionNext := st.regionNext + 1,
                             children := st.children.push fieldTy }
  return k

/-- The arguments of the function's arm functions: the frame, the
    scheduler, the parameters. -/
def armArgs : M (List Expr) := do
  return [fr, .local schS] ++ (List.range (← read).arity).map fun i => .local (i + 2)

mutual
/-- The statements of `e`, each guarded, with the continuation `k` applied
    to its value (none: the value is discarded). -/
partial def block (e : Expr) (k : Option (Expr → Expr)) : M (List Expr) := do
  -- (`return` becomes "store the result, give 1" only here, as the user's
  -- code is emitted: inference sees the code as written)
  if !(← hasS e) then return [← emit (pure (app k (retToDone e)))]
  match e with
  -- the defers active at the suspension points of `b` (`withDeferMark`)
  | .seq (.ite (.prim .fail []) d (.lit .void)) b =>
    let saved := (← get).defers
    modify fun st => { st with defers := d }
    let r ← block b k
    modify fun st => { st with defers := saved }
    return r
  | .seq a b => return (← block a none) ++ (← block b k)
  | .assign i e1 => block e1 (some fun v => app k (.assign i v))
  | .ite c t e2 =>
    if ← hasS c then throw "internal error: a suspending call in a failure context"
    return [← emit do
      let b ← freshT .int
      let lo := (← get).next + 1
      let tb ← block t k
      let mid := (← get).next
      let eb ← block e2 k
      let sel : Expr := .ite (← seeking) (.ite (← inRange lo mid) (int 1) (int 0)) (.ite (retToDone c) (int 1) (int 0))
      pure (.seq (.assign b sel) (.ite (.prim .eq [.local b, int 1]) (seqVoid tb) (seqVoid eb)))]
  | .loop body =>
    let l ← emit do pure (.loop (seqVoid (← block body none)))
    match k with
    | none => return [l]
    | some k => return [l, ← emit (pure (k vd))]
  | .forE i it filt body =>
    if ← hasS filt then throw "internal error: a suspending call in a failure context"
    if !(← hasS body) then
      -- only the array suspends: compute it first
      let a ← fresh (← infer it)
      let pre ← block it (some (.assign a ·))
      return pre ++ [← emit (pure (app k (.forE i (.local a) (retToDone filt) (retToDone body))))]
    -- a loop over an index (and the array of the body's values, when used)
    let a ← fresh (← infer it)
    let ix ← fresh .int
    let next : Expr := .assign ix (.prim .add [.local ix, int 1])
    let elem : Expr := .seq (.prim .lt [.local ix, .prim .len [.local a]])
      (.assign i (.prim .index [.local a, .local ix]))
    match k with
    | none =>
      block (.seq (.assign a it) (.seq (.assign ix (int 0))
        (.loop (.ite elem (.seq next (.ite filt (.seq body vd) vd)) .brk)))) none
    | some k =>
      let acc ← fresh (← infer e)
      let add : Expr := .assign acc (.prim .concat [.local acc, .prim .mkArr [body]])
      block (.seq (.assign a it) (.seq (.assign ix (int 0)) (.seq (.assign acc (.lit (.arr #[])))
        (.seq (.loop (.ite elem (.seq next (.ite filt (.seq add vd) vd)) .brk)) (.local acc))))) (some k)
  | .call g es =>
    let env ← read
    if g == env.spawnMark then
      -- a new task root, started now (not a suspension point)
      let [.prim .mkArr [.seq (.call h hs) _, .seq (.local t) _]] := es
        | throw "internal error: a malformed spawn"
      let i := (← get).spawnNext
      modify fun st => { st with spawnNext := i + 1 }
      let some (newFn, startFn) := env.spawns[i]? | throw "internal error: spawns miscounted"
      let start : Expr := .call startFn [.local schS, .call newFn (.local schS :: .local t :: hs.map retToDone)]
      let _ := h
      return [← emit (pure (app k (.seq start vd)))]
    if g == env.branchMark then
      -- an arm over this frame, run as a task root through a wrapper
      -- (`start`), stopped when the function exits (`killMark`)
      let [.prim .mkArr [arm]] := es | throw "internal error: a malformed branch"
      let i := (← get).branchNext
      -- (its slot in `branchArms` taken now: the branches in its body are
      -- numbered after it but lowered first)
      modify fun st => { st with branchNext := i + 1, branchArms := st.branchArms.push (0, 0, true) }
      let some (startFn, stopFn, wrapTag) := env.branches[i]? | throw "internal error: branches miscounted"
      let wide : VTy := .ref [wrapTag, env.schedTag] []
      let s ← emit do
        let site := (← get).next + 1
        modify fun st => { st with next := site, children := st.children.push wide }
        let a := (← get).armsNext
        modify fun st => { st with armsNext := a + 1, arms := st.arms.push (vd, vd) }
        let pcA := armPcF env.sites a
        let doneA := armDoneF env.sites a
        let (res, can) ← region pcA none arm
        let y ← freshT wide
        let killInfo := (childF site, wrapTag, stopFn, y, pcA, doneA, env.fnBase + 2 * a + 1)
        modify fun st => { st with arms := st.arms.set! a (res, can) }
        modify fun st => { st with kills := st.kills.push killInfo }
        modify fun st => { st with branchArms := st.branchArms.set! i (env.fnBase + 2 * a, doneA, true) }
        -- (`start(sched, frame)` makes the wrapper, registers it, runs the
        -- arm once and gives the wrapper, kept in the frame for `stop`)
        pure (seqVoid [fset pcA (int 0), fset doneA (int 0), spillMark,
          fset (childF site) (.call startFn [.local schS, fr]), reloadMark])
      match k with
      | some k => return [s, ← emit (pure (k vd))]
      | none => return [s]
    if isMark env g then
      let [.prim .mkArr arms] := es | throw "internal error: a malformed sync or race"
      let s ← emit (concAt (g == env.syncMark) arms (g == env.rushMark))
      match k with
      | none => return [s]
      | some k => return [s, ← emit (pure (k vd))]
    let (pre, rs) ← operands es
    match env.callee g with
    | some c =>
      let (s, v) ← emitWith (suspendAt g c rs)
      match k with
      | none => return pre ++ [s]
      | some k => return pre ++ [s, ← emit (pure (k v))]
    | none => return pre ++ [← emit (pure (app k (.call g rs)))]
  | .prim p es =>
    let (pre, rs) ← operands es
    return pre ++ [← emit (pure (app k (.prim p rs)))]
  | .heap op es =>
    let (pre, rs) ← operands es
    return pre ++ [← emit (pure (app k (.heap op rs)))]
  | .print e1 =>
    let (pre, rs) ← operands [e1]
    return pre ++ [← emit (pure (app k (.print rs.head!)))]
  | .ret e1 => block e1 (some fun v => .seq (fset resF v) (.seq killMark (.ret (int 1))))
  | e => return [← emit (pure (app k (retToDone e)))]

/-- Operands evaluated left to right, some of which suspend: those before
    the last that suspends go to temporaries first. -/
partial def operands (es : List Expr) : M (List Expr × List Expr) := do
  let flags ← es.mapM hasS
  match (flags.zipIdx.filter (·.1)).getLast? with
  | none => return ([], es)
  | some (_, j) =>
    let mut pre : Array Expr := #[]
    let mut rs : Array Expr := #[]
    for (e, i) in es.zipIdx do
      if i > j || (i < j && stable e) then rs := rs.push (retToDone e)
      else
        let t ← fresh (← infer e)
        pre := pre ++ (← block e (some (.assign t ·)))
        rs := rs.push (.local t)
    return (pre.toList, rs.toList)

/-- The statement of a call of a suspends function: on arrival, make (or
    reset) the callee's frame with arguments `rs`; then resume it; if it is
    pending, store the slots and return 0; else take its result. Gives the
    statement and the call's value. -/
partial def suspendAt (g : Nat) (c : Callee) (rs : List Expr) : M (Expr × Expr) := do
  let env ← read
  let newArgs (as : List Expr) : List Expr := if c.newSched then .local schS :: as else as
  if c.generic then
    -- an option field, unwrapped in conditions
    let fty ← infer (.call c.newFn (newArgs rs))
    let k ← newSite (.opt fty)
    modify fun st => { st with sites := st.sites.push { id := k, waits := .callee k c 0 [], defers := st.defers } }
    let cf := childF k
    let q : Expr := .prim .query [fget cf]
    let create : Expr := .ite (.call c.initFn (q :: rs)) vd (.seq (fset cf (.prim .mkSome [.call c.newFn (newArgs rs)])) vd)
    let st ← freshT .int
    let arrive : Expr := .ite (← seeking) vd (.seq create (.seq (fset env.pcFld (int k)) vd))
    let poll : Expr := .ite (.assign st (.call c.resumeFn ([q, .local schS] ++ c.passFields.map fun f => .heap (.get f) [q])))
      vd (.seq (.prim .userErr []) vd)
    let pend : Expr := .ite (.prim .eq [.local st, int 0]) (.seq spillMark (.ret (int 0))) vd
    let found : Expr := .assign env.rS (int 0)
    match c.resField with
    | some rf =>
      let t ← fresh (← infer (.call g rs))
      let take : Expr := .ite (.assign t (.heap (.get rf) [q])) vd (.seq (.prim .userErr []) vd)
      return (seqVoid [arrive, found, poll, pend, take], .local t)
    | none => return (seqVoid [arrive, found, poll, pend], vd)
  -- a field of type `ref [tag, sched] []` (first the scheduler), copied to a
  -- slot of that type (whose initial value is the scheduler parameter) and
  -- resumed after a test of its class, so not in a condition: C journals
  -- the writes made in a condition. The arguments stay in slots, for each
  -- resumption.
  let wide : VTy := .ref [c.tag, env.schedTag] []
  let k ← newSite wide
  let cf := childF k
  let ptys := ((env.S.fns[g]?).map (·.1)).getD []
  let argSlots ← ptys.mapM fresh
  let as := argSlots.map Expr.local
  let y ← freshT wide
  modify fun st => { st with sites := st.sites.push { id := k, waits := .callee k c y argSlots, defers := st.defers } }
  let isC : Expr := .heap (.isTag [c.tag]) [.local y]
  let st ← freshT .int
  let arrive : Expr := .ite (← seeking) vd (seqVoid (
    (argSlots.zip rs).map (fun (a, r) => .assign a r) ++
    [.assign y (fget cf),
     .ite isC (.call c.initFn (.local y :: as)) (.seq (fset cf (.call c.newFn (newArgs as))) vd),
     fset env.pcFld (int k)]))
  let pass := if c.passFields.isEmpty then [] else as
  let poll : Expr := seqVoid [.assign y (fget cf),
    .assign st (.ite isC (.call c.resumeFn (.local y :: .local schS :: pass)) (.prim .userErr []))]
  let pend : Expr := .ite (.prim .eq [.local st, int 0]) (.seq spillMark (.ret (int 0))) vd
  let found : Expr := .assign env.rS (int 0)
  match c.resField, c.resultFn with
  | some _, some rfn =>
    let t ← fresh (← infer (.call g rs))
    let take : Expr := .assign t (.ite isC (.call rfn [.local y]) (.prim .userErr []))
    return (seqVoid [arrive, found, poll, pend, take], .local t)
  | _, _ => return (seqVoid [arrive, found, poll, pend], vd)

/-- The statement of a `sync` (`isSync`) or `race` with arms `arms` (each
    a statement that leaves the arm's value in a slot). -/
partial def concAt (isSync : Bool) (arms : List Expr) (isRush : Bool := false) : M Expr := do
  let k ← newSite .int
  let env ← read
  let defersHere := (← get).defers
  -- (a `rush`'s arms each get a wrapper, as a `branch`, for its losers to
  -- go on as tasks; their numbers and fields are taken first)
  let mut rushW : Array (Nat × Nat × Nat × Nat × Nat) := #[]
  if isRush then
    for _ in arms do
      let i := (← get).branchNext
      modify fun st => { st with branchNext := i + 1, branchArms := st.branchArms.push (0, 0, false) }
      let some (startFn, stopFn, wrapTag) := env.branches[i]? | throw "internal error: branches miscounted"
      let site := (← get).next + 1
      modify fun st => { st with next := site, children := st.children.push (.ref [wrapTag, env.schedTag] []) }
      rushW := rushW.push (i, startFn, stopFn, wrapTag, site)
  -- each arm, a region of its own
  let mut info : Array (Nat × Nat × Nat × Nat) := #[]
  for arm in arms do
    let a := (← get).armsNext
    modify fun st => { st with armsNext := a + 1, arms := st.arms.push (vd, vd) }
    let pcA := armPcF env.sites a
    let doneA := armDoneF env.sites a
    let (res, can) ← region pcA (none) arm
    modify fun st => { st with arms := st.arms.set! a (res, can) }
    info := info.push (env.fnBase + 2 * a, env.fnBase + 2 * a + 1, pcA, doneA)
  modify fun st => { st with sites := st.sites.push { id := k, waits := .arms info.toList, defers := defersHere } }
  let args ← armArgs
  let st ← freshT .int
  let arrive : Expr := .ite (← seeking) vd (seqVoid
    (info.toList.flatMap (fun (_, _, pcA, doneA) => [fset pcA (int 0), fset doneA (int 0)]) ++ [fset env.pcFld (int k)]))
  let found : Expr := .assign env.rS (int 0)
  let run (res doneA : Nat) : Expr := seqVoid [spillMark, .assign st (.call res args),
    .ite (.prim .eq [.local st, int 1]) (.seq (fset doneA (int 1)) vd) vd, reloadMark]
  if isSync then
    let polls := info.toList.map fun (res, _, _, doneA) =>
      Expr.ite (.prim .eq [fget doneA, int 0]) (.seq (run res doneA) vd) vd
    let all := allOf (info.toList.map fun (_, _, _, doneA) => .prim .eq [fget doneA, int 1])
    let wait : Expr := .ite all vd (.seq spillMark (.ret (int 0)))
    return seqVoid ([arrive, found] ++ polls ++ [wait])
  else
    let w ← freshT .int
    let polls := info.toList.zipIdx.map fun ((res, _, _, doneA), i) =>
      Expr.ite (.prim .eq [.local w, int (-1)])
        (.seq (Expr.ite (.prim .eq [fget doneA, int 0])
          (.seq (seqVoid [run res doneA, .ite (.prim .eq [fget doneA, int 1]) (.seq (.assign w (int i)) vd) vd]) vd) vd) vd) vd
    let wait : Expr := .ite (.prim .eq [.local w, int (-1)]) (.seq spillMark (.ret (int 0))) vd
    if isRush then
      -- the arms that started and are pending go on as tasks, through
      -- their wrappers (registered, not run), stopped when the function exits
      let mut goOn : Array Expr := #[]
      for (((res, can, pcA, doneA), (i, startFn, stopFn, wrapTag, site)), j) in (info.toList.zip rushW.toList).zipIdx do
        let y ← freshT (.ref [wrapTag, env.schedTag] [])
        modify fun st => { st with kills := st.kills.push (childF site, wrapTag, stopFn, y, pcA, doneA, can) }
        modify fun st => { st with branchArms := st.branchArms.set! i (res, doneA, false) }
        goOn := goOn.push (Expr.ite (allOf [.prim .ne [.local w, int j], .prim .ne [fget pcA, int 0], .prim .eq [fget doneA, int 0]])
          (.seq (fset (childF site) (.call startFn [.local schS, fr])) vd) vd)
      return seqVoid ([arrive, found, .assign w (int (-1))] ++ polls ++ [wait] ++ goOn.toList)
    -- the winner cancels the arms that started and are pending, last first
    let cancels := info.toList.zipIdx.reverse.map fun ((_, can, pcA, doneA), i) =>
      Expr.ite (allOf [.prim .ne [.local w, int i], .prim .ne [fget pcA, int 0], .prim .eq [fget doneA, int 0]])
        (.seq (seqVoid [spillMark, .call can args, reloadMark]) vd) vd
    return seqVoid ([arrive, found, .assign w (int (-1))] ++ polls ++ [wait] ++ cancels)

/-- Lower `body` as a region whose suspension point is in field `pcFld`:
    its resume body (ending with `done`, or, for an arm, storing the slots
    and giving 1) and its cancel body. -/
partial def region (pcFld : Nat) (done : Option (Expr → Expr)) (body : Expr) : M (Expr × Expr) := do
  let env ← read
  let rS ← freshT .int
  let saved ← get
  modify fun st => { st with regionNext := 0, sites := #[], defers := vd }
  let regionTotal := countSusp (fun f => (env.callee f).isSome || isMark env f)
    (fun f => isMark env f || f == env.branchMark) true (· == env.spawnMark) body
  let stmts ← withReader (fun e => { e with pcFld, rS, regionTotal }) (block body done)
  let st ← get
  if st.regionNext != regionTotal then
    throw "internal error: lowering a <suspends> function: suspension points miscounted"
  let seek : Expr := .assign rS (.ite (.prim .eq [fget pcFld, int 0]) (int 0) (int 1))
  let finish : List Expr := match done with
    | some _ => []
    | none => [spillMark]
  let resume := Expr.seq (seqVoid ([reloadMark, seek] ++ stmts ++ finish)) (int 1)
  -- cancel: what the current suspension point waits for, then its defers
  let args ← armArgs
  let cancelAt (s : Site) : Expr :=
    let child : Expr := match s.waits with
      | .callee k c y as => match c.cancelFn with
        | some cf =>
          if c.generic then
            let q : Expr := .prim .query [fget (childF k)]
            .ite (.call cf ([q, .local schS] ++ c.passFields.map fun f => .heap (.get f) [q])) vd vd
          else
            -- (the child's frame, as `suspendAt` reads it: through a slot
            -- of its field's type, and with its parameters from its frame)
            let pass := if c.passFields.isEmpty then [] else as.map Expr.local
            .seq (.assign y (fget (childF k)))
              (.seq (.ite (.heap (.isTag [c.tag]) [.local y]) (.call cf (.local y :: .local schS :: pass)) vd) vd)
        | none => vd
      | .arms as => seqVoid (as.reverse.map fun (_, can, pcA, doneA) =>
          .ite (allOf [.prim .ne [fget pcA, int 0], .prim .eq [fget doneA, int 0]])
            (.seq (seqVoid [spillMark, .call can args, reloadMark]) vd) vd)
    .ite (.prim .eq [fget pcFld, int s.id]) (.seq (seqVoid [child, s.defers]) vd) vd
  -- (a function's cancel also stops its branches, before the rest)
  -- (a function's branches are stopped last, after its own defers, as when
  -- it returns)
  let cancel := seqVoid ([reloadMark] ++ st.sites.toList.map cancelAt ++
    (if pcFld == pcF then [killMark] else []) ++ [spillMark])
  modify fun st => { st with regionNext := saved.regionNext, sites := saved.sites, defers := saved.defers }
  return (resume, cancel)
end

/-- Replace the spill and reload placeholders. -/
partial def fill (spill reload : Expr) (kill : Expr := vd) : Expr → Expr
  | .heap (.get 1000000007) [] => spill
  | .heap (.get 1000000009) [] => reload
  | .heap (.get 1000000011) [] => fill spill reload vd kill
  | .assign i e => .assign i (fill spill reload kill e)
  | .forE i it f b => .forE i (fill spill reload kill it) (fill spill reload kill f) (fill spill reload kill b)
  | .seq a b => .seq (fill spill reload kill a) (fill spill reload kill b)
  | .prim p es => .prim p (es.map (fill spill reload kill))
  | .call f es => .call f (es.map (fill spill reload kill))
  | .heap op es => .heap op (es.map (fill spill reload kill))
  | .ite c t e => .ite (fill spill reload kill c) (fill spill reload kill t) (fill spill reload kill e)
  | .loop b => .loop (fill spill reload kill b)
  | .ret e => .ret (fill spill reload kill e)
  | .print e => .print (fill spill reload kill e)
  | e => e

/-- The element slots of the `for`s in `e`. -/
partial def forBinders : Expr → List Nat
  | .forE i it f b => i :: forBinders it ++ forBinders f ++ forBinders b
  | .assign _ e | .ret e | .print e | .loop e => forBinders e
  | .seq a b => forBinders a ++ forBinders b
  | .prim _ es | .call _ es | .heap _ es => (es.map forBinders).flatten
  | .ite c t e => forBinders c ++ forBinders t ++ forBinders e
  | _ => []

/-- `e` with the slots `fld` maps read and written in the frame's fields. -/
partial def toFields (fld : Nat → Option Nat) : Expr → Expr
  | .local j => match fld j with
    | some f => fget f
    | none => .local j
  | .assign j e => match fld j with
    | some f => fset f (toFields fld e)
    | none => .assign j (toFields fld e)
  | .forE i it f b => .forE i (toFields fld it) (toFields fld f) (toFields fld b)
  | .seq a b => .seq (toFields fld a) (toFields fld b)
  | .prim p es => .prim p (es.map (toFields fld))
  | .call g es => .call g (es.map (toFields fld))
  | .heap op es => .heap op (es.map (toFields fld))
  | .ite c t e => .ite (toFields fld c) (toFields fld t) (toFields fld e)
  | .loop b => .loop (toFields fld b)
  | .ret e => .ret (toFields fld e)
  | .print e => .print (toFields fld e)
  | e => e

/-- The slots `e` uses. -/
partial def slotsOf : Expr → List Nat
  | .local j => [j]
  | .assign j e => j :: slotsOf e
  | .forE i it f b => i :: slotsOf it ++ slotsOf f ++ slotsOf b
  | .ret e | .print e | .loop e => slotsOf e
  | .seq a b => slotsOf a ++ slotsOf b
  | .prim _ es | .call _ es | .heap _ es => (es.map slotsOf).flatten
  | .ite c t e => slotsOf c ++ slotsOf t ++ slotsOf e
  | _ => []

/-- `e` with its slots renamed by `ren`. -/
partial def renumber (ren : Nat → Nat) : Expr → Expr
  | .local j => .local (ren j)
  | .assign j e => .assign (ren j) (renumber ren e)
  | .forE i it f b => .forE (ren i) (renumber ren it) (renumber ren f) (renumber ren b)
  | .seq a b => .seq (renumber ren a) (renumber ren b)
  | .prim p es => .prim p (es.map (renumber ren))
  | .call g es => .call g (es.map (renumber ren))
  | .heap op es => .heap op (es.map (renumber ren))
  | .ite c t e => .ite (renumber ren c) (renumber ren t) (renumber ren e)
  | .loop b => .loop (renumber ren b)
  | .ret e => .ret (renumber ren e)
  | .print e => .print (renumber ren e)
  | e => e

/-- A function of a lowered suspends function: its body, without the slots'
    initialisations, and its slot types (the frame, the scheduler, the
    parameters, then the transient slots it uses). -/
structure LFn where
  body : Expr
  slots : List VTy

/-- A lowered suspends function. -/
structure Lowered where
  /-- `resume` and `cancel`. -/
  body : LFn
  cancel : LFn
  /-- Each arm's resume and cancel (functions `fnBase + 2a`, `+ 1`). -/
  arms : List (LFn × LFn)
  /-- The frame's field types. -/
  fields : List VTy
  /-- Each `branch`'s (and `rush` arm's) arm resume function, done field,
      and whether its wrapper runs it at once, in their numbering order. -/
  branchArms : List (Nat × Nat × Bool) := []

/-- Lower the body `b` (initialisations stripped) of a suspends function
    with `arity` parameters, slot types `Γ` and result type `ρ`, whose frame
    type is `frameTy`; its arm functions are numbered from `fnBase`. -/
def lower (S : Sigs) (callee : Nat → Option Callee) (syncMark raceMark rushMark spawnMark : Nat) (spawns : Array (Nat × Nat))
    (branchMark : Nat) (branches : Array (Nat × Nat × Nat))
    (arity : Nat) (Γ : List VTy) (ρ : VTy) (frameTy : VTy) (schedTag : Nat) (fnBase : Nat) (b : Expr) :
    Except String Lowered := do
  let schedTy : VTy := .ref [schedTag] []
  let isM := fun f => f == syncMark || f == raceMark || f == rushMark
  let isS := fun f => (callee f).isSome || isM f
  let sites := countSusp (fun f => isS f || f == branchMark) (fun _ => false) false (· == spawnMark) b +
    countArms (· == rushMark) b
  let armsTotal := countArms (fun f => isM f || f == branchMark) b
  let b := shift 2 b
  let Γ0 := #[frameTy, schedTy] ++ Γ.toArray
  let trans0 := #[true, true] ++ (List.replicate Γ.length false).toArray
  let env : Env := { S, ρ, callee, syncMark, raceMark, rushMark, arity, sites, armsTotal, fnBase, schedTag, spawnMark, spawns,
                     branchMark, branches,
                     pcFld := pcF, rS := 0, regionTotal := 0 }
  let done : Expr → Expr := fun v => .seq (fset resF v) (.seq killMark (.ret (int 1)))
  let ((res, can), st) ← ((region pcF (some done) b).run env).run { Γ := Γ0, trans := trans0 }
  if st.next != sites || st.armsNext != armsTotal then
    throw "internal error: lowering a <suspends> function: suspension points miscounted"
  let base := slotBaseOf sites armsTotal
  -- stopping the branches: each wrapper marked done (through a test of its
  -- class), each arm still pending cancelled and marked dead
  let args : List Expr := [fr, .local schS] ++ (List.range arity).map fun i => .local (i + 2)
  -- (last started first, as a `race`'s losers)
  let kill := seqVoid (st.kills.toList.reverse.map fun (wf, wrapTag, stopFn, y, pcA, doneA, can) =>
    seqVoid [.assign y (fget wf),
      .ite (.heap (.isTag [wrapTag]) [.local y]) (.call stopFn [.local y, .local schS]) vd,
      .ite (allOf [.prim .ne [fget pcA, int 0], .prim .eq [fget doneA, int 0]])
        (.seq (seqVoid [.call can args, fset doneA (int 2)]) vd) vd])
  -- the slots kept across suspension points live in the frame: their reads
  -- and writes become the frame's (so nothing is stored or reloaded), except
  -- a `for`'s element slot, bound by the `for` itself; each function then
  -- keeps only the transient slots it uses, renumbered after its parameters
  let finish (e : Expr) : LFn :=
    let e := fill vd vd kill e
    let binders := forBinders e
    let resident (j : Nat) : Bool :=
      j ≥ 2 + arity && !((st.trans[j]?).getD false) && !binders.contains j
    let e := toFields (fun j => if resident j then some (base + (j - 2)) else none) e
    let used := ((slotsOf e).filter (· ≥ 2 + arity)).eraseDups.mergeSort
    let ren (j : Nat) : Nat := if j < 2 + arity then j else 2 + arity + ((used.idxOf? j).getD 0)
    { body := renumber ren e, slots := st.Γ.toList.take (2 + arity) ++ used.map fun j => (st.Γ[j]?).getD .int }
  return { body := finish res, cancel := finish can, arms := st.arms.toList.map fun (r, c) => (finish r, finish c),
           branchArms := st.branchArms.toList,
           fields := [.int, ρ] ++ st.children.toList ++ List.replicate (2 * armsTotal) .int ++
             (st.Γ.toList.drop 2) }

end OpenVerse.Front.Suspend
