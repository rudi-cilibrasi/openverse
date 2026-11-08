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
  | .ret e => .seq (fset resF (retToDone e)) (.ret (int 1))
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
partial def countSusp (isS : Nat → Bool) (m : Nat → Bool := fun _ => false) (own : Bool := false) : Expr → Nat
  | .call f es =>
    (if isS f then 1 else 0) + (if own && m f then 0 else (es.map (countSusp isS m own)).sum)
  | .assign _ e | .ret e | .print e | .loop e => countSusp isS m own e
  | .seq a b => countSusp isS m own a + countSusp isS m own b
  | .prim _ es | .heap _ es => (es.map (countSusp isS m own)).sum
  | .ite c t e => countSusp isS m own c + countSusp isS m own t + countSusp isS m own e
  | .forE _ it f b => countSusp isS m own it + countSusp isS m own f + countSusp isS m own b
  | _ => 0

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
  /-- The function's parameters (slots 2 …), passed on to its arms. -/
  arity : Nat
  /-- Suspension points and arms in the whole function. -/
  sites : Nat
  armsTotal : Nat
  /-- The index of the function's first arm function. -/
  fnBase : Nat
  /-- The scheduler's class. -/
  schedTag : Nat
  /-- The region being lowered: the field of its suspension point, the flag
      set while seeking it, and its own suspension points. -/
  pcFld : Nat
  rS : Nat
  regionTotal : Nat

structure St where
  /-- The functions' slot types (shared by the body and its arms). -/
  Γ : Array VTy
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

abbrev M := ReaderT Env (StateT St (Except String))

def fresh (τ : VTy) : M Nat :=
  modifyGet fun st => (st.Γ.size, { st with Γ := st.Γ.push τ })

def infer (e : Expr) : M VTy := do
  let env ← read
  match tc env.S (← get).Γ.toList env.ρ e none with
  | some τ => pure τ
  | none => throw "internal error: lowering a <suspends> function: cannot infer the type of a value kept across a suspension point"

def isMark (env : Env) (f : Nat) : Bool := f == env.syncMark || f == env.raceMark

def hasS (e : Expr) : M Bool := do
  let env ← read
  return hasSusp (fun f => (env.callee f).isSome || isMark env f) e

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
      let b ← fresh .int
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
    if isMark env g then
      let [.prim .mkArr arms] := es | throw "internal error: a malformed sync or race"
      let s ← emit (concAt (g == env.syncMark) arms)
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
  | .ret e1 => block e1 (some fun v => .seq (fset resF v) (.ret (int 1)))
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
    let st ← fresh .int
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
  let y ← fresh wide
  modify fun st => { st with sites := st.sites.push { id := k, waits := .callee k c y argSlots, defers := st.defers } }
  let isC : Expr := .heap (.isTag [c.tag]) [.local y]
  let st ← fresh .int
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
partial def concAt (isSync : Bool) (arms : List Expr) : M Expr := do
  let k ← newSite .int
  let env ← read
  let defersHere := (← get).defers
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
  let st ← fresh .int
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
    let w ← fresh .int
    let polls := info.toList.zipIdx.map fun ((res, _, _, doneA), i) =>
      Expr.ite (.prim .eq [.local w, int (-1)])
        (.seq (Expr.ite (.prim .eq [fget doneA, int 0])
          (.seq (seqVoid [run res doneA, .ite (.prim .eq [fget doneA, int 1]) (.seq (.assign w (int i)) vd) vd]) vd) vd) vd) vd
    let wait : Expr := .ite (.prim .eq [.local w, int (-1)]) (.seq spillMark (.ret (int 0))) vd
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
  let rS ← fresh .int
  let saved ← get
  modify fun st => { st with regionNext := 0, sites := #[], defers := vd }
  let regionTotal := countSusp (fun f => (env.callee f).isSome || isMark env f) (isMark env) true body
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
  let cancel := seqVoid ([reloadMark] ++ st.sites.toList.map cancelAt ++ [spillMark])
  modify fun st => { st with regionNext := saved.regionNext, sites := saved.sites, defers := saved.defers }
  return (resume, cancel)
end

/-- Replace the spill and reload placeholders. -/
partial def fill (spill reload : Expr) : Expr → Expr
  | .heap (.get 1000000007) [] => spill
  | .heap (.get 1000000009) [] => reload
  | .assign i e => .assign i (fill spill reload e)
  | .forE i it f b => .forE i (fill spill reload it) (fill spill reload f) (fill spill reload b)
  | .seq a b => .seq (fill spill reload a) (fill spill reload b)
  | .prim p es => .prim p (es.map (fill spill reload))
  | .call f es => .call f (es.map (fill spill reload))
  | .heap op es => .heap op (es.map (fill spill reload))
  | .ite c t e => .ite (fill spill reload c) (fill spill reload t) (fill spill reload e)
  | .loop b => .loop (fill spill reload b)
  | .ret e => .ret (fill spill reload e)
  | .print e => .print (fill spill reload e)
  | e => e

/-- A lowered suspends function. -/
structure Lowered where
  /-- `resume`'s and `cancel`'s bodies, without the slots' initialisations. -/
  body : Expr
  cancel : Expr
  /-- Each arm's resume and cancel bodies (functions `fnBase + 2a`, `+ 1`). -/
  arms : List (Expr × Expr)
  /-- The functions' slot types (frame, scheduler, the parameters, then the
      other slots and the temporaries). -/
  slots : List VTy
  /-- The frame's field types. -/
  fields : List VTy

/-- Lower the body `b` (initialisations stripped) of a suspends function
    with `arity` parameters, slot types `Γ` and result type `ρ`, whose frame
    type is `frameTy`; its arm functions are numbered from `fnBase`. -/
def lower (S : Sigs) (callee : Nat → Option Callee) (syncMark raceMark : Nat) (arity : Nat) (Γ : List VTy)
    (ρ : VTy) (frameTy : VTy) (schedTag : Nat) (fnBase : Nat) (b : Expr) : Except String Lowered := do
  let schedTy : VTy := .ref [schedTag] []
  let isM := fun f => f == syncMark || f == raceMark
  let isS := fun f => (callee f).isSome || isM f
  let sites := countSusp isS
  let sites := sites b
  let armsTotal := countArms isM b
  let b := shift 2 b
  let Γ0 := #[frameTy, schedTy] ++ Γ.toArray
  let env : Env := { S, ρ, callee, syncMark, raceMark, arity, sites, armsTotal, fnBase, schedTag,
                     pcFld := pcF, rS := 0, regionTotal := 0 }
  let done : Expr → Expr := fun v => .seq (fset resF v) (.ret (int 1))
  let ((res, can), st) ← ((region pcF (some done) b).run env).run { Γ := Γ0 }
  if st.next != sites || st.armsNext != armsTotal then
    throw "internal error: lowering a <suspends> function: suspension points miscounted"
  let n := st.Γ.size
  let base := slotBaseOf sites armsTotal
  let spill := seqVoid ((List.range (n - 2)).map fun j => fset (base + j) (.local (j + 2)))
  let reload := seqVoid ((List.range (n - 2)).map fun j => .assign (j + 2) (fget (base + j)))
  let f := fill spill reload
  return { body := f res, cancel := f can, arms := st.arms.toList.map fun (r, c) => (f r, f c),
           slots := st.Γ.toList,
           fields := [.int, ρ] ++ st.children.toList ++ List.replicate (2 * armsTotal) .int ++
             (st.Γ.toList.drop 2) }

end OpenVerse.Front.Suspend
