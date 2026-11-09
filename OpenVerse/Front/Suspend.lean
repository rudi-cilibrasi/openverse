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
  /-- A callee's frame is kept in a field of type `ref [tag, sched] []`,
      first the scheduler, and resumed by a test of its class
      (`Typed.dispatch`), outside any condition. A generic callee's frame
      has type arguments, which the scheduler's type has none of: its field
      has type `ref [tag, $nil] args`, first an empty object made at those
      arguments (#256), and it is resumed and cancelled through helpers
      that read its parameters from it (`passFields` is empty). -/
  generic : Bool := false
  /-- `new` takes the scheduler first (to fill its frame's child fields). -/
  newSched : Bool := false
  /-- The callee's result getter, `g$result(frame)`. -/
  resultFn : Option Nat := none
  /-- For a method of a class that fixes type arguments, called through
      `Typed.dispatch` (#142): helpers taking the receiver first, so that
      the code depending on the refinement keeps the rule's shape —
      `arrive(self, args…, frame, sched)` (resets the frame, or makes one),
      `take(self, frame)` (the result), and `resume(frame, sched)` and
      `cancel(frame, sched)` (with the parameters from the frame). -/
  selfFns : Option (Nat × Nat × Nat × Nat) := none
  /-- The callee's number of type parameters (its frame's type arguments). -/
  ntp : Nat := 0
  deriving Inhabited

/-- Slots of a resume function: the frame, the scheduler. -/
def frS : Nat := 0
def schS : Nat := 1

/-- Frame fields: the suspension point the body is at (0: not started), the
    result, one field per suspension point (a callee's frame), two per arm
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

/-- `return e` as: store `e` as the result, then (in the function's body)
    stop its branches and give 1 (done), or (in an arm of a `sync`, `race`
    or `rush`) give 2: the function returns, which the code around the arm
    carries out. -/
partial def retToDone (arm : Bool := false) : Expr → Expr
  | .ret e => .seq (fset resF (retToDone arm e))
      (if arm then .ret (int 2) else .seq killMark (.ret (int 1)))
  | .assign i e => .assign i (retToDone arm e)
  | .forE i it f b => .forE i (retToDone arm it) (retToDone arm f) (retToDone arm b)
  | .seq a b => .seq (retToDone arm a) (retToDone arm b)
  | .prim p es => .prim p (es.map (retToDone arm))
  | .call f es => .call f (es.map (retToDone arm))
  | .heap op es => .heap op (es.map (retToDone arm))
  | .ite c t e => .ite (retToDone arm c) (retToDone arm t) (retToDone arm e)
  | .loop b => .loop (retToDone arm b)
  | .print e => .print (retToDone arm e)
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
    -- (the spawns in its arguments first: they start first, #180)
    | true, [.prim .mkArr [.seq (.call g gs) _, .seq (.local t) _]] => (gs.map (spawnSites m)).flatten ++ [(g, gs, t)]
    | _, _ => (es.map (spawnSites m)).flatten
  | .assign _ e | .ret e | .print e | .loop e => spawnSites m e
  | .seq a b => spawnSites m a ++ spawnSites m b
  | .prim _ es | .heap _ es => (es.map (spawnSites m)).flatten
  | .ite c t e => spawnSites m c ++ spawnSites m t ++ spawnSites m e
  | .forE _ it f b => spawnSites m it ++ spawnSites m f ++ spawnSites m b
  | _ => []

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

/-- Whether `e` is a method call's dispatch on the class of the receiver in
    slot `y` (#34, #142): a chain of class tests of it (each binding the
    narrowed receiver to a slot, or in `Typed.dispatch`'s shape), each
    running an implementation, ending in `userErr`. -/
partial def isDispatchChainOn (y : Nat) : Expr → Bool
  | .ite (.assign sd (.heap (.isTag _) [.local y'])) _ e => y' == y && sd != y && isDispatchChainOn y e
  | .ite (.heap (.isTag _) [.local y']) _ e => y' == y && isDispatchChainOn y e
  | .prim .userErr [] => true
  | _ => false

/-- `isDispatchChainOn` at the receiver its first test reads. -/
def isDispatchChain : Expr → Bool
  | e@(.ite (.assign _ (.heap (.isTag _) [.local y])) _ _) => isDispatchChainOn y e
  | e@(.ite (.heap (.isTag _) [.local y]) _ _) => isDispatchChainOn y e
  | _ => false

/-- Every call in `e`: its callee and arguments. -/
partial def callsOf : Expr → List (Nat × List Expr)
  | .call f es => (f, es) :: (es.map callsOf).flatten
  | .assign _ e | .ret e | .print e | .loop e => callsOf e
  | .seq a b => callsOf a ++ callsOf b
  | .prim _ es | .heap _ es => (es.map callsOf).flatten
  | .ite c t e => callsOf c ++ callsOf t ++ callsOf e
  | .forE _ it f b => callsOf it ++ callsOf f ++ callsOf b
  | _ => []

/-- The code each test of a dispatch chain runs. -/
partial def chainArms : Expr → List Expr
  | .ite _ t e => t :: chainArms e
  | _ => []

/-- The `spawn`s (mark `m`) in `e` of a dispatch chain rather than a call
    (#173): each chain becomes a function, `base + i` for the `i`-th met
    (counting from the state's size), of the slots it uses, called in its
    place. Collects each chain, its slots and its task's slot. -/
partial def liftChains (m base : Nat) : Expr → StateM (Array (Expr × List Nat × Nat)) Expr
  | .call f es => do
    match f == m, es with
    | true, [.prim .mkArr [.seq ch v, .seq (.local t) v2]] =>
      match ch with
      -- (also one whose every test a copy at closed types dropped, #186:
      -- left with its unreachable end, at a type no class implements)
      | .ite .. | .prim .userErr [] =>
        let ops := (slotsOf ch).eraseDups
        let i := (← get).size
        modify (·.push (ch, ops, t))
        return .call f [.prim .mkArr [.seq (.call (base + i) (ops.map Expr.local)) v, .seq (.local t) v2]]
      | .call g gs =>
        let gs ← gs.mapM (liftChains m base)
        return .call f [.prim .mkArr [.seq (.call g gs) v, .seq (.local t) v2]]
      | _ => return .call f es
    | _, _ => return .call f (← es.mapM (liftChains m base))
  | .assign i x => return .assign i (← liftChains m base x)
  | .ret x => return .ret (← liftChains m base x)
  | .print x => return .print (← liftChains m base x)
  | .loop x => return .loop (← liftChains m base x)
  | .seq a b => return .seq (← liftChains m base a) (← liftChains m base b)
  | .prim p es => return .prim p (← es.mapM (liftChains m base))
  | .heap op es => return .heap op (← es.mapM (liftChains m base))
  | .ite c t x => return .ite (← liftChains m base c) (← liftChains m base t) (← liftChains m base x)
  | .forE i it f b => return .forE i (← liftChains m base it) (← liftChains m base f) (← liftChains m base b)
  | x => return x

/-- `e` without the tests in `Typed.dispatch`'s shape that no object can
    pass at the slot types `Γ`: no substitution makes the receiver's type
    arguments agree with any tested class's pins on them (#142, #209), so
    no instance of them starts an object's. The checker types a dispatch
    only when its pins can agree, and such tests arise in a copy of a
    generic function at closed types, where the generic one had a
    refinement (#174), and in #157's field accessors on closed receivers;
    every function is pruned before the lowering (#186). -/
partial def pruneDead (S : Sigs) (Γ : List VTy) : Expr → Expr
  | .ite c@(.heap (.isTag us) [.local y]) t@(.call _ (.local y' :: _)) e =>
    let dead := y == y' && !us.isEmpty && match Γ[y]? with
      | some (.ref _ a) =>
        -- (as the checker opens the arguments beyond `a`, #209)
        let k := openCount S us a.length
        let N := VTy.nvarsL a
        us.all fun u =>
          let P := (S.pinsOf u).take (a.length + k)
          VTy.pinsBelow P (a.length + k) && (unify (VTy.pinEqs P (a ++ VTy.ext N k))).isNone
      | _ => false
    if dead then pruneDead S Γ e else .ite c (pruneDead S Γ t) (pruneDead S Γ e)
  | .assign i x => .assign i (pruneDead S Γ x)
  | .ret x => .ret (pruneDead S Γ x)
  | .print x => .print (pruneDead S Γ x)
  | .loop x => .loop (pruneDead S Γ x)
  | .seq a b => .seq (pruneDead S Γ a) (pruneDead S Γ b)
  | .call f es => .call f (es.map (pruneDead S Γ))
  | .prim p es => .prim p (es.map (pruneDead S Γ))
  | .heap op es => .heap op (es.map (pruneDead S Γ))
  | .ite c t x => .ite (pruneDead S Γ c) (pruneDead S Γ t) (pruneDead S Γ x)
  | .forE i it f b => .forE i (pruneDead S Γ it) (pruneDead S Γ f) (pruneDead S Γ b)
  | x => x

/-- `e` with each call `call g es` for which `r g es` gives a function
    redirected to it (#174). -/
partial def redirectCalls (r : Nat → List Expr → Option Nat) : Expr → Expr
  | .call f es =>
    let es := es.map (redirectCalls r)
    .call ((r f es).getD f) es
  | .assign i x => .assign i (redirectCalls r x)
  | .ret x => .ret (redirectCalls r x)
  | .print x => .print (redirectCalls r x)
  | .loop x => .loop (redirectCalls r x)
  | .seq a b => .seq (redirectCalls r a) (redirectCalls r b)
  | .prim p es => .prim p (es.map (redirectCalls r))
  | .heap op es => .heap op (es.map (redirectCalls r))
  | .ite c t x => .ite (redirectCalls r c) (redirectCalls r t) (redirectCalls r x)
  | .forE i it f b => .forE i (redirectCalls r it) (redirectCalls r f) (redirectCalls r b)
  | x => x

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

/-- `e` with its `spawn`s (calls of the mark `m`, in `spawnSites`' order)
    replaced: the `i`-th by `repl i callee args taskSlot`. -/
partial def substSpawns (m : Nat) (repl : Nat → Nat → List Expr → Nat → Expr) (e : Expr) : Expr :=
  (go e).run' 0
where
  go : Expr → StateM Nat Expr
  | .call f es => do
    match f == m, es with
    | true, [.prim .mkArr [.seq (.call g gs) _, .seq (.local t) _]] =>
      let gs ← gs.mapM go
      let i ← get
      set (i + 1)
      return repl i g gs t
    | _, _ => return .call f (← es.mapM go)
  | .assign i x => return .assign i (← go x)
  | .ret x => return .ret (← go x)
  | .print x => return .print (← go x)
  | .loop x => return .loop (← go x)
  | .seq a b => return .seq (← go a) (← go b)
  | .prim p es => return .prim p (← es.mapM go)
  | .heap op es => return .heap op (← es.mapM go)
  | .ite c t x => return .ite (← go c) (← go t) (← go x)
  | .forE i it f b => return .forE i (← go it) (← go f) (← go b)
  | x => return x

/-- `e` with each call of `f` replaced by `repl args`. -/
partial def substCall (f : Nat) (repl : List Expr → Expr) : Expr → Expr
  | .call g es =>
    let es := es.map (substCall f repl)
    if g == f then repl es else .call g es
  | .assign i x => .assign i (substCall f repl x)
  | .ret x => .ret (substCall f repl x)
  | .print x => .print (substCall f repl x)
  | .loop x => .loop (substCall f repl x)
  | .seq a b => .seq (substCall f repl a) (substCall f repl b)
  | .prim p es => .prim p (es.map (substCall f repl))
  | .heap op es => .heap op (es.map (substCall f repl))
  | .ite c t x => .ite (substCall f repl c) (substCall f repl t) (substCall f repl x)
  | .forE i it fl b => .forE i (substCall f repl it) (substCall f repl fl) (substCall f repl b)
  | x => x

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
  -- (as deep as the elaborator's `slotDefault` goes)
  if depth > 16 then none else
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
  /-- The empty class without type parameters whose objects first fill a
      generic callee's frame field (#256). -/
  nilTag : Nat
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
  /-- The region is an arm of a `sync`, `race` or `rush`. -/
  inArmR : Bool := false
  /-- The index of the function's first refined call helper (after its arms). -/
  viaBase : Nat := 0
  /-- The type the value being lowered is checked against (a slot's, or
      the function's result), when known: a refined call's result needs it. -/
  expTy : Option VTy := none
  rS : Nat
  regionTotal : Nat

structure St where
  /-- The functions' slot types (shared by the body and its arms). -/
  Γ : Array VTy
  /-- Which slots are transient: used only within one resumption (so real
      slots), not kept in the frame. -/
  trans : Array Bool := #[]
  /-- The helpers of the calls under a refinement (#171): each one's body,
      parameter types and result type (functions `viaBase + i`). -/
  vias : Array (Expr × List VTy × VTy) := #[]
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
  kills : Array (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) := #[]
  /-- The slot counting the starts of the function's branches and `rush`
      arms, which each record theirs (the last entry of `kills`), so that
      they are stopped last started first (#187). -/
  seqSlot : Option Nat := none
  /-- By the order the `branch`es (and `rush` arms) are numbered in: each
      one's arm resume function, done field, and whether its wrapper runs
      it at once (a `branch`) or only registers it (a `rush` loser). -/
  branchArms : Array (Nat × Nat × Bool) := #[]
  /-- The entries of `kills` that a `branch`'s or `rush` arm's own code
      started (child, owner), so that each is stopped with its owner, before
      it, and not among the function's own (#254). -/
  killOwner : Array (Nat × Nat) := #[]

/-- The entries `kills[from, to)` not already owned, owned by `owner` (#254). -/
def ownKills (st : St) (lo hi owner : Nat) : St :=
  { st with killOwner := st.killOwner ++ ((List.range (hi - lo)).map (lo + ·) |>.filter
      (fun i => !st.killOwner.any (·.1 == i))).toArray.map (·, owner) }

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

/-- The types a call's arguments are checked against: `g`'s parameter types,
    at the type arguments its other arguments give (none where one of `g`'s
    type variables stays unbound, #188). -/
def callHints (g : Nat) (es : List Expr) : M (List (Option VTy)) := do
  let env ← read
  match env.S.fns[g]? with
  | some (ps, τ) =>
    let acc := bindArgs env.S (← get).Γ.toList env.ρ ps es []
    let θ := callInst acc τ none
    return ps.map fun p => if p.unbound acc then none else some (p.subst θ)
  | none => return []

/-- A new slot recording the start number of a branch or `rush` arm, and
    the statements that number it (#187). -/
def startNumber : M (Nat × Expr) := do
  let cnt ← match (← get).seqSlot with
    | some c => pure c
    | none => do
      let c ← fresh .int
      modify fun st => { st with seqSlot := some c }
      pure c
  let sk ← fresh .int
  return (sk, seqVoid [.assign cnt (.prim .add [.local cnt, int 1]), .assign sk (.local cnt)])

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

/-- Whether a type mentions a reference. -/
partial def refIn : VTy → Bool
  | .ref _ _ => true
  | .arr t | .opt t => refIn t
  | .tup ts => ts.any refIn
  | _ => false

/-- `e` with each `for` whose element has a reference type turned into a
    loop over an index: its element slot then lives in the frame, initialised
    once, rather than being a real slot whose initial value would be a new
    placeholder object at each resumption. -/
partial def loopify (e : Expr) (used : Bool := true) : M Expr := do
  match e with
  | .forE i it f b =>
    let ty := ((← get).Γ[i]?).getD .int
    let τit? := tc (← read).S (← get).Γ.toList (← read).ρ it none
    let τ? := tc (← read).S (← get).Γ.toList (← read).ρ e none
    let it' ← loopify it
    let f' ← loopify f
    let b' ← loopify b
    match refIn ty, τit?, τ? with
    | true, some τit, some τ =>
      let a ← fresh τit
      let ix ← fresh .int
      let next : Expr := .assign ix (.prim .add [.local ix, int 1])
      let elem : Expr := .seq (.prim .lt [.local ix, .prim .len [.local a]])
        (.assign i (.prim .index [.local a, .local ix]))
      if !used then
        -- (its value is dropped: no array of the body's values)
        return .seq (.assign a it') (.seq (.assign ix (int 0))
          (.loop (.ite elem (.seq next (.ite f' (.seq b' vd) vd)) .brk)))
      let acc ← fresh τ
      let add : Expr := .assign acc (.prim .concat [.local acc, .prim .mkArr [b']])
      return .seq (.assign a it') (.seq (.assign ix (int 0)) (.seq (.assign acc (.lit (.arr #[])))
        (.seq (.loop (.ite elem (.seq next (.ite f' (.seq add vd) vd)) .brk)) (.local acc))))
    | _, _, _ => return .forE i it' f' b'
  | .assign j x => return .assign j (← loopify x)
  | .seq x y => return .seq (← loopify x false) (← loopify y used)
  | .prim p es => return .prim p (← es.mapM loopify)
  | .call g es => return .call g (← es.mapM loopify)
  | .heap op es => return .heap op (← es.mapM loopify)
  | .ite c t x => return .ite (← loopify c) (← loopify t) (← loopify x)
  | .loop x => return .loop (← loopify x)
  | .ret x => return .ret (← loopify x)
  | .print x => return .print (← loopify x)
  | e => return e

/-- A call through `Typed.dispatch`'s shape, `ite (isTag us [local y])
    (call g (local y :: es)) _`, of a callee with receiver-first helpers
    (#142): the classes, the receiver's slot, the callee, the arguments. -/
def refined? (c t : Expr) : M (Option (List Nat × Nat × Nat × Callee × List Expr)) := do
  match c, t with
  | .heap (.isTag us) [.local y], .call g (.local y' :: es) =>
    if y != y' then return none
    match (← read).callee g with
    | some cal => return if cal.selfFns.isSome then some (us, y, g, cal, es) else none
    | none => return none
  | _, _ => return none

mutual
/-- The statements of `e`, each guarded, with the continuation `k` applied
    to its value (none: the value is discarded). -/
partial def block (e : Expr) (k : Option (Expr → Expr)) : M (List Expr) := do
  -- (`return` becomes "store the result, give 1" only here, as the user's
  -- code is emitted: inference sees the code as written)
  if !(← hasS e) then
    let e ← loopify e k.isSome
    return [← emit (pure (app k (retToDone (← read).inArmR e)))]
  match e with
  -- the defers active at the suspension points of `b` (`withDeferMark`)
  | .seq (.ite (.prim .fail []) d (.lit .void)) b =>
    let saved := (← get).defers
    modify fun st => { st with defers := d }
    let r ← block b k
    modify fun st => { st with defers := saved }
    return r
  | .seq a b => return (← block a none) ++ (← block b k)
  | .assign i e1 =>
    let τ := (← get).Γ[i]?
    withReader (fun env => { env with expTy := τ }) (block e1 (some fun v => app k (.assign i v)))
  | .ite c t e2 =>
    if ← hasS c then throw "internal error: a suspending call in a failure context"
    return [← emit do
      let b ← freshT .int
      let lo := (← get).next + 1
      let tb ← match ← refined? c t with
        | some (us, y, g, cal, es) => selfCall us y g cal es k
        | none => block t k
      let mid := (← get).next
      let eb ← block e2 k
      let sel : Expr := .ite (← seeking) (.ite (← inRange lo mid) (int 1) (int 0)) (.ite (retToDone (← read).inArmR c) (int 1) (int 0))
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
      let fe ← loopify (.forE i (.local a) filt body) k.isSome
      return pre ++ [← emit (pure (app k (retToDone (← read).inArmR fe)))]
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
      -- (its arguments now, a spawn among them first, #180)
      let (pre, hs) ← operands hs (← callHints h hs)
      let i := (← get).spawnNext
      modify fun st => { st with spawnNext := i + 1 }
      let some (newFn, startFn) := env.spawns[i]? | throw "internal error: spawns miscounted"
      let start : Expr := .call startFn [.local schS, .call newFn (.local schS :: .local t :: hs.map (retToDone false))]
      let _ := h
      return pre ++ [← emit (pure (app k (.seq start vd)))]
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
        let k0 := (← get).kills.size
        let (res, can) ← region pcA none arm
        let k1 := (← get).kills.size
        let y ← freshT wide
        let (sk, number) ← startNumber
        let killInfo := (childF site, wrapTag, stopFn, y, pcA, doneA, env.fnBase + 2 * a + 1, sk)
        modify fun st => { st with arms := st.arms.set! a (res, can) }
        modify fun st => { st with kills := st.kills.push killInfo }
        -- (the branches and `rush` arms its arm starts are stopped with it)
        modify fun st => ownKills st k0 k1 k1
        modify fun st => { st with branchArms := st.branchArms.set! i (env.fnBase + 2 * a, doneA, true) }
        -- (`start(sched, frame)` makes the wrapper, registers it, runs the
        -- arm once and gives the wrapper, kept in the frame for `stop`)
        pure (seqVoid [fset pcA (int 0), fset doneA (int 0), number, spillMark,
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
    let (pre, rs) ← operands es (← callHints g es)
    match env.callee g with
    | some c =>
      let (s, v) ← emitWith (suspendAt g c rs)
      match k with
      | none => return pre ++ [s]
      | some k => return pre ++ [s, ← emit (pure (k v))]
    | none => return pre ++ [← emit (pure (app k (.call g rs)))]
  | .prim p es =>
    -- (an array's or tuple's parts are checked against its expected type's)
    let hints : List (Option VTy) := match p, (← read).expTy with
      | .mkArr, some (.arr τ) => es.map fun _ => some τ
      | .mkTup, some (.tup ts) => ts.map some
      | _, _ => []
    let (pre, rs) ← operands es hints
    return pre ++ [← emit (pure (app k (.prim p rs)))]
  | .heap op es =>
    -- (an object's fields against its class's, at the expected type's
    -- type arguments)
    let env ← read
    let hints : List (Option VTy) := match op, env.expTy with
      | .new c, some (.ref _ args) => ((env.S.classes[c]?).getD []).map fun f => some (f.inst args)
      | _, _ => []
    let (pre, rs) ← operands es hints
    return pre ++ [← emit (pure (app k (.heap op rs)))]
  | .print e1 =>
    let (pre, rs) ← operands [e1]
    return pre ++ [← emit (pure (app k (.print rs.head!)))]
  | .ret e1 =>
    let arm := (← read).inArmR
    withReader (fun env => { env with expTy := some env.ρ })
      (block e1 (some fun v => .seq (fset resF v) (if arm then .ret (int 2) else .seq killMark (.ret (int 1)))))
  | e =>
    let e ← loopify e k.isSome
    return [← emit (pure (app k (retToDone (← read).inArmR e)))]

/-- Operands evaluated left to right, some of which suspend: those before
    the last that suspends go to temporaries first. -/
partial def operands (es : List Expr) (hints : List (Option VTy) := []) : M (List Expr × List Expr) := do
  let flags ← es.mapM hasS
  match (flags.zipIdx.filter (·.1)).getLast? with
  | none => return ([], es)
  | some (_, j) =>
    let mut pre : Array Expr := #[]
    let mut rs : Array Expr := #[]
    for (e, i) in es.zipIdx do
      if i > j || (i < j && stable e) then rs := rs.push (retToDone (← read).inArmR (← loopify e))
      else
        -- (one with no type of its own, `if … then array{} else array{}`:
        -- the type it is checked against, when known, #188)
        let env ← read
        let Γ := (← get).Γ.toList
        let τ ← match tc env.S Γ env.ρ e none, hints[i]? with
          | some τ, _ => pure τ
          | none, some (some h) => if (tc env.S Γ env.ρ e (some h)).isSome then pure h else infer e
          | none, _ => infer e
        let t ← fresh τ
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
  -- a field of type `ref [tag, sched] []` (first the scheduler), copied to a
  -- slot of that type (whose initial value is the scheduler parameter) and
  -- resumed after a test of its class, so not in a condition: C journals
  -- the writes made in a condition, and the reference interpreter copies
  -- the heap at the first one (#256). The arguments stay in slots, for each
  -- resumption. A generic callee's frame has type arguments: its field and
  -- slot have type `ref [tag, $nil] args` (the slot's initial value is the
  -- field, read from the frame), and its resume and cancel functions read
  -- its parameters from it.
  let wide : VTy ← if c.generic then do
      match ← infer (.call c.newFn (newArgs rs)) with
      | .ref _ args => pure (.ref [c.tag, env.nilTag] args)
      | _ => throw "internal error: a generic callee's frame type"
    else pure (.ref [c.tag, env.schedTag] [])
  let k ← newSite wide
  let cf := childF k
  let ptys := if c.generic then [] else ((env.S.fns[g]?).map (·.1)).getD []
  let argSlots ← ptys.mapM fresh
  let as := if c.generic then rs else argSlots.map Expr.local
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

/-- A call of a method of a class that fixes type arguments, through
    `Typed.dispatch` on the receiver in slot `y` (classes `us`, #142). -/
partial def selfCall (us : List Nat) (y g : Nat) (c : Callee) (es : List Expr) (k : Option (Expr → Expr)) :
    M (List Expr) := do
  let (pre, rs) ← operands es
  let schedTag := (← read).schedTag
  let (s, v) ← emitWith (if c.generic then suspendSelfGeneric us y g c rs k.isSome
    else suspendSelf us y c rs k.isSome (.ref [c.tag, schedTag] []))
  match k with
  | none => return pre ++ [s]
  | some k => return pre ++ [s, ← emit (pure (k v))]

/-- `suspendAt` for a call through `Typed.dispatch`: what depends on the
    refinement (the arguments, the result) goes through the callee's
    receiver-first helpers, each called in the rule's shape by a helper of
    this call site whose first parameter is the receiver (`arriveVia(recv,
    args…, frame, sched)`, `takeVia(recv, frame)`), as the receiver's slot
    may be a frame field. The frame is kept as any callee's, in a field of
    type `wide`, and resumed and cancelled with its parameters from itself.
    Gives the statement and the call's value. -/
partial def suspendSelf (us : List Nat) (y : Nat) (c : Callee) (rs : List Expr) (valued : Bool) (wide : VTy) :
    M (Expr × Expr) := do
  let env ← read
  let some (arriveFn, takeFn, resumeFn, cancelFn) := c.selfFns
    | throw "internal error: a refined call without helpers"
  let some ty := (← get).Γ[y]? | throw "internal error: a refined call's receiver"
  let σs ← rs.mapM infer
  let k ← newSite wide
  let cf := childF k
  let w ← freshT wide
  let own : Callee := { c with resumeFn, cancelFn := some cancelFn, passFields := [] }
  modify fun st => { st with sites := st.sites.push { id := k, waits := .callee k own w [], defers := st.defers } }
  let isR : Expr := .heap (.isTag us) [.local 0]
  let n := rs.length
  let via (body : Expr) (ps : List VTy) (τ : VTy) : M Nat := do
    let i := (← get).vias.size
    modify fun st => { st with vias := st.vias.push (body, ps, τ) }
    return env.viaBase + i
  let arriveV ← via (.ite isR (.call arriveFn ((List.range (n + 3)).map Expr.local)) (.prim .userErr []))
    (ty :: σs ++ [wide, .ref [env.schedTag] []]) wide
  let st ← freshT .int
  let arrive : Expr := .ite (← seeking) vd (seqVoid [
    fset cf (.call arriveV (.local y :: rs ++ [fget cf, .local schS])),
    fset env.pcFld (int k)])
  let poll : Expr := seqVoid [.assign w (fget cf),
    .assign st (.ite (.heap (.isTag [c.tag]) [.local w]) (.call resumeFn [.local w, .local schS]) (.prim .userErr []))]
  let pend : Expr := .ite (.prim .eq [.local st, int 0]) (.seq spillMark (.ret (int 0))) vd
  let found : Expr := .assign env.rS (int 0)
  match c.resField, valued with
  | some _, true =>
    let some τ := env.expTy | throw "internal error: a refined call's value has no expected type"
    let takeV ← via (.ite isR (.call takeFn [.local 0, .local 1]) (.prim .userErr [])) [ty, wide] τ
    return (seqVoid [arrive, found, poll, pend], .call takeV [.local y, .local w])
  | _, _ => return (seqVoid [arrive, found, poll, pend], vd)

/-- `suspendSelf` for a generic callee (an override with type parameters of
    its own or of its class, #171): its frame is kept as any generic
    callee's, at the type arguments the dispatch gives (the receiver's,
    refined by the tested classes' pins, matched against the callee's
    parameters as the checker does). -/
partial def suspendSelfGeneric (us : List Nat) (y g : Nat) (c : Callee) (rs : List Expr) (valued : Bool) :
    M (Expr × Expr) := do
  let env ← read
  let some ty := (← get).Γ[y]? | throw "internal error: a refined call's receiver"
  let .ref _ a := ty | throw "internal error: a refined call's receiver type"
  let some (ps, _) := env.S.fns[g]? | throw "internal error: a refined call's callee"
  let σs ← rs.mapM infer
  -- (the callee's type arguments: its parameters matched against the
  -- receiver and arguments as refined by the pins)
  -- (as the checker opens them, #209: the arguments the pins mention
  -- beyond the receiver's, as fresh variables)
  let k := openCount env.S us a.length
  let N := max (VTy.nvarsL a) (VTy.nvarsL σs)
  let a' := a ++ VTy.ext N k
  let μ := (unify (VTy.pinEqs (commonPins env.S us (a.length + k)) a')).getD VTy.var
  let acc := VTy.bindVarsL ps ((VTy.ref us a' :: σs).map (VTy.subst μ)) []
  let frameTy : VTy := .ref [c.tag] ((List.range c.ntp).map VTy.var)
  if frameTy.unbound acc then
    throw "a <suspends> method whose type parameters the call does not determine cannot be dispatched to a class that fixes type arguments yet (#171)"
  let .ref _ fargs := frameTy.subst (callInst acc .void none)
    | throw "internal error: a refined call's frame type"
  if !VTy.varsBelowL N fargs then
    throw "a <suspends> method of a class with type parameters that only its parent's type arguments determine cannot be dispatched to yet: its frame would need them (#209)"
  suspendSelf us y c rs valued (.ref [c.tag, env.nilTag] fargs)

/-- The statement of a `sync` (`isSync`) or `race` with arms `arms` (each
    a statement that leaves the arm's value in a slot). -/
partial def concAt (isSync : Bool) (arms : List Expr) (isRush : Bool := false) : M Expr := do
  let k ← newSite .int
  let env ← read
  let defersHere := (← get).defers
  -- (a `rush`'s arms each get a wrapper, as a `branch`, for its losers to
  -- go on as tasks; their numbers and fields are taken first)
  let mut rushW : Array (Nat × Nat × Nat × Nat × Nat × Nat) := #[]
  -- (and each is numbered when it starts, at the `rush`, #187)
  let mut numbers : Array Expr := #[]
  if isRush then
    for _ in arms do
      let i := (← get).branchNext
      modify fun st => { st with branchNext := i + 1, branchArms := st.branchArms.push (0, 0, false) }
      let some (startFn, stopFn, wrapTag) := env.branches[i]? | throw "internal error: branches miscounted"
      let site := (← get).next + 1
      modify fun st => { st with next := site, children := st.children.push (.ref [wrapTag, env.schedTag] []) }
      let (sk, number) ← startNumber
      numbers := numbers.push number
      rushW := rushW.push (i, startFn, stopFn, wrapTag, site, sk)
  -- each arm, a region of its own
  let mut info : Array (Nat × Nat × Nat × Nat) := #[]
  -- (the entries of `kills` each arm's own code adds, #254)
  let mut ranges : Array (Nat × Nat) := #[]
  for arm in arms do
    let a := (← get).armsNext
    modify fun st => { st with armsNext := a + 1, arms := st.arms.push (vd, vd) }
    let pcA := armPcF env.sites a
    let doneA := armDoneF env.sites a
    let k0 := (← get).kills.size
    let (res, can) ← region pcA (none) arm
    ranges := ranges.push (k0, (← get).kills.size)
    modify fun st => { st with arms := st.arms.set! a (res, can) }
    info := info.push (env.fnBase + 2 * a, env.fnBase + 2 * a + 1, pcA, doneA)
  modify fun st => { st with sites := st.sites.push { id := k, waits := .arms info.toList, defers := defersHere } }
  let args ← armArgs
  let st ← freshT .int
  let arrive : Expr := .ite (← seeking) vd (seqVoid
    (info.toList.flatMap (fun (_, _, pcA, doneA) => [fset pcA (int 0), fset doneA (int 0)]) ++ numbers.toList ++
      [fset env.pcFld (int k)]))
  let found : Expr := .assign env.rS (int 0)
  -- an arm that gives 2 makes the function return: the other arms that
  -- started and are pending are cancelled (last first), the defers active
  -- here run, then the function's branches stop and it gives 1, or (in an
  -- arm) this arm gives 2 in turn
  let returning : Expr := seqVoid (
    info.toList.reverse.map (fun (_, can, pcA, doneA) =>
      Expr.ite (allOf [.prim .ne [fget pcA, int 0], .prim .eq [fget doneA, int 0]])
        (.seq (seqVoid [.call can args, fset doneA (int 2)]) vd) vd) ++
    [defersHere, if env.pcFld == pcF then .seq killMark (.ret (int 1)) else .ret (int 2)])
  let run (res doneA : Nat) : Expr := seqVoid [spillMark, .assign st (.call res args),
    .ite (.prim .eq [.local st, int 1]) (.seq (fset doneA (int 1)) vd) vd,
    .ite (.prim .eq [.local st, int 2]) (.seq (seqVoid [fset doneA (int 1), returning]) vd) vd, reloadMark]
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
      for (((res, can, pcA, doneA), (i, startFn, stopFn, wrapTag, site, sk)), j) in (info.toList.zip rushW.toList).zipIdx do
        let y ← freshT (.ref [wrapTag, env.schedTag] [])
        modify fun st => { st with kills := st.kills.push (childF site, wrapTag, stopFn, y, pcA, doneA, can, sk) }
        -- (the branches and `rush` arms this arm starts are stopped with it)
        let (lo, hi) := ranges.getD j (0, 0)
        modify fun st => ownKills st lo hi (st.kills.size - 1)
        modify fun st => { st with branchArms := st.branchArms.set! i (res, doneA, false) }
        goOn := goOn.push (Expr.ite (allOf [.prim .ne [.local w, int j], .prim .ne [fget pcA, int 0], .prim .eq [fget doneA, int 0]])
          (.seq (fset (childF site) (.call startFn [.local schS, fr])) vd) vd)
      return seqVoid ([arrive, found, .assign w (int (-1))] ++ polls ++ [wait] ++ goOn.toList)
    -- the winner cancels the arms that started and are pending, last first
    let cancels := info.toList.zipIdx.reverse.map fun ((_, can, pcA, doneA), i) =>
      Expr.ite (allOf [.prim .ne [.local w, int i], .prim .ne [fget pcA, int 0], .prim .eq [fget doneA, int 0]])
        (.seq (seqVoid [spillMark, .call can args, reloadMark, fset doneA (int 2)]) vd) vd
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
  let stmts ← withReader (fun e => { e with pcFld, rS, regionTotal, inArmR := pcFld != pcF }) (block body done)
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
          -- (the child's frame, as `suspendAt` reads it: through a slot of
          -- its field's type, and with its parameters from the caller's
          -- slots or, for a generic one, from its frame)
          let pass := if c.passFields.isEmpty then [] else as.map Expr.local
          .seq (.assign y (fget (childF k)))
            (.seq (.ite (.heap (.isTag [c.tag]) [.local y]) (.call cf (.local y :: .local schS :: pass)) vd) vd)
        | none => vd
      -- (each marked cancelled, 2, so that stopping a `rush`'s arm wrappers
      -- after does not cancel it again, #181)
      | .arms as => seqVoid (as.reverse.map fun (_, can, pcA, doneA) =>
          .ite (allOf [.prim .ne [fget pcA, int 0], .prim .eq [fget doneA, int 0]])
            (.seq (seqVoid [spillMark, .call can args, reloadMark, fset doneA (int 2)]) vd) vd)
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

/-- The functions among `isT` that `e` calls in `Typed.dispatch`'s shape. -/
partial def dispatchTargets (isT : Nat → Bool) : Expr → List Nat
  | .ite (.heap (.isTag _) [.local y]) (.call g (.local y' :: es)) e =>
    (if y == y' && isT g then [g] else []) ++ (es.map (dispatchTargets isT)).flatten ++ dispatchTargets isT e
  | .assign _ e | .ret e | .print e | .loop e => dispatchTargets isT e
  | .forE _ it f b => dispatchTargets isT it ++ dispatchTargets isT f ++ dispatchTargets isT b
  | .seq a b => dispatchTargets isT a ++ dispatchTargets isT b
  | .prim _ es | .call _ es | .heap _ es => (es.map (dispatchTargets isT)).flatten
  | .ite c t e => dispatchTargets isT c ++ dispatchTargets isT t ++ dispatchTargets isT e
  | _ => []

/-- (#179) `e` with each test in `Typed.dispatch`'s shape (a refined call,
    #142, or a #157 field accessor) whose receiver slot is kept in the frame
    (`resident`) made a call of a helper whose first parameter is the
    receiver, `via(recv, args…) = if (isTag us [local 0]) then f(local 0,
    args…) else userErr`, typed at the type `exp` the value is checked
    against: once the slot is a frame field, the test would lose the rule's
    shape. The helpers (body, parameter types, result type) are collected,
    numbered from `base`. -/
partial def fixRefined (S : Sigs) (Γ : Array VTy) (ρ : VTy) (resident : Nat → Bool) (base : Nat)
    (exp : Option VTy) : Expr → StateM (Array (Expr × List VTy × VTy)) Expr
  | .ite c@(.heap (.isTag us) [.local y]) (.call f (.local y' :: es)) e => do
    let e' ← fixRefined S Γ ρ resident base exp e
    let es' ← es.mapM (fixRefined S Γ ρ resident base none)
    let keep : Expr := .ite c (.call f (.local y' :: es')) e'
    if y != y' || !resident y then return keep
    match exp, Γ[y]?, es'.mapM (fun a => tc S Γ.toList ρ a none) with
    | some τ, some ty, some σs =>
      let i := (← get).size
      let n := es'.length
      modify (·.push (.ite (.heap (.isTag us) [.local 0]) (.call f ((List.range (n + 1)).map Expr.local))
        (.prim .userErr []), ty :: σs, τ))
      return .ite c (.call (base + i) (.local y :: es')) e'
    | _, _, _ => return keep
  | .assign i x => return .assign i (← fixRefined S Γ ρ resident base (Γ[i]?) x)
  | .heap (.set k) [.local 0, v] => do
    let v' ← fixRefined S Γ ρ resident base (if k == resF then some ρ else none) v
    return .heap (.set k) [.local 0, v']
  | .seq a b => return .seq (← fixRefined S Γ ρ resident base none a) (← fixRefined S Γ ρ resident base exp b)
  | .ite c t e => do
    let c' ← fixRefined S Γ ρ resident base none c
    let t' ← fixRefined S Γ ρ resident base exp t
    let e' ← fixRefined S Γ ρ resident base exp e
    return .ite c' t' e'
  | .call f es => return .call f (← es.mapM (fixRefined S Γ ρ resident base none))
  | .prim p es => return .prim p (← es.mapM (fixRefined S Γ ρ resident base none))
  | .heap op es => return .heap op (← es.mapM (fixRefined S Γ ρ resident base none))
  | .ret x => return .ret (← fixRefined S Γ ρ resident base none x)
  | .print x => return .print (← fixRefined S Γ ρ resident base none x)
  | .loop x => return .loop (← fixRefined S Γ ρ resident base none x)
  | .forE i it f b => do
    let it' ← fixRefined S Γ ρ resident base none it
    let f' ← fixRefined S Γ ρ resident base none f
    let b' ← fixRefined S Γ ρ resident base none b
    return .forE i it' f' b'
  | x => return x

/-- The element slots of the `for`s in `e`. -/
partial def forBinders : Expr → List Nat
  | .forE i it f b => i :: forBinders it ++ forBinders f ++ forBinders b
  | .assign _ e | .ret e | .print e | .loop e => forBinders e
  | .seq a b => forBinders a ++ forBinders b
  | .prim _ es | .call _ es | .heap _ es => (es.map forBinders).flatten
  | .ite c t e => forBinders c ++ forBinders t ++ forBinders e
  | _ => []

/-- The slots `e` assigns. -/
partial def assignsIn : Expr → List Nat
  | .assign j e => j :: assignsIn e
  | .ret e | .print e | .loop e => assignsIn e
  | .seq a b => assignsIn a ++ assignsIn b
  | .prim _ es | .call _ es | .heap _ es => (es.map assignsIn).flatten
  | .ite c t e => assignsIn c ++ assignsIn t ++ assignsIn e
  | .forE _ it f b => assignsIn it ++ assignsIn f ++ assignsIn b
  | _ => []

/-- `e` with the slots `fld` maps read and written in the frame's fields.
    A condition (or a `for`'s filter) that assigns such a slot works on the
    slot itself, loaded from the field first, and the field is written
    once the condition holds: a heap write in a condition makes the
    reference interpreter keep the heap as it was, for the rollback, and so
    copy it (#225). A condition cannot suspend, so the slot holds the
    value throughout. -/
partial def toFields (fld : Nat → Option Nat) : Expr → Expr
  | .local j => match fld j with
    | some f => fget f
    | none => .local j
  | .assign j e => match fld j with
    | some f => fset f (toFields fld e)
    | none => .assign j (toFields fld e)
  | .forE i it f b =>
    let (load, f', store) := inCond fld f
    .forE i (toFields fld it) (seqWith load f') (seqWith store (toFields fld b))
  | .seq a b => .seq (toFields fld a) (toFields fld b)
  | .prim p es => .prim p (es.map (toFields fld))
  | .call g es => .call g (es.map (toFields fld))
  | .heap op es => .heap op (es.map (toFields fld))
  | .ite c t e =>
    let (load, c', store) := inCond fld c
    .ite (seqWith load c') (seqWith store (toFields fld t)) (toFields fld e)
  | .loop b => .loop (toFields fld b)
  | .ret e => .ret (toFields fld e)
  | .print e => .print (toFields fld e)
  | e => e
where
  /-- A condition with the frame slots it assigns kept in their slots: the
      loads before it, it, and the stores after it. -/
  inCond (fld : Nat → Option Nat) (c : Expr) : List Expr × Expr × List Expr :=
    let mine := (assignsIn c).eraseDups.filterMap fun j => (fld j).map (j, ·)
    let fld' : Nat → Option Nat := fun j => if mine.any (·.1 == j) then none else fld j
    (mine.map (fun (j, f) => .assign j (fget f)), toFields fld' c, mine.map fun (j, f) => fset f (.local j))
  seqWith (pre : List Expr) (e : Expr) : Expr := pre.foldr (fun a acc => .seq a acc) e

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
  /-- The refined calls' helpers (#171): each one's body, parameter types and
      result type, after the arms' functions. -/
  vias : List (Expr × List VTy × VTy) := []

/-- Lower the body `b` (initialisations stripped) of a suspends function
    with `arity` parameters, slot types `Γ` and result type `ρ`, whose frame
    type is `frameTy`; its arm functions are numbered from `fnBase`, then its
    refined calls' helpers. -/
def lower (S : Sigs) (callee : Nat → Option Callee) (syncMark raceMark rushMark spawnMark : Nat) (spawns : Array (Nat × Nat))
    (branchMark : Nat) (branches : Array (Nat × Nat × Nat))
    (arity : Nat) (Γ : List VTy) (ρ : VTy) (frameTy : VTy) (schedTag nilTag : Nat) (fnBase : Nat) (b : Expr) :
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
  let env : Env := { S, ρ, callee, syncMark, raceMark, rushMark, arity, sites, armsTotal, fnBase, schedTag, nilTag, spawnMark, spawns,
                     branchMark, branches, viaBase := fnBase + 2 * armsTotal, expTy := some ρ,
                     pcFld := pcF, rS := 0, regionTotal := 0 }
  let done : Expr → Expr := fun v => .seq (fset resF v) (.seq killMark (.ret (int 1)))
  let ((res, can), st) ← ((region pcF (some done) b).run env).run { Γ := Γ0, trans := trans0 }
  if st.next != sites || st.armsNext != armsTotal then
    throw "internal error: lowering a <suspends> function: suspension points miscounted"
  let base := slotBaseOf sites armsTotal
  -- stopping the branches: each wrapper marked done (through a test of its
  -- class), each arm still pending cancelled and marked dead
  let args : List Expr := [fr, .local schS] ++ (List.range arity).map fun i => .local (i + 2)
  -- (last started first, by their start numbers, each cleared once it is
  -- stopped, #187: a loop picking the highest, in two transient slots)
  let bestS := st.Γ.size
  let whichS := bestS + 1
  let entries := st.kills.toList.zipIdx
  -- (only in a function that has some, so that the others' frames stay as
  -- they were)
  let st := if entries.isEmpty then st else
    { st with Γ := st.Γ ++ #[VTy.int, VTy.int], trans := st.trans ++ #[true, true] }
  let pick : List Expr := [.assign bestS (int 0), .assign whichS (int (-1))] ++ entries.map fun ((_, _, _, _, _, _, _, sk), j) =>
    .ite (.prim .lt [.local bestS, .local sk]) (.seq (seqVoid [.assign bestS (.local sk), .assign whichS (int (j : Nat))]) vd) vd
  let stopOne : List Expr := entries.map fun ((wf, wrapTag, stopFn, y, pcA, doneA, can, sk), j) =>
    .ite (.prim .eq [.local whichS, int (j : Nat)]) (.seq (seqVoid [.assign y (fget wf),
      .ite (.heap (.isTag [wrapTag]) [.local y]) (.call stopFn [.local y, .local schS]) vd,
      .ite (allOf [.prim .ne [fget pcA, int 0], .prim .eq [fget doneA, int 0]])
        (.seq (seqVoid [.call can args, fset doneA (int 2)]) vd) vd,
      .assign sk (int 0)]) vd) vd
  -- (#254: each stopped with what its own code started, which goes first,
  -- also last started first, so that each unwinds whole; the function's
  -- own last started first among them. Only where some are nested, so that
  -- the other functions' code stays as it was)
  let ownerOf (i : Nat) : Option Nat := (st.killOwner.find? (·.1 == i)).map (·.2)
  let stopBody (j : Nat) : Expr :=
    let (wf, wrapTag, stopFn, y, pcA, doneA, can, sk) := st.kills[j]!
    seqVoid [.assign y (fget wf),
      .ite (.heap (.isTag [wrapTag]) [.local y]) (.call stopFn [.local y, .local schS]) vd,
      .ite (allOf [.prim .ne [fget pcA, int 0], .prim .eq [fget doneA, int 0]])
        (.seq (seqVoid [.call can args, fset doneA (int 2)]) vd) vd,
      .assign sk (int 0)]
  -- (a loop that picks the last started among `ids`, stops it and what it
  -- started, until none is left; one `else` chain, as the slots are shared)
  let rec loopOver (fuel : Nat) (ids : List Nat) : Expr :=
    match fuel with
    | 0 => vd
    | fuel + 1 =>
      let pickAmong : List Expr := [.assign bestS (int 0), .assign whichS (int (-1))] ++ ids.map fun j =>
        let sk := (st.kills[j]!).2.2.2.2.2.2.2
        .ite (.prim .lt [.local bestS, .local sk]) (.seq (seqVoid [.assign bestS (.local sk), .assign whichS (int j)]) vd) vd
      let dispatch : Expr := ids.foldr (fun j acc =>
        let kids := (List.range st.kills.size).filter (ownerOf · == some j)
        let stopTree := if kids.isEmpty then stopBody j else .seq (loopOver fuel kids) (stopBody j)
        .ite (.prim .eq [.local whichS, int j]) (.seq stopTree vd) acc) vd
      .seq (.loop (seqVoid (pickAmong ++ [.ite (.prim .eq [.local whichS, int (-1)]) .brk vd, dispatch]))) vd
  let kill : Expr := if entries.isEmpty then vd
    else if !st.killOwner.isEmpty then
      loopOver (st.kills.size + 1) ((List.range st.kills.size).filter (ownerOf · == none))
    else
    .seq (.loop (seqVoid (pick ++ [.ite (.prim .eq [.local whichS, int (-1)]) .brk vd] ++ stopOne))) vd
  -- the slots kept across suspension points live in the frame: their reads
  -- and writes become the frame's (so nothing is stored or reloaded), except
  -- a `for`'s element slot, bound by the `for` itself; each function then
  -- keeps only the transient slots it uses, renumbered after its parameters
  let residentIn (e : Expr) (j : Nat) : Bool :=
    j ≥ 2 + arity && !((st.trans[j]?).getD false) && !(forBinders e).contains j
  -- (the refined tests on slots that become frame fields go through helpers
  -- of their own, after the refined suspending calls', #179)
  let prep (e : Expr) : StateM (Array (Expr × List VTy × VTy)) Expr :=
    let e := fill vd vd kill e
    fixRefined S st.Γ ρ (residentIn e) (env.viaBase + st.vias.size) none e
  let ((res, can, arms), more) := (do
      let r ← prep res
      let c ← prep can
      let as ← st.arms.toList.mapM fun (r, c) => do return (← prep r, ← prep c)
      return (r, c, as) : StateM _ _).run #[]
  let finish (e : Expr) : LFn :=
    let resident := residentIn e
    let e := toFields (fun j => if resident j then some (base + (j - 2)) else none) e
    let used := ((slotsOf e).filter (· ≥ 2 + arity)).eraseDups.mergeSort
    let ren (j : Nat) : Nat := if j < 2 + arity then j else 2 + arity + ((used.idxOf? j).getD 0)
    { body := renumber ren e, slots := st.Γ.toList.take (2 + arity) ++ used.map fun j => (st.Γ[j]?).getD .int }
  return { body := finish res, cancel := finish can, arms := arms.map fun (r, c) => (finish r, finish c),
           branchArms := st.branchArms.toList, vias := st.vias.toList ++ more.toList,
           fields := [.int, ρ] ++ st.children.toList ++ List.replicate (2 * armsTotal) .int ++
             (st.Γ.toList.drop 2) }

end OpenVerse.Front.Suspend
