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
  /-- The frame fields `resume` takes after the frame and the scheduler. -/
  passFields : List Nat
  /-- The frame's `?result` field; none when the call's value is `void`. -/
  resField : Option Nat
  deriving Inhabited

/-- Slots of a resume function: the frame, the scheduler. -/
def frS : Nat := 0
def schS : Nat := 1

/-- Frame fields: the suspension point the frame is at (0: not started),
    the result, then one `?frame` per suspension point, then the slots. -/
def pcF : Nat := 0
def resF : Nat := 1
def childF (k : Nat) : Nat := 2 + (k - 1)
def slotF (total j : Nat) : Nat := 2 + total + (j - 2)

/-- A placeholder for "store every slot in the frame", filled in once the
    number of slots is known. -/
def spillMark : Expr := .heap (.get 1000000007) []

def int (i : Int) : Expr := .lit (.int i)
def vd : Expr := .lit .void
def fr : Expr := .local frS
def pcE : Expr := .heap (.get pcF) [fr]

/-- Statements in sequence, of type `void`. -/
def seqVoid (ss : List Expr) : Expr := ss.foldr .seq vd

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
  | .ret e => .seq (.heap (.set resF) [fr, .prim .mkSome [retToDone e]]) (.ret (int 1))
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

/-- Whether `e` contains a call of a suspends function. -/
partial def hasSusp (isS : Nat → Bool) : Expr → Bool
  | .call f es => isS f || es.any (hasSusp isS)
  | .assign _ e | .ret e | .print e | .loop e => hasSusp isS e
  | .seq a b => hasSusp isS a || hasSusp isS b
  | .prim _ es | .heap _ es => es.any (hasSusp isS)
  | .ite c t e => hasSusp isS c || hasSusp isS t || hasSusp isS e
  | .forE _ it f b => hasSusp isS it || hasSusp isS f || hasSusp isS b
  | _ => false

/-- The number of calls of suspends functions in `e`. -/
partial def countSusp (isS : Nat → Bool) : Expr → Nat
  | .call f es => (if isS f then 1 else 0) + (es.map (countSusp isS)).sum
  | .assign _ e | .ret e | .print e | .loop e => countSusp isS e
  | .seq a b => countSusp isS a + countSusp isS b
  | .prim _ es | .heap _ es => (es.map (countSusp isS)).sum
  | .ite c t e => countSusp isS c + countSusp isS t + countSusp isS e
  | .forE _ it f b => countSusp isS it + countSusp isS f + countSusp isS b
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

structure Env where
  /-- The signatures, for inferring types: each suspends function's own,
      and its `new` and `init`. -/
  S : Sigs
  /-- The function's result type. -/
  ρ : VTy
  callee : Nat → Option Callee
  /-- Calls of suspends functions in the function. -/
  total : Nat
  /-- The flag that is set while seeking the suspension point to resume at. -/
  rS : Nat

structure St where
  /-- The resume function's slot types. -/
  Γ : Array VTy
  /-- Suspension points numbered so far, in order (from 1). -/
  next : Nat := 0
  /-- Each suspension point's child frame field type (`?frame`). -/
  children : Array VTy := #[]

abbrev M := ReaderT Env (StateT St (Except String))

def fresh (τ : VTy) : M Nat :=
  modifyGet fun st => (st.Γ.size, { st with Γ := st.Γ.push τ })

def infer (e : Expr) : M VTy := do
  let env ← read
  match tc env.S (← get).Γ.toList env.ρ e none with
  | some τ => pure τ
  | none => throw "internal error: lowering a <suspends> function: cannot infer the type of a value kept across a suspension point"

def isCallee (f : Nat) : M Bool := return ((← read).callee f).isSome

def hasS (e : Expr) : M Bool := do
  let env ← read
  return hasSusp (fun f => (env.callee f).isSome) e

/-- `lo ≤ pc ≤ hi`, as a condition. -/
def inRange (lo hi : Nat) : Expr :=
  .seq (.prim .le [int lo, pcE]) (.prim .le [pcE, int hi])

/-- Run `prod`, a statement, and guard it so that it is skipped while
    seeking a suspension point outside it. No guard is needed when no
    suspension point follows it. -/
def emitWith (prod : M (Expr × α)) : M (Expr × α) := do
  let lo := (← get).next + 1
  let (s, x) ← prod
  let hi := (← get).next
  let env ← read
  if hi < env.total then
    let seeking := Expr.prim .eq [.local env.rS, int 1]
    let run : Expr :=
      if lo ≤ hi then .ite seeking (.ite (inRange lo hi) (int 1) (int 0)) (int 1)
      else .ite seeking (int 0) (int 1)
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

mutual
/-- The statements of `e`, each guarded, with the continuation `k` applied
    to its value (none: the value is discarded). -/
partial def block (e : Expr) (k : Option (Expr → Expr)) : M (List Expr) := do
  if !(← hasS e) then return [← emit (pure (app k e))]
  match e with
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
      let env ← read
      let sel : Expr := .ite (.prim .eq [.local env.rS, int 1])
        (.ite (inRange lo mid) (int 1) (int 0)) (.ite c (int 1) (int 0))
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
      return pre ++ [← emit (pure (app k (.forE i (.local a) filt body)))]
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
    let (pre, rs) ← operands es
    match (← read).callee g with
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
  | .ret e1 => block e1 (some (.ret ·))
  | e => return [← emit (pure (app k e))]

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
      if i > j || (i < j && stable e) then rs := rs.push e
      else
        let t ← fresh (← infer e)
        pre := pre ++ (← block e (some (.assign t ·)))
        rs := rs.push (.local t)
    return (pre.toList, rs.toList)

/-- The statement of suspension point `k`: on arrival, make (or reset) the
    callee's frame with arguments `rs`; then resume it; if it is pending,
    store the slots and return 0; else take its result. Gives the
    statement and the call's value. -/
partial def suspendAt (g : Nat) (c : Callee) (rs : List Expr) : M (Expr × Expr) := do
  let k := (← get).next + 1
  modify fun st => { st with next := k }
  let fty ← infer (.call c.newFn rs)
  modify fun st => { st with children := st.children.push (.opt fty) }
  let env ← read
  let cf := childF k
  let q : Expr := .prim .query [.heap (.get cf) [fr]]
  let create : Expr := .ite (.call c.initFn (q :: rs)) vd
    (.seq (.heap (.set cf) [fr, .prim .mkSome [.call c.newFn rs]]) vd)
  let st ← fresh .int
  let arrive : Expr := .ite (.prim .eq [.local env.rS, int 1]) vd
    (.seq create (.seq (.heap (.set pcF) [fr, int k]) vd))
  let poll : Expr := .ite (.assign st (.call c.resumeFn ([q, .local schS] ++ c.passFields.map fun f => .heap (.get f) [q])))
    vd (.seq (.prim .userErr []) vd)
  let pend : Expr := .ite (.prim .eq [.local st, int 0]) (.seq spillMark (.ret (int 0))) vd
  let found : Expr := .assign env.rS (int 0)
  match c.resField with
  | some rf =>
    let t ← fresh (← infer (.call g rs))
    let take : Expr := .ite (.assign t (.prim .query [.heap (.get rf) [q]])) vd (.seq (.prim .userErr []) vd)
    return (seqVoid [arrive, found, poll, pend, take], .local t)
  | none => return (seqVoid [arrive, found, poll, pend], vd)
end

/-- Replace the spill placeholder by stores of slots `2 … n-1`. -/
partial def fillSpill (spill : Expr) : Expr → Expr
  | .heap (.get 1000000007) [] => spill
  | .assign i e => .assign i (fillSpill spill e)
  | .forE i it f b => .forE i (fillSpill spill it) (fillSpill spill f) (fillSpill spill b)
  | .seq a b => .seq (fillSpill spill a) (fillSpill spill b)
  | .prim p es => .prim p (es.map (fillSpill spill))
  | .call f es => .call f (es.map (fillSpill spill))
  | .heap op es => .heap op (es.map (fillSpill spill))
  | .ite c t e => .ite (fillSpill spill c) (fillSpill spill t) (fillSpill spill e)
  | .loop b => .loop (fillSpill spill b)
  | .ret e => .ret (fillSpill spill e)
  | .print e => .print (fillSpill spill e)
  | e => e

/-- A lowered suspends function. -/
structure Lowered where
  /-- `resume`'s body, without its slots' initialisations. -/
  body : Expr
  /-- `resume`'s slot types (frame, scheduler, the function's parameters,
      then its other slots and the temporaries). -/
  slots : List VTy
  /-- The frame's field types. -/
  fields : List VTy

/-- Lower the body `b` (initialisations stripped) of a suspends function
    with slot types `Γ` and result type `ρ`, whose frame type is `frameTy`. -/
def lower (S : Sigs) (callee : Nat → Option Callee) (Γ : List VTy) (ρ : VTy) (frameTy schedTy : VTy)
    (b : Expr) : Except String Lowered := do
  let isS := fun f => (callee f).isSome
  let total := countSusp isS b
  let b := retToDone (shift 2 b)
  let Γ0 := (#[frameTy, schedTy] ++ Γ.toArray).push .int
  let rS := Γ0.size - 1
  let env : Env := { S, ρ, callee, total, rS }
  let done : Expr → Expr := fun v => .seq (.heap (.set resF) [fr, .prim .mkSome [v]]) (.ret (int 1))
  let (stmts, st) ← ((block b (some done)).run env).run { Γ := Γ0 }
  if st.next != total then throw "internal error: lowering a <suspends> function: suspension points miscounted"
  let n := st.Γ.size
  let spill := seqVoid ((List.range (n - 2)).map fun j => .heap (.set (slotF total (j + 2))) [fr, .local (j + 2)])
  let reload := (List.range (n - 2)).map fun j => Expr.assign (j + 2) (.heap (.get (slotF total (j + 2))) [fr])
  let seek : Expr := .assign rS (.ite (.prim .eq [pcE, int 0]) (int 0) (int 1))
  let body := seqVoid (reload ++ [seek] ++ stmts.map (fillSpill spill)) |> fun e => Expr.seq e (int 1)
  return { body, slots := st.Γ.toList,
           fields := [.int, .opt ρ] ++ st.children.toList ++ (st.Γ.toList.drop 2) }

end OpenVerse.Front.Suspend
