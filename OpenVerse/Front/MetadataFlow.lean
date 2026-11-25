/- Compiler-only provenance analysis. Metadata is not a Core runtime tag. -/
import OpenVerse.Front.Syntax
import OpenVerse.Core.Syntax
import OpenVerse.Front.MetadataPlan
import OpenVerse.Front.MetadataReferences
import OpenVerse.Front.MetadataCells
import OpenVerse.Front.MetadataValues
import OpenVerse.Front.MetadataBits
import OpenVerse.Front.MetadataLiveness
import Std.Data.HashMap
import Std.Data.TreeMap

namespace OpenVerse.Front.MetadataFlow
open OpenVerse MetadataBits

/-- Roles collected before witness, capture and concurrency lowering erase
    the distinction between executable values and opaque type metadata. -/
structure Info where
  pos : Pos := { line := 0, col := 0 }
  inputs : List Nat := []
  required : List Nat := []
  /-- Every normal result of this generated helper is type metadata. -/
  metadataResult : Bool := false
  seeds : List Nat := []
  uses : List Nat := []
  shared : List Nat := []
  metadataWrites : List (Nat × Nat) := []
  /-- Exact compiler-owned cell and lazy-transport tags, never user fields. -/
  cellTag : Option Nat := none
  cellTransportTag : Option Nat := none
  cellParams : List Nat := []
  cellSlots : List Nat := []
  nonCellSlots : List Nat := []
  /-- Metadata-only virtual locals; emitted frame sizes are unchanged. -/
  extraSlots : Nat := 0
  /-- Prepared once by check, including shifted graph-call contexts. -/
  nonCellMask : Nat := 0
  /-- Source-certified values containing no heap reference, including containers. -/
  objectFreeSlots : List Nat := []
  objectFreeMask : Nat := 0
  /-- Source-certified typed data graphs have no private-relevant aliases.
      Unlike objectFree, their ordinary runtime object identities remain. -/
  dataOnlySlots : List Nat := []
  dataOnlyMask : Nat := 0
  cellHelper : Bool := false
  source : FrameRefs.Info := {}
  borrowTasks : Bool := false
  body : Option Expr := none
  deriving Inhabited

private abbrev TupleParts := MetadataCells.TupleParts

private def joinParts (a : Option Bool) (ap : TupleParts)
    (b : Option Bool) (bp : TupleParts) : TupleParts :=
  match a, b with
  | none, _ => bp
  | _, none => ap
  | some ar, some br => MetadataCells.joinParts ar ap br bp

private def putParts (parts : Std.HashMap Nat (List MetadataCells.Column)) (i : Nat) (value : TupleParts) :=
  match value with
  | none => parts.erase i
  | some fields => if fields.any (·.role) then parts.insert i fields else parts.erase i

private structure Argument where
  role : Bool := false
  parts : TupleParts := none
  deriving BEq, Hashable, Inhabited, Repr

private structure Slots where
  values : Bits := {}
  tuples : Std.HashMap Nat (List MetadataCells.Column) := {}
  initialized : Bits := {}
  sharedMetadata : Bits := {}
  /-- Writes performed by this arm, excluding roles received from siblings. -/
  written : Bits := {}
  heap : MetadataCells.Memory := {}
  deriving BEq, Inhabited

private def joinSlots (a b : Slots) : Slots := {
  heap := MetadataCells.join a.heap b.heap
  values := a.values.union b.values
  -- Known columns join directly; their whole-value bits carry no extra
  -- information. Only a missing shape needs the other path's opaque role.
  -- Canonical maps omit all-real tuples, so equal maps are their own join.
  tuples := if a.tuples == b.tuples then a.tuples else
    b.tuples.fold (fun out i fields =>
      if a.tuples.contains i || a.values.get i then out else putParts out i (some fields))
      (a.tuples.fold (fun out i fields =>
        let joined := MetadataCells.joinParts (a.values.get i) (some fields)
          (b.values.get i) b.tuples[i]?
        putParts out i joined) {})
  initialized := a.initialized.union b.initialized
  written := a.written.union b.written
  sharedMetadata := a.sharedMetadata.joinModes a.initialized b.sharedMetadata b.initialized }

private def joinOpt (a b : Option Slots) : Option Slots :=
  match a, b with
  | some a, some b => some (joinSlots a b)
  | some a, none | none, some a => some a
  | none, none => none

/-- Forget iteration-local shared-cell modes on back edges. Values and
    nonshared scratch slots retain their usual fixed-point joins. -/
private def freshLocals (shared : List Nat) (entry head : Slots) : Slots :=
  if shared.isEmpty then head else { head with
    initialized := head.initialized.mapIdx fun i ready =>
      ready && ((entry.initialized.get i) || !shared.contains i)
    sharedMetadata := head.sharedMetadata.mapIdx fun i role =>
      if (entry.initialized.get i) || !shared.contains i then role
      else (entry.sharedMetadata.get i) }

private def joinRole (a b : Option Bool) : Option Bool :=
  match a, b with
  | some a, some b => some (a || b)
  | some a, none | none, some a => some a
  | none, none => none

private structure Flow where
  slots : Slots
  value : Option Bool := some false
  valueParts : TupleParts := none
  valueRefs : MetadataCells.Refs := []
  argumentRefs : List MetadataCells.Refs := []
  returned : Option Bool := none
  returnedParts : TupleParts := none
  returnedRefs : MetadataCells.Refs := []
  returnedHeap : Option MetadataCells.Memory := none
  broken : Option Slots := none
  /-- May yield before normal completion or a nonreturning path. -/
  yielded : Bool := false

private def withExits (a b : Flow) : Flow := { b with
  returned := joinRole a.returned b.returned
  returnedRefs := MetadataCells.joinRefs a.returnedRefs b.returnedRefs
  returnedHeap := match a.returnedHeap, b.returnedHeap with
    | some x, some y => some (MetadataCells.join x y)
    | some x, none | none, some x => some x
    | none, none => none
  returnedParts := joinParts a.returned a.returnedParts b.returned b.returnedParts
  broken := joinOpt a.broken b.broken
  yielded := a.yielded || b.yielded }

private abbrev Key := Nat × List Argument

/-- A full scheduled transfer checked executable roles and encountered no
    shared-write diagnostic suppressed during summary solving. -/
private structure ScheduleProof where
  flow : Flow
  calls : Array (Key × Option Bool × TupleParts × Bool)
  seen : Bits
  captureMismatch : Bool
  signalArguments : Option (Array (List Nat))

private structure Summary where
  key : Key
  result : Option Bool := none
  parts : TupleParts := none
  yielded : Bool := false
  dependencies : Array (Nat × Option Bool × TupleParts × Bool) := #[]
  cached : Bool := false
  deriving Inhabited

private inductive ActorStatus where
  | idle | running | ready | waiting (resumable : Bool) | joining (group : Nat) | done
  deriving BEq, Inhabited

private structure LoopCell where
  slot : Nat
  initialized : Bool
  metadata : Bool
  deriving BEq, Inhabited

private def loopCells (shared : List Nat) (slots : Slots) : List LoopCell :=
  shared.eraseDups.map fun i => {
    slot := i, initialized := (slots.initialized.get i)
    metadata := (slots.sharedMetadata.get i) }

private def restoreLoopCells (cells : List LoopCell) (slots : Slots) : Slots :=
  cells.foldl (fun slots cell => if cell.initialized then slots else { slots with
    initialized := slots.initialized.set! cell.slot false
    sharedMetadata := slots.sharedMetadata.set! cell.slot cell.metadata }) slots

private structure LoopEntry where
  id : Nat
  /-- Back edges restore only entry modes of fresh shared cells. Retaining
      scratch values here adds irrelevant facts to the configuration lattice. -/
  cells : List LoopCell
  cleanups : List Nat
  deriving BEq, Inhabited

private structure CallFrame where
  context : Option (Nat × Nat)
  cleanups : List Nat
  loops : List LoopEntry
  deriving BEq, Inhabited

private structure Actor where
  pc : Nat := 0
  status : ActorStatus := .idle
  cleanups : List Nat := []
  loops : List LoopEntry := []
  context : Option (Nat × Nat) := none
  frames : List CallFrame := []
  event : Option MetadataReferences.Refs := none
  canceling : Bool := false
  /-- Stop after an active continuation next suspends. -/
  cancelRequested : Bool := false
  task : Option MetadataReferences.Refs := none
  taskWait : Bool := false
  waitDst : Option Nat := none
  signalReturns : List (Option Nat) := []
  canComplete : Bool := false
  canSignal : Bool := false
  deriving BEq, Inhabited

private structure GroupStatus where
  /-- A branch launched after its cancellation tree was stopped can still
      run in the current runtime; retain its effects after that stop. -/
  late : Bool := false
  active : Bool := false
  started : Nat := 0
  winner : Option Nat := none
  deriving BEq, Inhabited

private inductive Pending where
  | cancel (actor : Nat)
  | cleanup (actor : Nat) (context : Option (Nat × Nat)) (entry : Nat)
  | stop (actor : Nat)
  | resume (actor pc : Nat)
  | returnCall (actor next : Nat)
  | returnScope (actor fn offset dropFrames next : Nat)
  | result (role : Bool) (parts : TupleParts) (slot : Option Nat := none)
  | discard
  deriving BEq, Inhabited

/-- Multiple live starts at one spawn site share a finite effect summary.
    Their own metadata contexts remain independently validated. -/
private structure Pool where
  task : MetadataReferences.Refs := []
  owners : MetadataReferences.Refs := []
  events : MetadataReferences.Refs := []
  tasks : MetadataReferences.Refs := []
  canComplete : Bool := false
  canSignal : Bool := false
  progressed : Bool := false
  deriving BEq, Inhabited

private structure Snapshot where
  owner : Nat
  no : Nat
  slots : Slots
  refs : MetadataReferences.Memory
  actors : Array Actor
  groups : Array GroupStatus
  startup : List Nat
  events : List Nat
  pending : List Pending
  launches : List Nat
  tasks : Std.HashMap Nat (List Nat)
  taskResults : Std.HashMap Nat MetadataReferences.Refs
  pools : Std.HashMap Nat Pool
  signals : List Nat
  deriving BEq, Inhabited

private structure Configuration where
  slots : Slots
  refs : MetadataReferences.Memory
  actors : Array Actor
  groups : Array GroupStatus
  current : Option Nat := some 0
  startup : List Nat := []
  events : List Nat := []
  pending : List Pending := []
  tests : List Snapshot := []
  launches : List Nat := []
  tasks : Std.HashMap Nat (List Nat) := {}
  taskResults : Std.HashMap Nat MetadataReferences.Refs := {}
  pools : Std.HashMap Nat Pool := {}
  signals : List Nat := []
  deriving BEq, Inhabited

private def appendKeyList (key : Array Nat) (values : List Nat) : Array Nat :=
  values.foldl Array.push (key.push values.length)

private def appendContextKey (key : Array Nat) : Option (Nat × Nat) → Array Nat
  | none => key.push 0
  | some (fn, offset) => key.push (fn + 1) |>.push offset

private def appendLoopsKey (key : Array Nat) (loops : List LoopEntry) : Array Nat :=
  loops.foldl (fun key loop => appendKeyList (key.push loop.id) loop.cleanups)
    (key.push loops.length)

private def appendActorsKey (key : Array Nat) (actors : Array Actor) : Array Nat :=
  actors.foldl (fun key a => Id.run do
    let (tag, data) := match a.status with
      | .idle => (0, 0) | .running => (1, 0) | .ready => (5, 0)
      | .waiting ready => (2, ready.toNat)
      | .joining g => (3, g) | .done => (4, 0)
    let key := key.push a.pc |>.push tag |>.push data |>.push a.canceling.toNat
      |>.push a.cancelRequested.toNat |>.push a.taskWait.toNat
    let key := appendKeyList key a.cleanups |>.push (a.waitDst.map (· + 1) |>.getD 0)
      |>.push a.canComplete.toNat |>.push a.canSignal.toNat |>.push a.signalReturns.length
    let key := a.signalReturns.foldl (fun key pc => key.push (pc.map (· + 1) |>.getD 0)) key
    let key := appendContextKey (appendLoopsKey key a.loops) a.context
    return a.frames.foldl (fun key f =>
      appendLoopsKey (appendKeyList (appendContextKey key f.context) f.cleanups) f.loops)
      (key.push a.frames.length)) key

private def appendGroupsKey (key : Array Nat) (groups : Array GroupStatus) : Array Nat :=
  groups.foldl (fun key g => key.push g.late.toNat |>.push g.active.toNat
    |>.push g.started |>.push (g.winner.map (· + 1) |>.getD 0)) key

private partial def appendTupleKey (key : Array Nat) (parts : TupleParts) : Array Nat :=
  match parts with
  | none => key.push 0
  | some fields => fields.foldl (fun key field =>
      appendTupleKey (key.push field.role.toNat) field.parts) (key.push 1 |>.push fields.length)

private def appendPendingKey (key : Array Nat) (pending : List Pending) : Array Nat :=
  pending.foldl (fun key => fun
    | .cancel a => key.push 0 |>.push a
    | .cleanup a ctx pc => appendContextKey (key.push 1 |>.push a |>.push pc) ctx
    | .stop a => key.push 2 |>.push a
    | .resume a pc => key.push 3 |>.push a |>.push pc
    | .returnCall a pc => key.push 4 |>.push a |>.push pc
    | .returnScope a f o n pc => key.push 7 |>.push a |>.push f |>.push o |>.push n |>.push pc
    | .result role parts slot =>
      let key := appendTupleKey (key.push 5 |>.push role.toNat) parts
      match slot with
      | none => key.push 0
      | some value => key.push 1 |>.push value
    | .discard => key.push 6) (key.push pending.length)

/-- Encode control and continuation fields in one buffer. The scheduler joins
    provenance facts only after every field in this key compares equal. -/
private def configurationKey (c : Configuration) : Array Nat := Id.run do
  let key := Array.emptyWithCapacity (1 + 16 * c.actors.size + 4 * c.groups.size)
  let key := (key : Array Nat).push (c.current.getD c.actors.size)
  let key := appendKeyList (appendKeyList key c.startup) c.events
  let key := appendGroupsKey (appendActorsKey key c.actors) c.groups
  let key := appendKeyList (appendKeyList key c.signals) c.launches
  let key := appendPendingKey key c.pending |>.push c.tests.length
  return c.tests.foldl (fun key t =>
    let key := appendKeyList (appendKeyList (key.push t.owner |>.push t.no) t.startup) t.events
    let key := appendGroupsKey (appendActorsKey key t.actors) t.groups
    let key := appendKeyList (appendKeyList key t.signals) t.launches
    appendPendingKey key t.pending) key

private def joinLoops (a b : List LoopEntry) : List LoopEntry :=
  a.zipWith (fun s t => { t with cells := s.cells.zipWith (fun x y => { y with
    initialized := x.initialized || y.initialized
    metadata := if !x.initialized then y.metadata else if !y.initialized then x.metadata
      else x.metadata && y.metadata }) t.cells }) b

private def joinActors (a b : Array Actor) : Array Actor :=
  a.zipWith (fun x y => { y with
    task := match x.task, y.task with
      | some a, some b => some ((a ++ b).mergeSort (· ≤ ·) |>.eraseDups)
      | some a, none | none, some a => some a
      | none, none => none
    event := match x.event, y.event with
      | some a, some b => some ((a ++ b).mergeSort (· ≤ ·) |>.eraseDups)
      | some a, none | none, some a => some a
      | none, none => none
    loops := joinLoops x.loops y.loops
    frames := x.frames.zipWith (fun s t => { t with loops := joinLoops s.loops t.loops }) y.frames }) b

private def unionRefs (a b : List Nat) : List Nat :=
  (a ++ b).mergeSort (· ≤ ·) |>.eraseDups

private def joinTable (a b : Std.HashMap Nat (List Nat)) (missing : List Nat) :
    Std.HashMap Nat (List Nat) :=
  (a.keys ++ b.keys).eraseDups.foldl (fun result k =>
    result.insert k (unionRefs (a[k]?.getD missing) (b[k]?.getD missing))) {}

private def taskOptions (c : Configuration) (refs : MetadataReferences.Refs) : List Nat :=
  refs.foldl (fun options reference =>
    unionRefs options (c.tasks[reference]?.getD [1, 2, 4])) []

private def setTask (c : Configuration) (refs : MetadataReferences.Refs) (state : Nat)
    (result : Option MetadataReferences.Refs := none) : Configuration := Id.run do
  let mut tasks := c.tasks
  let mut results := c.taskResults
  for reference in (refs ++ tasks.keys).eraseDups do
    if !MetadataReferences.aliases refs [reference] then continue
    if MetadataReferences.definitelyAliases c.refs refs [reference] then
      tasks := tasks.insert reference [state]
      if let some value := result then results := results.insert reference value
    else
      tasks := tasks.insert reference (unionRefs (tasks[reference]?.getD [1, 2, 4]) [state])
      if let some value := result then
        results := results.insert reference (unionRefs (results[reference]?.getD [0]) value)
  return { c with tasks, taskResults := results }

private def joinPool (a b : Pool) : Pool := {
  task := unionRefs a.task b.task, owners := unionRefs a.owners b.owners
  events := unionRefs a.events b.events
  tasks := unionRefs a.tasks b.tasks
  canComplete := a.canComplete || b.canComplete, canSignal := a.canSignal || b.canSignal
  progressed := a.progressed || b.progressed }

private def joinPools (a b : Std.HashMap Nat Pool) : Std.HashMap Nat Pool :=
  b.fold (fun result k p => result.insert k (joinPool (result[k]?.getD {}) p)) a

private def joinConfiguration (a b : Configuration) : Configuration := { b with
  slots := joinSlots a.slots b.slots
  refs := MetadataReferences.join a.refs b.refs
  actors := joinActors a.actors b.actors
  pools := joinPools a.pools b.pools
  tasks := joinTable a.tasks b.tasks [1, 2, 4]
  taskResults := joinTable a.taskResults b.taskResults [0]
  tests := a.tests.zipWith (fun s t => { t with
    slots := joinSlots s.slots t.slots, refs := MetadataReferences.join s.refs t.refs
    actors := joinActors s.actors t.actors
    pools := joinPools s.pools t.pools
    tasks := joinTable s.tasks t.tasks [1, 2, 4]
    taskResults := joinTable s.taskResults t.taskResults [0] }) b.tests }

private def putRole (s : Slots) (i : Nat) (role : Bool) (parts : TupleParts := none) : Slots := { s with
  tuples := putParts s.tuples i parts
  values := s.values.set! i role
  initialized := s.initialized.set! i true
  sharedMetadata := s.sharedMetadata.set! i role }

private def advanceActor (c : Configuration) (a pc : Nat) : Configuration := { c with
  current := some a
  events := c.events.filter (· != a)
  actors := c.actors.modify a fun t => { t with pc, status := .running, event := none, taskWait := false, waitDst := none } }

private def nextActor (c : Configuration) : Configuration := Id.run do
  let mut c := c
  for a in c.startup do
    c := { c with startup := c.startup.tail }
    if c.actors[a]!.status == .running || c.actors[a]!.status == .ready then
      return advanceActor c a c.actors[a]!.pc
  return { c with current := none }

private def groupReady (p : MetadataPlan.Plan) (c : Configuration) (i : Nat) : Bool :=
  let g := p.groups[i]!
  let state := c.groups[i]!
  if g.kind == .branch || g.kind == .spawn then state.started > 0
  else if g.kind == .sync then
    state.started == g.children.size &&
      g.children.all (fun (a, _) => c.actors[a]!.status == .done)
  else state.winner.isSome

/-- A return propagates through active concurrent groups. Once a rush has
    ended, its surviving arm is background work: a later return stops that
    arm instead of returning from the enclosing function. -/
private def lateReturnActor (plan : MetadataPlan.Plan) (c : Configuration)
    (actor owner : Nat) : Option Nat := Id.run do
  let mut current := actor
  while current != owner do
    let some group := plan.groups.findIdx? (fun g => g.children.any (·.1 == current))
      | return none
    let g := plan.groups[group]!
    if g.kind == .rush && !c.groups[group]!.active then return some current
    current := g.owner
  return none

private def restoreTest (c : Configuration) (actor : Nat) : Option Configuration := do
  let t ← c.tests.head?
  if t.owner != actor then none else
    some <| advanceActor { c with
      slots := t.slots, refs := t.refs, actors := t.actors
      groups := t.groups, startup := t.startup, events := t.events
      pending := t.pending, launches := t.launches, tasks := t.tasks
      taskResults := t.taskResults, pools := t.pools, signals := t.signals, tests := c.tests.tail } actor t.no

private def mayFail : Expr → Bool
  | .heap (.isTag _) _ => true
  | .prim .query [.lit (.logic true)] => false
  | .prim op _ => [.query, .index, .lt, .le, .gt, .ge, .eq, .ne,
      .flt, .fle, .fgt, .fge].contains op
  | _ => false

private def wake (c : Configuration) (event : MetadataReferences.Refs)
    (task : Bool := false) (payload : Option MetadataReferences.Refs := none) : List Configuration := Id.run do
  let mut states := [(c, [])]
  for listener in c.events do
    let a := c.actors[listener]!
    if a.canceling || a.cancelRequested || a.status != .waiting true || a.taskWait != task then continue
    let some waiting := a.event | continue
    if !MetadataReferences.aliases event waiting then continue
    let certain := MetadataReferences.definitelyAliases c.refs event waiting
    states := states.flatMap fun (c, ready) =>
      let refs := match a.waitDst, payload with
        | some dst, some value => MetadataReferences.set c.refs dst value
        | _, _ => c.refs
      let started := ({ c with
        refs, events := c.events.filter (· != listener)
        actors := c.actors.modify listener fun a => { a with status := .ready, event := none } },
        ready ++ [listener])
      if certain then [started] else [(c, ready), started]
  return states.map fun (c, ready) =>
    if ready.isEmpty then c else
      let owner := c.current.toList
      nextActor { c with startup := ready ++ owner ++ c.startup }

private def beginSignal (plan : MetadataPlan.Plan) (c : Configuration)
    (actor : Nat) (resume : Option Nat) : Configuration :=
  let c := advanceActor c actor plan.drain
  { c with signals := actor :: c.signals, actors := c.actors.modify actor fun a =>
    { a with signalReturns := resume :: a.signalReturns } }

private def descendants (plan : MetadataPlan.Plan) (root : Nat) : List Nat := Id.run do
  let mut found := [root]
  repeat
    let next := plan.groups.foldl (fun found g =>
      if found.contains g.owner then (found ++ g.children.toList.map (·.1)).eraseDups else found) found
    if next == found then return found
    found := next
  return found

private def capturePool (plan : MetadataPlan.Plan) (c : Configuration)
    (group child : Nat) : Configuration :=
  let a := c.actors[child]!
  if a.status == .idle || a.status == .done then c else
    let waiters := (descendants plan child).map fun i => c.actors[i]!
    let active := waiters.filter (fun a => a.status != .idle && a.status != .done)
    let summary : Pool := {
      owners := active.flatMap (fun a => a.task.getD [])
      task := active.filter (·.canComplete) |>.flatMap (fun a => a.task.getD [])
      canComplete := active.any (fun a => a.task.isSome && a.canComplete)
      canSignal := active.any (·.canSignal)
      events := waiters.filter (fun a => !a.taskWait) |>.flatMap (fun a => a.event.getD [])
      tasks := waiters.filter (·.taskWait) |>.flatMap (fun a => a.event.getD []) }
    { c with pools := c.pools.insert group (joinPool (c.pools[group]?.getD {}) summary) }

private inductive PoolCause where
  | event (refs : MetadataReferences.Refs)
  | task (refs : MetadataReferences.Refs)
  | cancel (refs : MetadataReferences.Refs)
  | inside | global

private def objectRefs (refs : MetadataReferences.Refs) : MetadataReferences.Refs :=
  if refs.isEmpty then [0] else refs

/-- Widen the effects of older starts without restoring stale caller slots.
    Each transition returns to the same suspension/drain boundary; the
    ordinary configuration fixed point includes arbitrary repetitions. -/
private def poolTransitions (plan : MetadataPlan.Plan) (c : Configuration)
    (cause : PoolCause) : List Configuration := Id.run do
  let mut output := []
  for (group, pool) in c.pools.toList do
    let eligible := pool.progressed || match cause with
      | .event refs => MetadataReferences.aliases pool.events refs
      | .task refs => MetadataReferences.aliases pool.tasks refs
      | .cancel refs => MetadataReferences.aliases pool.owners refs
      | .inside => false
      | .global => true
    if !eligible then continue
    let progressed := { c with
      refs := MetadataReferences.widenFields c.refs
      pools := c.pools.insert group { pool with progressed := true } }
    if progressed != c then output := output ++ [progressed]
    let emit (base : Configuration) (refs : MetadataReferences.Refs) (task : Bool) : List Configuration :=
      match c.current with
      | some actor =>
        let paused := beginSignal plan base actor (some c.actors[actor]!.pc)
        (wake paused refs task (some [0])).filter (fun next => next.current != some actor)
      | none =>
        (wake base refs task (some [0])).filterMap fun next =>
          if next.current.isSome then some { next with signals := c.actors.size :: next.signals }
          else none
    if pool.canSignal then output := output ++ emit progressed [0] false
    let cancelled := match cause with | .cancel _ => !pool.progressed | _ => false
    if pool.canComplete && !cancelled then
      let completed := setTask progressed pool.task 2 (some [0])
      if completed != c then output := output ++ [completed]
      output := output ++ emit completed pool.task true
  return output

private partial def constantSleep : Expr → Option Float
  | .lit (.float bits) => some (VFloat.ofBits bits)
  | .seq _ b | .assign _ b => constantSleep b
  | .prim .fneg [e] => (constantSleep e).map (- ·)
  | _ => none

private structure ScheduleEnv where
  fns : Array Fn
  infos : Array Info
  fields : Array (List Nat)
  fn : Fn
  info : Info
  plan : MetadataPlan.Plan
  referenceLive : MetadataLiveness.Analysis
  environments : Std.HashMap (Nat × Nat) (Fn × Info) := {}

/-- A transfer key forgets analysis stack slots, but retains actual heap
    identities and argument aliases. These are distinct from scalar roles. -/
private structure CellInput where
  fn : Nat
  arguments : List Argument
  references : List MetadataCells.Refs
  heap : MetadataCells.Memory
  deriving BEq, Inhabited

private structure CellEffect where
  role : Option Bool := none
  parts : TupleParts := none
  references : MetadataCells.Refs := []
  heap : Option MetadataCells.Memory := none
  images : Std.HashMap Nat MetadataCells.Refs := {}
  yielded : Bool := false
  deriving BEq, Inhabited

private structure CellSummary where
  input : CellInput
  effect : CellEffect := {}
  deriving Inhabited

private def joinCellEffect (a b : CellEffect) : CellEffect := {
  role := joinRole a.role b.role
  parts := joinParts a.role a.parts b.role b.parts
  references := MetadataCells.joinRefs a.references b.references
  heap := match a.heap, b.heap with
    | some x, some y => some (MetadataCells.join x y)
    | some x, none | none, some x => some x
    | none, none => none
  images := b.images.fold (fun out key refs =>
    out.insert key (MetadataCells.joinRefs (out[key]?.getD []) refs)) a.images
  yielded := a.yielded || b.yielded }

private def cellPair (a b : Nat) : Nat :=
  let sum := a + b
  sum * (sum + 1) / 2 + b

/-- Witness references are ordinary tracked locals, so every allocation,
    rollback and join updates them along with source aliases. -/
private def cellWitness (base object : Nat) : Nat :=
  18446744073709551616 + cellPair base object

private def applyCellEffect (before : MetadataCells.Memory) (effect : CellEffect) : MetadataCells.Memory :=
  match effect.heap with
  | none => before
  | some heap => { heap with
      nslots := before.nslots
      locals := before.locals.fold (fun out slot refs =>
        out.insert slot (refs.foldl (fun renamed object =>
          MetadataCells.joinRefs renamed (effect.images[object]?.getD [object])) [])) {} }

private structure State where
  scheduleProofs : Std.HashMap Key ScheduleProof := {}
  scheduledCalls : Option (Std.HashMap Key (Option Bool × TupleParts × Bool)) := none
  scheduledCallOrder : Array Key := #[]
  suppressedSharedWrite : Bool := false
  scalarReturns : Array Bool := #[]
  deferSchedules : Bool := true
  contextDeferred : Bool := false
  summaries : Array Summary := #[]
  indices : Std.HashMap Key Nat := {}
  changed : Bool := false
  /-- Shared-local modes depend on complete return summaries, not an early
      real-only approximation of a recursive initializer. -/
  validateShared : Bool := false
  /-- Executable roles grow with return summaries. Checking them during
      solving avoids exploring continuations of an already invalid use;
      discovery still disables this while selecting a transfer. -/
  validateUses : Bool := true
  discovery : Bool := false
  seen : Bits := {}
  plans : Array (Option MetadataPlan.Plan) := #[]
  referenceLives : Array (Option MetadataLiveness.Analysis) := #[]
  sites : Array (Bool × List Expr) := #[]
  live : Array Key := #[]
  liveSeen : Std.HashMap Key Unit := {}
  debug : Bool := false
  active : Option Key := none
  signalArguments : Option (Array (List Nat)) := none
  dependencies : Option (Std.HashMap Nat (Option Bool × TupleParts × Bool)) := none
  captureMismatch : Bool := false
  borrowers : Array Bool := #[]
  borrowedWork : Array Bool := #[]
  borrowedTasks : Array Bool := #[]
  cellTag : Option Nat := none
  cellEnabled : Bool := false
  cellTransportTag : Option Nat := none
  cellPath : List Nat := [0]
  cellSites : Std.HashMap (Nat × Option Nat × List Nat) Nat := {}
  cellExternalSites : Std.HashMap Nat Nat := {}
  cellInputSites : Std.HashMap (Nat × Nat) Nat := {}
  cellScope : Nat := 0
  cellGraphOwner : Option Nat := none
  cellTransports : Array Bool := #[]
  cellArraySummaries : Array Bool := #[]
  cellSummaries : Array CellSummary := #[]
  cellSummaryIndices : Std.HashMap Nat (List Nat) := {}
  cellActive : List Nat := []
  cellRecursive : Std.HashMap Nat Unit := {}
  cellRefBase : Nat := 0
  cellCapable : Array Bool := #[]
  /-- Independently validated all-real transfers. The leading flag requires
      the caller's complete alias state to prove empty private input refs. -/
  closedTransfers : Std.HashMap Nat (Bool × Option Bool × TupleParts × Bool) := {}

private abbrev M := StateT State (Except String)

private def cellChild (child : Nat) (action : M α) : M α := do
  if !(← get).cellEnabled then return ← action
  let path := (← get).cellPath
  modify fun st => { st with cellPath := child :: path }
  let result ← action
  modify fun st => { st with cellPath := path }
  return result

private def cellSite (_fn : Fn) (transport : Option Bool) (arraySummary : Bool := false) : M Nat := do
  let st ← get
  let key := (st.cellScope, st.cellGraphOwner, st.cellPath)
  if let some site := st.cellSites[key]? then
    if let some transport := transport then
      modify fun st => { st with cellTransports := st.cellTransports.set! site transport }
    if arraySummary then
      modify fun st => { st with cellArraySummaries := st.cellArraySummaries.set! site true }
    return site
  let site := st.cellTransports.size
  modify fun st => { st with
    cellSites := st.cellSites.insert key site
    cellTransports := st.cellTransports.push (transport.getD false)
    cellArraySummaries := st.cellArraySummaries.push arraySummary }
  return site

/-- External private formals may alias each other. Their one summary site
    is disjoint from constructor sites, but never unique or metadata-writable. -/
private def cellExternalSite (owner : Nat) : M Nat := do
  let st ← get
  if let some site := st.cellExternalSites[owner]? then return site
  let site := st.cellTransports.size
  modify fun st => { st with
    cellExternalSites := st.cellExternalSites.insert owner site
    cellTransports := st.cellTransports.push false
    cellArraySummaries := st.cellArraySummaries.push false }
  return site

/-- Incoming value identities have their own sites and may alias each
    other; they can never collide with a constructor or private summary site. -/
private def cellInputSite (owner slot : Nat) : M Nat := do
  let st ← get
  if let some site := st.cellInputSites[(owner, slot)]? then return site
  let site := st.cellTransports.size
  modify fun st => { st with
    cellInputSites := st.cellInputSites.insert (owner, slot) site
    cellTransports := st.cellTransports.push false
    cellArraySummaries := st.cellArraySummaries.push false }
  return site

private def cellExternal (heap : MetadataCells.Memory) (objects : MetadataCells.Refs) : Bool :=
  objects.any fun object => object == 1 ||
    (heap.nodes[object]?.map (·.external)).getD false

private def cellTransport (heap : MetadataCells.Memory) (sites : Array Bool)
    (objects : MetadataCells.Refs) : Bool :=
  !objects.isEmpty && objects.all fun object => object ≥ 2 &&
    heap.nodes.contains object && (sites[(object - 2) / 2]?.getD false)

private def cellConcurrentBody (fns : Array Fn) (body : Expr) : Bool :=
  (MetadataPlan.calls body).any fun callee =>
    ["$branchMark", "$syncMark", "$raceMark", "$rushMark", "$spawnMark"].contains
      ((fns[callee]?.map (·.name)).getD "")

private def cellElements (heap : MetadataCells.Memory) (objects : MetadataCells.Refs) : MetadataCells.Refs :=
  objects.foldl (fun refs object =>
    if object == 1 then MetadataCells.joinRefs refs [1]
    else if object == 0 then MetadataCells.joinRefs refs [0] else
      let refs := if (heap.nodes[object]?.map (·.external)).getD false then
          MetadataCells.joinRefs refs [1] else refs
      heap.fields.fold (fun refs (owner, _) values =>
        if owner == object then MetadataCells.joinRefs refs values else refs) refs) []

private def refuse (fn : Fn) (info : Info) (what : String) (details : String := "") : M α := do
  let st ← get
  let context := if st.debug then
    s!"\nmetadata context: {reprStr st.active}\ninputs: {info.inputs}; seeds: {info.seeds}\n{details}\n{reprStr (info.body.getD fn.body)}" else ""
  throw s!"{info.pos.show}: dummy type value cannot {what} (in {fn.name}){context}"

/-- Preserve first-request order as well as dependency values: live-context
    replay must retain the original graph's diagnostic traversal order. -/
private def rememberScheduledCall (key : Key) (value : Option Bool × TupleParts × Bool) : M Unit := do
  let st ← get
  if let some calls := st.scheduledCalls then
    set { st with
      scheduledCallOrder := if calls.contains key then st.scheduledCallOrder else st.scheduledCallOrder.push key
      scheduledCalls := some (calls.insert key value) }

private def request (key : Key) : M (Option Bool × TupleParts × Bool) := do
  let st ← get
  if st.validateUses && st.validateShared && !st.discovery && !st.liveSeen.contains key then
    set { st with live := st.live.push key, liveSeen := st.liveSeen.insert key () }
  let st ← get
  if let some i := st.indices[key]? then
    let value := (st.summaries[i]!.result, st.summaries[i]!.parts, st.summaries[i]!.yielded)
    if let some dependencies := st.dependencies then
      if !dependencies.contains i then
        modify fun st => { st with dependencies := some (dependencies.insert i value) }
    rememberScheduledCall key value
    return value
  let i := st.summaries.size
  let dependencies := st.dependencies.map (·.insert i (none, none, false))
  set { st with
    indices := st.indices.insert key i
    summaries := st.summaries.push { key }, changed := true, dependencies }
  rememberScheduledCall key (none, none, false)
  return (none, none, false)



/-- Pending configurations share their complete facts by control key and
    run in graph reverse postorder. No provenance component is discarded. -/
private structure ScheduleWork where
  env : ScheduleEnv
  modes : Bits
  modeWords : MetadataLiveness.SlotMask
  ranks : Array Nat
  ready : Std.TreeMap (Nat × Nat) (Array Nat) (fun a b =>
    match compare a.1 b.1 with | .eq => compare a.2 b.2 | order => order) := {}
  pending : Std.HashMap (Array Nat) Configuration := {}
  serial : Nat := 0


mutual
private partial def expr (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots) : Expr → M Flow
  | .lit value => do
    let refs := if (← get).cellEnabled && MetadataValues.hasObjectRef value then [0] else []
    return { slots, valueRefs := refs }
  | .local i => do
    let base := (← get).cellRefBase
    return {
      slots
      value := some ((slots.values.get i))
      valueParts := slots.tuples[i]?
      valueRefs := if info.objectFreeMask.testBit i || info.dataOnlyMask.testBit i then [] else MetadataCells.getLocal slots.heap (base + i) }
  | .assign i e => do
    let out ← cellChild 0 (expr fns infos fields fn info slots e)
    let some role := out.value | return out
    let role := role || info.seeds.contains i
    if role then modify fun st => { st with seen := st.seen.set! i true }
    if (← get).validateUses && role && info.uses.contains i then
      refuse fn info "be an executable function or method receiver" s!"receiver slot {i}, value {reprStr e}"
    if info.shared.contains i && (out.slots.initialized.get i) && role &&
        !((out.slots.sharedMetadata.get i)) then
      if (← get).validateShared then
        refuse fn info "enter a shared local containing executable data" s!"shared slot {i}, value {reprStr e}"
      else
        modify fun st => { st with suppressedSharedWrite := true }
    let first := !((out.slots.initialized.get i))
    let refs := if info.objectFreeMask.testBit i || info.dataOnlyMask.testBit i then [] else out.valueRefs
    return { out with
      valueRefs := refs
      value := some role
      valueParts := if info.seeds.contains i then none else out.valueParts
      slots := {
        heap := MetadataCells.setLocal out.slots.heap ((← get).cellRefBase + i) refs
        values := out.slots.values.set! i role
        tuples := putParts out.slots.tuples i (if info.seeds.contains i then none else out.valueParts)
        initialized := out.slots.initialized.set! i true
        written := if info.shared.contains i then out.slots.written.set! i true else out.slots.written
        -- Once real data enters a shared cell, waiting aliases can execute it.
        -- A later metadata write must not reuse its original metadata mode.
        sharedMetadata := out.slots.sharedMetadata.set! i
          (role && (first || (out.slots.sharedMetadata.get i))) } }
  | .seq a b => do
    let a ← cellChild 0 (expr fns infos fields fn info slots a)
    if a.value.isNone then return a
    return withExits a (← cellChild 1 (expr fns infos fields fn info a.slots b))
  | .call g es => do
    let name := (fns[g]?.map (·.name)).getD ""
    if name == "$spawnMark" then
      if let [.prim .mkArr [.seq target _, .seq (.local _) _]] := es then
        let (result, out) ← spawned fns infos fields fn info slots target
        -- Lowering stores the call's result in task.Result. It is an
        -- ordinary mutable field, subject to the same rule as heap.set.
        if (← get).validateUses && result.getD false then
          refuse fn info "enter a spawned task's result field containing executable data"
        return out
    if ["$syncMark", "$raceMark", "$rushMark"].contains name then
      if let [.prim .mkArr arms] := es then
        return ← concurrent fns infos fields fn info slots (name == "$syncMark") arms
    let (out, result, parts, yielded) ← invoke fns infos fields fn info slots g es
    return { out with
      value := if name == "$branchMark" then
          -- The child releases its owner when it completes or first waits.
          if out.value.isSome || out.yielded then some false else none
        else if out.value.isSome then result else none
      valueParts := if name == "$branchMark" then none else parts
      valueRefs := out.valueRefs
      -- A branch starts its body to its first wait without yielding its owner.
      yielded := if name == "$branchMark" then false else out.yielded || yielded }
  | .prim op es => do
    let (args, argumentParts, out) ← arguments fns infos fields fn info slots es
    if out.value.isNone then return out
    let column := match op with
      | .tupGet i => (argumentParts.headD none).bind (·[i]?)
      | _ => none
    let value := match op, es with
      | .fail, _ | .userErr, _ | .query, [.lit (.logic false)] | .query, [.lit .none] => none
      -- Equality and inequality return the left operand; an array index selects a
      -- payload without becoming part of it. All operands still run above.
      | .eq, _ | .ne, _ | .index, _ => some (args.headD false)
      | .arrSet, _ => some (args.headD false || args[2]?.getD false)
      | .tupGet _, _ => some ((column.map (·.role)).getD (args.headD false))
      | .query, _ | .mkArr, _ | .mkTup, _ | .mkSome, _ | .concat, _ |
          .flatten, _ |
          .lt, _ | .le, _ | .gt, _ | .ge, _ |
          .flt, _ | .fle, _ | .fgt, _ | .fge, _ => some (args.any id)
      -- Length, formatting and arithmetic construct fresh scalar data;
      -- they cannot preserve a dictionary, function or opaque payload.
      | _, _ => some false
    let mut out := out
    let mut refs := []
    if (← get).cellEnabled then
      let values := args.zipIdx.map fun (role, i) =>
        ({ role, parts := argumentParts[i]?.getD none, refs := out.argumentRefs[i]?.getD [] } : MetadataCells.Payload)
      let first := out.argumentRefs.headD []
      match op with
      | .mkArr | .mkTup | .mkSome =>
        -- Immutable values whose children contain no object aliases cannot
        -- acquire an alias later. Their scalar roles/tuple columns stay in
        -- the ordinary domain; unknown 0/1 references are never omitted.
        if values.any (fun value => !value.refs.isEmpty) then
          let site ← cellSite fn (some true)
          let allocated := MetadataCells.allocate out.slots.heap site false values
          out := { out with slots := { out.slots with heap := allocated.2 } }
          refs := allocated.1
      | .tupGet field => refs := MetadataCells.loadRefs out.slots.heap first field
      | .query => refs := MetadataCells.loadRefs out.slots.heap first 0
      | .eq | .ne => refs := first
      | .index =>
        let summaries := (← get).cellArraySummaries
        refs := match (es[1]? : Option Expr) with
          | some (.lit (.int index)) =>
            if index ≥ 0 then
              first.foldl (fun refs object =>
                let field := if object ≥ 2 && (summaries[(object - 2) / 2]?.getD false) then 0 else index.toNat
                MetadataCells.joinRefs refs (MetadataCells.loadRefs out.slots.heap [object] field)) []
            else []
          | _ => cellElements out.slots.heap first
      | .arrSet | .concat | .flatten =>
        let elements := if op == .flatten then
            cellElements out.slots.heap (cellElements out.slots.heap first)
          else if op == .arrSet then MetadataCells.joinRefs (cellElements out.slots.heap first)
            (out.argumentRefs[2]?.getD [])
          else out.argumentRefs.foldl (fun refs arg =>
            MetadataCells.joinRefs refs (cellElements out.slots.heap arg)) []
        if !elements.isEmpty then
          let site ← cellSite fn (some true) true
          let allocated := MetadataCells.allocate out.slots.heap site false [{ refs := elements }]
          out := { out with slots := { out.slots with heap := allocated.2 } }
          refs := allocated.1
      | _ => pure ()
    let valueParts := match op with
      | .mkTup => MetadataCells.tupleParts args argumentParts
      | .mkSome | .query => argumentParts.headD none
      | .tupGet _ => column.bind (·.parts)
      | _ => none
    return { out with value, valueRefs := refs, valueParts }
  | .heap op es => do
    let (args, parts, out) ← arguments fns infos fields fn info slots es
    if out.value.isNone then return out
    let mut out := out
    let mut refs := []
    let mut payload : Option MetadataCells.Payload := none
    let policy ← get
    let privateObjects := out.argumentRefs.headD []
    if policy.cellEnabled then
      match op with
      | .new tag =>
        let isPrivate := policy.cellTag == some tag
        let transport := policy.cellTransportTag == some tag
        let values := args.zipIdx.map fun (role, i) =>
          ({ role, parts := parts[i]?.getD none, refs := out.argumentRefs[i]?.getD [] } : MetadataCells.Payload)
        let heap := if !isPrivate && !transport then
            values.foldl (fun heap value => MetadataCells.markEscaped heap value.refs) out.slots.heap
          else out.slots.heap
        let site ← cellSite fn (some transport)
        let allocated := MetadataCells.allocate heap site isPrivate values
        out := { out with slots := { out.slots with heap := allocated.2 } }
        refs := allocated.1
      | .get field =>
        if field == 0 then payload := MetadataCells.readCell out.slots.heap privateObjects
        if payload.isNone then
          if let some known := MetadataCells.readExternalFieldPayload out.slots.heap privateObjects field then
            let role := known.role || args.headD false
            let parts := if args.headD false then none else known.parts
            payload := some { known with role, parts }
        if payload.isNone && cellTransport out.slots.heap policy.cellTransports privateObjects then
          payload := MetadataCells.readFieldPayload out.slots.heap privateObjects field
        refs := MetadataCells.loadRefs out.slots.heap privateObjects field
        let excludesCell := es.head?.any fun
          | .local obj => info.nonCellMask.testBit obj
          | _ => false
        let possibleCell := policy.cellTag.isSome && field == 0 &&
          ((!excludesCell && (privateObjects.any (· ≤ 1) || cellExternal out.slots.heap privateObjects)) ||
            (es.head?.any fun | .local obj => info.cellSlots.contains obj | _ => false) ||
            privateObjects.any (fun object => out.slots.heap.cells.contains object))
        if payload.isNone && possibleCell && MetadataCells.mayPrivate out.slots.heap privateObjects then
          -- Unknown identities may denote any cell already present in this
          -- closed heap. Retain all payload taint instead of treating the
          -- real wrapper identity as evidence that its payload is real.
          payload := some <| if cellExternal out.slots.heap privateObjects then { role := true, refs := [1] }
            else if out.slots.heap.cells.isEmpty then { role := true, refs := [0] } else
            out.slots.heap.cells.fold (fun joined _ value => MetadataCells.joinPayload joined value)
              ({ role := args.headD false, refs } : MetadataCells.Payload)
      | .isTag _ => refs := privateObjects
      | _ => pure ()
    -- Only tuples and the immutable compiler-owned lazy stack carry
    -- structural columns. Heap reads can consume the lazy stack's columns
    -- even when an ordinary call summary has lost the physical identity.
    let knownColumn := match op with
      | .get i => (parts.headD none).bind (·[i]?)
      | _ => none
    let role ← match op with
      | .new tag => pure (if policy.cellEnabled && policy.cellTag == some tag && args.length == 1 then false else
          args.zipIdx.any fun (role, i) => role && !(fields[tag]?.getD []).contains i)
      | .set field => do
        let rhs : MetadataCells.Payload := {
          role := args[1]?.getD false, parts := parts[1]?.getD none,
          refs := out.argumentRefs[1]?.getD [] }
        let precise := if policy.cellEnabled && field == 0 then
            MetadataCells.writeCell out.slots.heap privateObjects rhs else none
        match precise with
        | some heap => out := { out with slots := { out.slots with heap } }
        | none => do
          let metadataField := match es.head? with
            | some (.local obj) => info.metadataWrites.contains (obj, field)
            | _ => false
          if (← get).validateUses && rhs.role && !metadataField then
            refuse fn info "enter a shared object field containing executable data"
          if policy.cellEnabled then
            let heap := if field == 0 then MetadataCells.writeKnownCells out.slots.heap privateObjects rhs else out.slots.heap
            let external := !privateObjects.isEmpty && privateObjects.all fun object =>
              (heap.nodes[object]?.map fun node => node.external && !node.privateCell).getD false
            let heap := if external then MetadataCells.storeExternalFieldPayload heap privateObjects field rhs
              else if cellTransport heap policy.cellTransports privateObjects then
                MetadataCells.storeFieldPayload heap privateObjects field rhs
              else MetadataCells.storeRefs heap privateObjects field rhs.refs
            out := { out with slots := { out.slots with heap } }
        refs := rhs.refs
        pure rhs.role
      | .get field =>
        if let some p := payload then pure p.role
        else if let some column := knownColumn then pure column.role
        else if policy.cellEnabled && cellTransport out.slots.heap policy.cellTransports privateObjects then
          pure true
        else if field == 0 && policy.cellEnabled &&
            ((es.head?.any fun | .local obj => info.cellSlots.contains obj | _ => false) ||
              privateObjects.any (fun object => (out.slots.heap.nodes[object]?.map (·.privateCell)).getD false)) &&
            MetadataCells.mayPrivate out.slots.heap privateObjects then
          pure true
        else pure (args.headD false)
      | .isTag _ => pure (args.headD false)
      | .tag => pure false
    let valueParts := match op with
      | .new tag =>
        if policy.cellTransportTag == some tag then MetadataCells.tupleParts args parts else none
      | .get _ =>
        match payload with
        | some value => value.parts
        | none => knownColumn.bind (·.parts)
      | _ => none
    return { out with
      value := some role, valueParts
      valueRefs := (payload.map (·.refs)).getD refs }
  | .ite c t e => do
    let c ← cellChild 0 (expr fns infos fields fn info slots c)
    let t ← if c.value.isSome then cellChild 1 (expr fns infos fields fn info c.slots t)
      else pure { slots := c.slots, value := none }
    -- The failure arm starts before c, including its mutable-local roles.
    let e ← cellChild 2 (expr fns infos fields fn info slots e)
    let merged := match t.value, e.value with
      | some _, some _ => joinSlots t.slots e.slots
      | some _, none => t.slots
      | _, _ => e.slots
    return withExits c {
      slots := merged, value := joinRole t.value e.value
      valueRefs := MetadataCells.joinRefs t.valueRefs e.valueRefs
      returnedRefs := MetadataCells.joinRefs t.returnedRefs e.returnedRefs
      returnedHeap := match t.returnedHeap, e.returnedHeap with
        | some a, some b => some (MetadataCells.join a b)
        | some a, none | none, some a => some a
        | none, none => none
      valueParts := joinParts t.value t.valueParts e.value e.valueParts
      returned := joinRole t.returned e.returned
      returnedParts := joinParts t.returned t.returnedParts e.returned e.returnedParts, broken := joinOpt t.broken e.broken
      yielded := t.yielded || e.yielded }
  | .forE i source filt body => do
    let source ← cellChild 0 (expr fns infos fields fn info slots source)
    let some item := source.value | return source
    if item then modify fun st => { st with seen := st.seen.set! i true }
    let enabled := (← get).cellEnabled
    let site ← if enabled then cellSite fn (some true) true else pure 0
    let base := (← get).cellRefBase
    let sourceKey := 79228162514264337593543950336 + 2 * cellPair site base
    let itemsKey := sourceKey + 1
    let heap := if enabled then
        MetadataCells.setLocal (MetadataCells.setLocal { source.slots.heap with
          nslots := max source.slots.heap.nslots (itemsKey + 1) } sourceKey source.valueRefs) itemsKey []
      else source.slots.heap
    let mut head := { source.slots with heap }
    let mut result := false
    let mut exits := source
    let mut growing := true
    let mut iterations := 0
    while growing do
      iterations := iterations + 1
      if (← get).debug && iterations % 32 == 0 then
        dbg_trace s!"metadata fixedpoint {fn.name} iterations={iterations} nodes={head.heap.nodes.size} fields={head.heap.fields.size} cells={head.heap.cells.size} locals={head.heap.locals.size}"
      let state ← get
      let entry := { head with
        values := head.values.set! i item, tuples := head.tuples.erase i
        heap := if enabled then MetadataCells.setLocal head.heap (state.cellRefBase + i)
          (cellElements head.heap (MetadataCells.getLocal head.heap sourceKey)) else head.heap }
      let filt ← cellChild 1 (expr fns infos fields fn info entry filt)
      let body ← if filt.value.isSome then cellChild 2 (expr fns infos fields fn info filt.slots body)
        else pure { slots := entry, value := none }
      exits := withExits filt (withExits body exits)
      result := result || body.value.getD false
      let body := if enabled && body.value.isSome then { body with slots := { body.slots with
        heap := MetadataCells.setLocal body.slots.heap itemsKey
          (MetadataCells.joinRefs (MetadataCells.getLocal body.slots.heap itemsKey) body.valueRefs) } }
        else body
      let next := if body.value.isSome then freshLocals info.shared source.slots (joinSlots head body.slots) else head
      growing := next != head
      head := next
    let items := if enabled then MetadataCells.getLocal head.heap itemsKey else []
    if items.isEmpty then return { exits with slots := head, value := some result, valueParts := none, valueRefs := [] }
    -- The array is a compiler-owned immutable carrier. Its stored item aliases
    -- are evaluated before allocation, and recency rebases them once more.
    let (refs, heap) := MetadataCells.allocate head.heap site false [{ role := result, refs := items }]
    return { exits with slots := { head with heap }, value := some result, valueParts := none, valueRefs := refs }
  | .loop body => do
    let mut head := slots
    let mut returned := none
    let mut returnedParts := none
    let mut exits : Flow := { slots, value := none }
    let mut broken := none
    let mut yielded := false
    let mut growing := true
    let mut iterations := 0
    while growing do
      iterations := iterations + 1
      if (← get).debug && iterations % 32 == 0 then
        dbg_trace s!"metadata fixedpoint {fn.name} iterations={iterations} nodes={head.heap.nodes.size} fields={head.heap.fields.size} cells={head.heap.cells.size} locals={head.heap.locals.size}"
      let out ← cellChild 0 (expr fns infos fields fn info head body)
      exits := withExits out exits
      returnedParts := joinParts returned returnedParts out.returned out.returnedParts
      returned := joinRole returned out.returned
      broken := joinOpt broken out.broken
      yielded := yielded || out.yielded
      let next := if out.value.isSome then freshLocals info.shared slots (joinSlots head out.slots) else head
      growing := next != head
      head := next
    return { exits with slots := broken.getD head, value := broken.map (fun _ => false), returned, returnedParts, yielded }
  | .brk => pure { slots, value := none, broken := some slots }
  | .ret e => do
    let out ← cellChild 0 (expr fns infos fields fn info slots e)
    return { out with
      value := none, valueParts := none, returned := joinRole out.returned out.value
      returnedParts := joinParts out.returned out.returnedParts out.value out.valueParts
      returnedRefs := MetadataCells.joinRefs out.returnedRefs out.valueRefs
      returnedHeap := some (match out.returnedHeap with
        | some old => MetadataCells.join old out.slots.heap | none => out.slots.heap) }
  | .print e => do
    let out ← cellChild 0 (expr fns infos fields fn info slots e)
    return { out with value := out.value.map (fun _ => false), valueParts := none, valueRefs := [] }

/-- A spawn evaluates the selected call's arguments now. Its result belongs
    to the task; returning or yielding lets its caller continue. A task that
    does neither holds the caller. Dispatch and argument exits run normally. -/
private partial def spawned (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots) :
    Expr → M (Option Bool × Flow)
  | .call g es => do
    let (out, result, parts, yielded) ← invoke fns infos fields fn info slots g es
    return (result, { out with valueParts := none, value :=
      if out.value.isSome && (result.isSome || yielded) then some false else none })
  | .seq a b => do
    let a ← expr fns infos fields fn info slots a
    if a.value.isNone then return (none, a)
    let (result, b) ← spawned fns infos fields fn info a.slots b
    return (result, withExits a b)
  | .ite c t e => do
    let c ← expr fns infos fields fn info slots c
    let (tr, t) ← if c.value.isSome then spawned fns infos fields fn info c.slots t
      else pure (none, { slots := c.slots, value := none })
    let (er, e) ← spawned fns infos fields fn info slots e
    let merged := match t.value, e.value with
      | some _, some _ => joinSlots t.slots e.slots
      | some _, none => t.slots
      | _, _ => e.slots
    return (joinRole tr er, withExits c {
      slots := merged, value := joinRole t.value e.value
      valueRefs := MetadataCells.joinRefs t.valueRefs e.valueRefs
      returnedRefs := MetadataCells.joinRefs t.returnedRefs e.returnedRefs
      returnedHeap := match t.returnedHeap, e.returnedHeap with
        | some a, some b => some (MetadataCells.join a b)
        | some a, none | none, some a => some a
        | none, none => none
      valueParts := joinParts t.value t.valueParts e.value e.valueParts
      returned := joinRole t.returned e.returned
      returnedParts := joinParts t.returned t.returnedParts e.returned e.returnedParts, broken := joinOpt t.broken e.broken
      yielded := t.yielded || e.yielded })
  | .assign i e => do
    let (result, out) ← spawned fns infos fields fn info slots e
    return (result.map (· || info.seeds.contains i), out)
  | e => do
    let out ← expr fns infos fields fn info slots e
    return (out.value, { out with value := out.value.map (fun _ => false), valueParts := none })

private partial def invoke (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots)
    (g : Nat) (es : List Expr) (summarize : Bool := true) : M (Flow × Option Bool × TupleParts × Bool) := do
  let (args, argumentParts, out) ← arguments fns infos fields fn info slots es
  if out.value.isNone then return (out, none, none, false)
  let gi := infos[g]?.getD {}
  -- A readonly borrower usually needs only the ordinary transfer. A
  -- statically opaque capture can nevertheless be stale after a real
  -- overwrite, in which case replay it against the owner's live cell.
  for (i, origin) in gi.source.slots do
    if origin.frame == (fns[g]?.map (·.name)).getD "" ||
        !(gi.inputs.contains i || gi.seeds.contains i) then continue
    if let some (cell, _) := info.source.slots.find? (fun (_, s) =>
        s.frame == fn.name && s.frame == origin.frame && s.name == origin.name) then
      if (slots.initialized.get cell) && !((slots.values.get cell)) then
        modify fun st => { st with captureMismatch := true }
  let roles := args.zipIdx.map fun (role, i) => role || gi.inputs.contains i
  let keyArgs := roles.zipIdx.map fun (role, i) =>
    ({ role, parts := if gi.inputs.contains i || !role then none else argumentParts[i]?.getD none } : Argument)
  if (← get).validateUses && gi.required.any (fun i => roles[i]?.getD false) then
    refuse fn info s!"provide executable evidence or a receiver to {(fns[g]?.map (·.name)).getD "a call"}"
  if !summarize then return (out, none, none, false)
  let out := { out with argumentRefs := out.argumentRefs.zipIdx.map fun (refs, i) =>
    if gi.objectFreeMask.testBit i || gi.dataOnlyMask.testBit i then [] else refs }
  let state ← get
  -- Closed transfers require private-irrelevant inputs and no external or protocol
  -- effects. Results are either object-free or Source-certified data whose
  -- typed reachable fields exclude private cells and metadata. Only those
  -- private-irrelevant aliases may be omitted; argument effects stay in out.
  if keyArgs.all (fun arg => !arg.role && (arg.parts.getD []).all (! ·.role)) &&
      argumentParts.all (fun parts => (parts.getD []).all (! ·.role)) then
    if let some (needsEmptyInputs, result, parts, yielded) := state.closedTransfers[g]? then
      -- A dynamic premise is checked only with complete alias interpretation.
      -- Empty refs denote no reachable private-relevant caller identity; they
      -- cannot be inferred from the arguments' metadata roles alone.
      if !needsEmptyInputs || (state.cellEnabled && out.argumentRefs.all List.isEmpty) then
        if state.debug then dbg_trace s!"closed transfer {(fns[g]?.map (·.name)).getD "?"} emptyInputs={needsEmptyInputs}"
        return ({ out with valueRefs := [] }, result, parts, yielded)
  let references := out.argumentRefs.flatten
  let privateCall := state.cellTag.isSome &&
    ((state.cellCapable[g]?.getD false) || MetadataCells.mayReachPrivate out.slots.heap references)
  if privateCall then
    let some callee := fns[g]? | throw "internal: private-cell call has no body"
    let body := gi.body.getD callee.body
    let directGetter := match body with
      | .heap (.get _) [.local _] | .ret (.heap (.get _) [.local _]) => true
      | _ => false
    let base := state.cellRefBase + out.slots.values.size
    let values := Bits.ofArray ((List.range callee.nslots).map fun i => roles[i]?.getD false).toArray
    let mut child : Slots := {
      values, initialized := Bits.ofArray ((List.range callee.nslots).map (fun i => decide (i < callee.arity))).toArray
      sharedMetadata := values, written := Bits.replicate callee.nslots false
      heap := { out.slots.heap with nslots := max out.slots.heap.nslots (base + callee.nslots) } }
    for (refs, i) in out.argumentRefs.zipIdx do
      child := { child with heap := MetadataCells.setLocal child.heap (base + i) refs }
      child := { child with tuples := putParts child.tuples i (keyArgs[i]?.getD default).parts }
    if directGetter then
      -- An exact getter neither allocates nor writes nor calls another
      -- function. Read the actual complete heap, without a heap-wide key or
      -- recency witnesses; every caller alias therefore remains unchanged.
      modify fun st => { st with
        active := some (g, keyArgs), cellEnabled := true, cellRefBase := base
        cellScope := g, cellGraphOwner := none, cellPath := [0] }
      let result ← expr fns infos fields callee gi child body
      modify fun st => { st with
        active := state.active, cellEnabled := state.cellEnabled, cellRefBase := state.cellRefBase
        cellScope := state.cellScope, cellGraphOwner := state.cellGraphOwner
        cellPath := state.cellPath, seen := state.seen }
      let role := (joinRole result.value result.returned).map (· || gi.metadataResult)
      let parts := if gi.metadataResult then none else
        joinParts result.value result.valueParts result.returned result.returnedParts
      let refs := if state.scalarReturns[g]?.getD false then [] else
        MetadataCells.joinRefs (if result.value.isSome then result.valueRefs else []) result.returnedRefs
      return ({ out with valueRefs := refs }, role, parts, result.yielded)
    let input : CellInput := {
      fn := g
      arguments := keyArgs
      references := out.argumentRefs
      heap := { out.slots.heap with locals := {}, nslots := 0 } }
    let index ← match (state.cellSummaryIndices[g]?.getD []).find? (fun index =>
        state.cellSummaries[index]!.input == input) with
      | some index => pure index
      | none => do
        let index := state.cellSummaries.size
        modify fun st => { st with
          cellSummaries := st.cellSummaries.push { input }
          cellSummaryIndices := st.cellSummaryIndices.insert g (index :: (st.cellSummaryIndices[g]?.getD [])) }
        pure index
    if state.cellActive.contains index then
      modify fun st => { st with cellRecursive := st.cellRecursive.insert index () }
      let effect := ((← get).cellSummaries[index]!).effect
      let heap := applyCellEffect out.slots.heap effect
      return ({ out with slots := { out.slots with heap }, valueRefs := effect.references },
        effect.role, effect.parts, effect.yielded)
    for (object, _) in input.heap.nodes do
      let heap := { child.heap with nslots := max child.heap.nslots (cellWitness base object + 1) }
      child := { child with heap := MetadataCells.setLocal heap (cellWitness base object) [object] }
    let (background, cleanups) := MetadataPlan.sites fns body
    let mut effect := ((← get).cellSummaries[index]!).effect
    repeat
      modify fun st => { st with
        active := some (g, keyArgs), cellEnabled := true, cellRefBase := base,
        cellScope := g, cellGraphOwner := none,
        cellPath := [0],
        cellActive := index :: state.cellActive }
      let result ← if background || !cleanups.isEmpty || cellConcurrentBody fns body then do
        let bodies := fns.mapIdx fun index function =>
          { function with body := (infos[index]?.getD {}).body.getD function.body }
        let plan := MetadataPlan.build bodies gi.metadataWrites callee.nslots body (some g)
          (infos.map (·.metadataWrites)) (infos.map (·.source)) (infos.map (·.borrowTasks))
        let referenceLive := MetadataLiveness.build fns plan
        schedule { fns, infos, fields, fn := callee, info := gi, plan, referenceLive } child
      else expr fns infos fields callee gi child body
      modify fun st => { st with
        active := state.active, cellEnabled := state.cellEnabled, cellRefBase := state.cellRefBase,
        cellScope := state.cellScope, cellGraphOwner := state.cellGraphOwner,
        cellPath := state.cellPath,
        cellActive := state.cellActive, seen := state.seen }
      let role := (joinRole result.value result.returned).map (· || gi.metadataResult)
      let parts := if gi.metadataResult then none else
        joinParts result.value result.valueParts result.returned result.returnedParts
      let heap := match result.value, result.returnedHeap with
        | some _, some returned => some (MetadataCells.join result.slots.heap returned)
        | none, some returned => some returned
        | some _, none => some result.slots.heap
        | none, none => none
      let refs := if state.scalarReturns[g]?.getD false then [] else
        MetadataCells.joinRefs (if result.value.isSome then result.valueRefs else []) result.returnedRefs
      let images := match heap with
        | none => {}
        | some heap => input.heap.nodes.fold (fun out object _ =>
            out.insert object (MetadataCells.getLocal heap (cellWitness base object))) {}
      let next := joinCellEffect effect {
        role, parts, references := refs
        heap := heap.map (fun heap => { heap with locals := {}, nslots := 0 })
        images
        yielded := result.yielded }
      if next == effect then break
      effect := next
      modify fun st => { st with cellSummaries := st.cellSummaries.modify index fun summary =>
        { summary with effect } }
      if !(← get).cellRecursive.contains index then break
    let heap := applyCellEffect out.slots.heap effect
    return ({ out with slots := { out.slots with heap }, valueRefs := effect.references },
      effect.role, effect.parts, effect.yielded)
  let (result, parts, yielded) ← request (g, keyArgs)
  let name := (fns[g]?.map (·.name)).getD ""
  let yielded : Bool := if name == "$Sleep" then
    match es with
    | [.lit (.float bits)] => decide (VFloat.ofBits bits > 0.0)
    | [.prim .fneg [.lit (.float bits)]] => decide (-(VFloat.ofBits bits) > 0.0)
    | _ => true
    else name == "$WaitDone" || yielded
  -- An ordinary transfer may return an alias before any private cell has
  -- been created. Preserve that possibility for later stores/observers;
  -- absence of a current private object is not a no-alias certificate.
  let refs := if state.cellEnabled && !(state.scalarReturns[g]?.getD false) then
      if cellExternal out.slots.heap out.argumentRefs.flatten then [1] else [0]
    else []
  return ({ out with valueRefs := refs }, result, parts, yielded)

private partial def concurrent (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots)
    (sync : Bool) (arms : List Expr) : M Flow := do
  -- Only cells already in scope can be shared by sibling arms. A local
  -- declared inside an arm starts fresh on each analysis of that arm.
  let shared := info.shared.filter fun i => (slots.initialized.get i)
  let entry (outs : Array Flow) (own : Nat) : Slots := Id.run do
    let mut joined := slots
    for (out, i) in outs.zipIdx do
      if i != own then
        let incoming := { out.slots with
          tuples := {}
          values := out.slots.values.mapIdx fun k role =>
            if (out.slots.written.get k) then role else (slots.values.get k)
          sharedMetadata := out.slots.sharedMetadata.mapIdx fun k role =>
            if (out.slots.written.get k) then role else (slots.sharedMetadata.get k) }
        joined := joinSlots joined incoming
    return {
      heap := joined.heap
      values := slots.values.mapIdx fun i role =>
        if shared.contains i then (joined.values.get i) else role
      initialized := slots.initialized
      written := Bits.replicate slots.values.size false
      sharedMetadata := slots.sharedMetadata.mapIdx fun i role =>
        if shared.contains i then (joined.sharedMetadata.get i) else role }
  let runArms (outs : Array Flow) : M (Array Flow) := do
    let mut next := #[]
    for (arm, i) in arms.toArray.zipIdx do
      let out ← cellChild i (expr fns infos fields fn info (entry outs i) arm)
      next := next.push out
      -- Startup runs each arm to its first wait or completion, in order.
      -- An arm that does neither holds startup; an immediate race/rush
      -- winner also prevents the remaining arms from starting.
      if !out.yielded && (out.value.isNone || !sync) then break
    return next
  -- Every arm starts independently, including when a sibling has no
  -- normal return. Exchange their shared-cell roles until they stabilize.
  let validate := (← get).validateShared
  modify fun st => { st with validateShared := false }
  let mut outs : Array Flow := arms.toArray.map fun _ => { slots }
  -- Seed from actual effects, so a definite real overwrite does not retain
  -- the entry's metadata value. Later rounds join monotonically: modes of
  -- mutually writing arms must not alternate before diagnostics can run.
  outs ← runArms outs
  let mut growing := true
  while growing do
    let raw ← runArms outs
    let next := raw.mapIdx fun i out => match outs[i]? with
      | none => out
      | some old => { out with
        slots := joinSlots old.slots out.slots
        value := joinRole old.value out.value
        valueParts := joinParts old.value old.valueParts out.value out.valueParts
        returned := joinRole old.returned out.returned
        returnedRefs := MetadataCells.joinRefs old.returnedRefs out.returnedRefs
        returnedHeap := match old.returnedHeap, out.returnedHeap with
          | some a, some b => some (MetadataCells.join a b)
          | some a, none | none, some a => some a
          | none, none => none
        returnedParts := joinParts old.returned old.returnedParts out.returned out.returnedParts
        broken := joinOpt old.broken out.broken
        yielded := old.yielded || out.yielded }
    growing := next.map (·.slots) != outs.map (·.slots)
    outs := next
  modify fun st => { st with validateShared := validate }
  if validate then outs ← runArms outs
  let mut joined : Option Slots := none
  let mut returned := none
  let mut exits : Flow := { slots, value := none }
  let mut broken := none
  for out in outs do
    joined := joinOpt joined (some out.slots)
    exits := withExits out exits
    returned := joinRole returned out.returned
    broken := joinOpt broken out.broken
  let merged := joined.getD slots
  let merged := { merged with written := slots.written.union merged.written }
  -- A successful sync completes every arm. With metadata reentry barred,
  -- any arm that definitely leaves real data makes that shared cell real.
  -- Race/rush can finish with another arm still pending, so retain may roles.
  let finalSlots := if sync then { merged with
    tuples := {}
    values := merged.values.mapIdx fun i role =>
      if shared.contains i then outs.all (fun out => (out.slots.values.get i)) else role }
    else merged
  let normal := if sync then outs.all (·.value.isSome) else outs.any (·.value.isSome)
  let yielded := if sync then
      outs.all (fun out => out.value.isSome || out.yielded) && outs.any (·.yielded)
    else outs.all (·.yielded)
  return { exits with slots := finalSlots, value := if normal then some false else none, returned, broken, yielded }

private partial def arguments (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots)
    (es : List Expr) : M (List Bool × List TupleParts × Flow) := do
  let mut out : Flow := { slots }
  let mut roles := []
  let mut parts := []
  let enabled := (← get).cellEnabled
  let scratchSite ← if enabled then cellSite fn none else pure 0
  let refBase := (← get).cellRefBase
  let scratch (index : Nat) : Nat :=
    4294967296 + cellPair (cellPair scratchSite refBase) index
  for (e, index) in es.zipIdx do
    if out.value.isNone then break
    out := withExits out (← cellChild index (expr fns infos fields fn info out.slots e))
    roles := out.value.getD false :: roles
    parts := out.valueParts :: parts
    if enabled then
      let heap := { out.slots.heap with nslots := max out.slots.heap.nslots (scratch index + 1) }
      out := { out with slots := { out.slots with
        heap := MetadataCells.setLocal heap (scratch index) out.valueRefs } }
  -- Operand evaluation goes left to right. Reverse the accumulated roles
  -- once so consumers see the same positional order as the parked aliases.
  let refs := if enabled then (List.range roles.length).map fun index =>
      MetadataCells.getLocal out.slots.heap (scratch index) else []
  -- All operands are now evaluated. Their final aliases are snapshotted
  -- above; constructors rebase those payloads on allocation, and calls bind
  -- them before executing a callee. Only this operation's consumed parking
  -- keys disappear. Outer pending operands and every exit snapshot remain.
  let heap := if enabled then
    let locals := (List.range roles.length).foldl
      (fun locals index => locals.erase (scratch index)) out.slots.heap.locals
    { out.slots.heap with locals }
    else out.slots.heap
  return (roles.reverse, parts.reverse, { out with slots := { out.slots with heap }, argumentRefs := refs })

private partial def actorEnvironment (env : ScheduleEnv) (a : Actor) : Fn × Info :=
  match a.context with
  | none => (env.fn, env.info)
  | some (g, offset) =>
    if let some cached := env.environments[(g, offset)]? then cached else
    let info := env.infos[g]?.getD {}
    let alias (i : Nat) := (env.plan.aliases.lookup (i + offset)).getD (i + offset)
    (env.fns[g]!, { info with
      inputs := info.inputs.filterMap fun i => if (env.plan.aliases.lookup (i + offset)).isSome then none else some (i + offset)
      seeds := info.seeds.filterMap fun i => if (env.plan.aliases.lookup (i + offset)).isSome then none else some (i + offset)
      uses := info.uses.map (· + offset)
      shared := info.shared.map alias
      cellSlots := info.cellSlots.map alias
      nonCellSlots := info.nonCellSlots.map alias
      nonCellMask := info.nonCellSlots.foldl (fun mask slot => mask ||| (1 <<< alias slot)) 0
      dataOnlySlots := info.dataOnlySlots.map alias
      dataOnlyMask := info.dataOnlySlots.foldl (fun mask slot => mask ||| (1 <<< alias slot)) 0
      objectFreeSlots := info.objectFreeSlots.map alias
      objectFreeMask := info.objectFreeSlots.foldl (fun mask slot => mask ||| (1 <<< alias slot)) 0
      cellParams := info.cellParams.map (· + offset)
      source := { info.source with slots := info.source.slots.map fun (i, s) => (alias i, s) }
      metadataWrites := info.metadataWrites.map fun (i, k) => (i + offset, k) })

/-- Initialization modes are observed only by shared-cell checks and by
    source-frame capture checks. Ordinary scratch slots still retain their
    value roles; their initialization history cannot affect either check.
    Include every lexical call context, resolving its source aliases, so an
    immutable borrowed capture keeps the same initialization evidence. -/
private partial def modeMask (env : ScheduleEnv) : Bits := Id.run do
  let mut result := Bits.replicate env.plan.slots false
  let contexts := (none :: env.plan.contexts.toList ++ env.plan.nodes.toList.filterMap
    (fun node => match node with | .enterCall g offset _ _ => some (some (g, offset)) | _ => none)).eraseDups
  for context in contexts do
    let (_, info) := actorEnvironment env { context }
    for i in info.shared ++ info.source.slots.map (·.1) do
      result := result.set! i true
  return result

private partial def keepModes (mask : Bits) (s : Slots) : Slots := { s with
  initialized := s.initialized.intersect mask
  sharedMetadata := s.sharedMetadata.intersect mask }

private partial def keepConfigurationModes (mask : Bits) (c : Configuration) : Configuration := { c with
  slots := keepModes mask c.slots
  tests := c.tests.map fun t => { t with slots := keepModes mask t.slots } }

/-- Current actors, deferred resumes, and signal return continuations can
    all become active. Saved transaction memories are deliberately retained. -/
private partial def restrictReferences (env : ScheduleEnv)
    (modeWords : MetadataLiveness.SlotMask) (c : Configuration) : Configuration := Id.run do
  let mut live := #[env.referenceLive.cleanup]
  for actor in c.actors do
    live := live.push (env.referenceLive.get actor.pc)
    for pc in actor.signalReturns.filterMap id do
      live := live.push (env.referenceLive.get pc)
  for step in c.pending do
    match step with
    | .cleanup _ _ pc | .resume _ pc | .returnCall _ pc | .returnScope _ _ _ _ pc =>
      live := live.push (env.referenceLive.get pc)
    | _ => pure ()
  let referenceLive (slot : Nat) : Bool :=
    let word := slot / 64
    let flag := (1 : UInt64) <<< (slot % 64).toUInt64
    live.any fun mask => (mask[word]?.getD 0 &&& flag) != 0
  -- Tuple columns, like references, are observed through local reads. Keep
  -- all source/shared cells as well as graph-live locals. Saved transaction
  -- slots remain intact until their rollback destination becomes current.
  let tupleLive (slot : Nat) : Bool :=
    let flag := (1 : UInt64) <<< (slot % 64).toUInt64
    (modeWords[slot / 64]?.getD 0 &&& flag) != 0 || referenceLive slot
  let tuples := if c.slots.tuples.all (fun i _ => tupleLive i) then c.slots.tuples
    else c.slots.tuples.filter fun i _ => tupleLive i
  return { c with
    refs := MetadataReferences.restrict c.refs referenceLive
    slots := { c.slots with tuples } }

private partial def ScheduleWork.push (w : ScheduleWork) (c : Configuration) : ScheduleWork :=
  let c := restrictReferences w.env w.modeWords (keepConfigurationModes w.modes c)
  let key := configurationKey c
  match w.pending[key]? with
  | some old => { w with pending := w.pending.insert key (joinConfiguration old c) }
  | none =>
    let rank := c.current.map (fun i =>
      (w.ranks[c.actors[i]!.pc]?.getD w.ranks.size) + 1) |>.getD 0
    { w with
      ready := w.ready.insert (rank, w.serial) key
      pending := w.pending.insert key c
      serial := w.serial + 1 }

private partial def cancelChildren (env : ScheduleEnv) (c : Configuration) (actor : Nat) (branch : Bool)
    (context : Option (Option (Nat × Nat)) := none) : List Pending :=
  c.launches.reverse.flatMap fun i =>
    let g := env.plan.groups[i]!
    let scope := if g.kind == .branch || (g.kind == .rush && !c.groups[i]!.active) then
      g.taskContext else g.context
    if g.owner == actor && g.kind != .spawn && !c.groups[i]!.late && (g.kind == .branch) == branch &&
        (context.isNone || context == some scope) then
      g.children.toList.reverse.map (fun (child, _) => .cancel child)
    else []

private partial def queue (c : Configuration) (steps : List Pending) : Configuration :=
  { c with current := none, pending := steps ++ c.pending }

/-- Spawned tasks and branches launched after an earlier stop survive that
    cancellation; other descendants belong to its cancellation tree. -/
private partial def cancellationTree (plan : MetadataPlan.Plan) (c : Configuration) (actor : Nat) : List Nat := Id.run do
  let mut found := [actor]
  repeat
    let next := plan.groups.toList.zipIdx.foldl (fun found (g, i) =>
      if g.kind != .spawn && !c.groups[i]!.late && found.contains g.owner then
        (found ++ g.children.toList.map (·.1)).eraseDups else found) found
    if next == found then return found
    found := next

private partial def cancelSteps (env : ScheduleEnv) (c : Configuration) (actor : Nat) : Configuration :=
  let a := c.actors[actor]!
  if a.canceling then c else
    let tree := cancellationTree env.plan c actor
    let active := c.signals ++ c.pending.filterMap (fun
      | .resume i _ => if c.actors[i]!.status == .running then some i else none
      | _ => none)
    if active.any tree.contains then
      let c := { c with
        events := c.events.filter (· != actor)
        actors := c.actors.modify actor fun a => { a with cancelRequested := true, event := none } }
      queue c (cancelChildren env c actor false ++ cancelChildren env c actor true)
    else
      let cleanups := if a.status == .done || a.status == .idle then [] else
        (a.cleanups.head?.toList.map fun d =>
          Pending.cleanup actor a.context env.plan.cleanupEntries[d]!) ++
        a.frames.flatMap (fun f => f.cleanups.head?.toList.map fun d =>
          Pending.cleanup actor f.context env.plan.cleanupEntries[d]!)
      let c := { c with
        events := c.events.filter (· != actor)
        actors := c.actors.modify actor fun a => { a with canceling := true, event := none } }
      -- (#724: a cancelled task's children first, the arms it waits in, its
      -- newest, then its branches, then its own cleanups, as Epic's Verse VM
      -- cancels a task: UEFN 43.12, followup-conc/branch-cancel-order and
      -- cancel-branch-before-sync-arms)
      queue c (cancelChildren env c actor false ++ cancelChildren env c actor true ++ cleanups ++
        [.stop actor])

/-- An active cancellation waits for the complete current step, including
    enclosing group continuations and fresh startup prefixes. Pending
    actions run first; a queued group resume can still finish that step. -/
private partial def readyCancellations (plan : MetadataPlan.Plan) (c : Configuration) : List Pending :=
  if !c.pending.isEmpty then [] else
    let requested := c.actors.toList.zipIdx.filterMap fun (a, i) =>
      if a.cancelRequested && !a.canceling then some i else none
    let roots := requested.filter fun i =>
      !requested.any (fun j => i != j && (cancellationTree plan c j).contains i)
    roots.filterMap fun root =>
      let tree := cancellationTree plan c root
      if tree.any (fun i => c.actors[i]!.status == .running || c.actors[i]!.status == .ready) then none
      else some (.cancel root)

private partial def finishGroup (env : ScheduleEnv) (c : Configuration)
    (group : Nat) : M Configuration := do
  let g := env.plan.groups[group]!
  let losers := if g.kind == .race then g.children.toList.reverse.filterMap fun (child, _) =>
      if some child != c.groups[group]!.winner then some (Pending.cancel child) else none
    else []
  let c := { c with
    groups := c.groups.modify group fun s => { s with active := false }
    slots := putRole c.slots g.dst false }
  return queue c (losers ++ [.resume g.owner g.next])

private partial def completeScheduled (env : ScheduleEnv) (c : Configuration)
    (actor : Nat) : M Configuration := do
  let mut c := { c with
    events := c.events.filter (· != actor)
    actors := c.actors.modify actor fun a =>
      { a with status := .done, cleanups := [], loops := [], frames := [], event := none, signalReturns := [] } }
  let parent := env.plan.groups.findIdx? fun g => g.children.any (·.1 == actor)
  if let some i := parent then
    if c.groups[i]!.active && c.groups[i]!.winner.isNone then
      c := { c with groups := c.groups.modify i fun g => { g with winner := some actor } }
  c := nextActor c
  if let some i := parent then
    let owner := env.plan.groups[i]!.owner
    if c.actors[owner]!.status == .joining i && groupReady env.plan c i then
      return ← finishGroup env c i
  return c

/-- (#724) A function's return stops none of the tasks its code started:
    its branches and the `rush` arms that went on are its task's children,
    which outlive it. They become late, out of the return's cancellation
    tree, and are analysed on after the result, as late branches are. -/
private partial def orphanBackground (plan : MetadataPlan.Plan) (c : Configuration) : Configuration :=
  { c with groups := c.groups.mapIdx fun i st =>
      match plan.groups[i]? with
      | some g => if c.launches.contains i && (g.kind == .branch || (g.kind == .rush && !st.active))
          then { st with late := true } else st
      | none => st }

/-- Branches launched after a stop are not reached by that earlier drain.
    Analyze their live descendants even after the owning result was saved. -/
private partial def liveLateBranches (plan : MetadataPlan.Plan) (c : Configuration) : Bool :=
  plan.groups.toList.zipIdx.any fun (g, i) =>
    c.groups[i]!.late && g.children.any (fun (child, _) =>
      (cancellationTree plan c child).any fun actor =>
        c.actors[actor]!.status != .done && c.actors[actor]!.status != .idle)

private partial def schedule (env : ScheduleEnv) (entry : Slots) : M Flow := do
  -- A lexical source frame has the same shifted ownership facts at every
  -- visit. Materialize it once per plan context rather than rebuilding its
  -- alias substitutions at every abstract transition.
  let mut env := env
  for context in env.plan.contexts do
    if let some key := context then
      if !env.environments.contains key then
        let value := actorEnvironment env { context }
        env := { env with environments := env.environments.insert key value }
  let refBase := (← get).cellRefBase
  let rootScope := (← get).cellScope
  let extra := env.plan.slots - entry.values.size
  let pad (a : Bits) := a.appendZeros extra
  let slots : Slots := {
    heap := { entry.heap with nslots := max entry.heap.nslots (refBase + env.plan.slots) }
    values := pad entry.values, tuples := entry.tuples, initialized := pad entry.initialized
    sharedMetadata := pad entry.sharedMetadata, written := pad entry.written }
  let initial : Configuration := {
    slots
    refs := MetadataReferences.initial env.plan.slots fun i =>
      if i < env.fn.arity then [i + 2] else []
    actors := (Array.replicate env.plan.actors {}).set! 0 {
      pc := env.plan.entry, status := .running }
    groups := Array.replicate env.plan.groups.size {} }
  modify fun st => { st with seen := st.seen.appendZeros extra }
  let modes := modeMask env
  let initialWork : ScheduleWork := {
    env, modes
    modeWords := MetadataLiveness.pack modes.bits
    ranks := MetadataLiveness.controlOrder env.plan }
  let mut work := initialWork.push initial
  let mut cursor := 0
  let mut known : Std.HashMap (Array Nat) Configuration := {}
  let mut result : Option Bool := none
  let mut resultParts : TupleParts := none
  let mut resultRefs : MetadataCells.Refs := []
  let mut finalSlots : Option Slots := none
  let mut yielded := false
  -- (#724: the check of metadata entering a shared local, relaxed for the
  -- steps of tasks that outlive their returned owner, below)
  let baseValidateShared := (← get).validateShared
  while !work.ready.isEmpty do
    if (← get).debug && cursor % 10000 == 0 then
      dbg_trace s!"metadata schedule {env.fn.name}: visited={cursor}, queued={cursor + work.pending.size}, states={known.size}"
    let (ticket, key) := work.ready.minEntry!
    let incoming := work.pending[key]!
    work := { work with ready := work.ready.erase ticket, pending := work.pending.erase key }
    cursor := cursor + 1
    let prior := known[key]?
    let c := match prior with
      | none => incoming
      | some old => if old == incoming then old else joinConfiguration old incoming
    if prior.any (· == c) then continue
    known := known.insert key c
    let stops := readyCancellations env.plan c
    if !stops.isEmpty then
      work := work.push (queue c stops)
      continue
    if c.pending.isEmpty && c.actors[0]!.status == .done &&
        !(c.actors.any fun a => a.cancelRequested && !a.canceling) &&
        !liveLateBranches env.plan c then continue
    let some actor := c.current | do
      if let step :: rest := c.pending then
        let c := { c with pending := rest }
        match step with
        | .cancel a => work := work.push (cancelSteps env c a)
        | .cleanup a context pc =>
          if c.actors[a]!.status == .done then continue
          let c := { c with actors := c.actors.modify a fun a =>
            { a with context, cleanups := [], loops := [] } }
          work := work.push (advanceActor c a pc)
        | .stop a =>
          let c := match c.actors[a]!.task with
            | some task => if !(taskOptions c task).contains 2 then setTask c task 4 else c
            | none => c
          work := work.push { c with
            signals := c.signals.filter (· != a)
            events := c.events.filter (· != a)
            actors := c.actors.modify a fun a =>
              { a with status := .done, cleanups := [], loops := [], frames := [], event := none, signalReturns := [] } }
        | .resume a pc =>
          if !(c.actors[a]!.canceling && c.actors[a]!.status == .done) then
            work := work.push (advanceActor c a pc)
        | .returnScope a fn offset dropFrames pc =>
          if c.actors[a]!.canceling && c.actors[a]!.status == .done then continue
          let c := { c with actors := c.actors.modify a fun a =>
            { a with
              context := some (fn, offset), cleanups := [], loops := []
              frames := a.frames.drop dropFrames, signalReturns := [] } }
          work := work.push (advanceActor c a pc)
        | .returnCall a pc =>
          let task := c.actors[a]!
          if let frame :: rest := task.frames then
            let c := { c with actors := c.actors.modify a fun t =>
              { t with
                context := frame.context, cleanups := frame.cleanups
                loops := frame.loops, frames := rest } }
            work := work.push (advanceActor c a pc)
        | .result role parts slot =>
          -- The result is already saved, but an active cancelled arm can
          -- still install and execute cleanup before its next suspension.
          resultParts := joinParts result resultParts (some role) parts
          if let some slot := slot then
            resultRefs := MetadataCells.joinRefs resultRefs (MetadataCells.getLocal c.slots.heap (refBase + slot))
          result := joinRole result (some role)
          finalSlots := joinOpt finalSlots (some c.slots)
          if (c.actors.any fun a => a.cancelRequested && !a.canceling) ||
              liveLateBranches env.plan c then
            work := work.push c
        | .discard =>
          if (c.actors.any fun a => a.cancelRequested && !a.canceling) ||
              liveLateBranches env.plan c then
            work := work.push c
        continue
      if !c.startup.isEmpty then
        work := work.push (nextActor c)
        continue
      if c.signals.head? == some c.actors.size then
        work := work.push { c with signals := c.signals.tail }
        continue
      for transition in poolTransitions env.plan c .global do work := work.push transition
      if c.actors.any (fun a => match a.status with
          | .waiting _ | .joining _ => true | _ => false) then
        yielded := true
        work := work.push (queue c [.cancel 0, .discard])
        -- A surviving branch can later be stopped by its still-live task.
        -- The creator's completed drain no longer reaches that cleanup.
        for (g, i) in env.plan.groups.toList.zipIdx do
          if c.groups[i]!.late then
            for (child, _) in g.children do
              work := work.push (queue c [.cancel child, .discard])
        for i in [:c.actors.size] do
          let a := c.actors[i]!
          let resumableTask := !a.taskWait || a.event.any (fun task =>
            (taskOptions c task).any (fun state => state == 1 || state == 2))
          if a.status == .waiting true && !a.canceling && !a.cancelRequested && resumableTask then
            work := work.push (advanceActor c i c.actors[i]!.pc)
      continue
    let a := c.actors[actor]!
    let lexical := env.plan.contexts[a.pc]?.getD a.context
    let (fn, info) := actorEnvironment env { a with context := lexical }
    let node := env.plan.nodes[a.pc]!
    let boundary := match node with
      | .call g args _ _ _ =>
        let name := env.fns[g]!.name
        let receiver := objectRefs (args.head?.map (fun i => (MetadataReferences.get c.refs i)) |>.getD [0])
        if name == "$signalAll" || MetadataPlan.isEventSignal env.fns g then
          some (PoolCause.event receiver)
        else if name == "$cancelMark" then some (.cancel receiver)
        else if !c.signals.isEmpty then some .inside else none
      | .finishTask _ => some (.task (a.task.getD [0]))
      | .drained => none
      | _ => if !c.signals.isEmpty then some .inside else none
    if let some cause := boundary then
      for transition in poolTransitions env.plan c cause do work := work.push transition
    modify fun st => { st with
      cellPath := [a.pc], cellGraphOwner := some rootScope,
      cellScope := lexical.map (·.1) |>.getD rootScope }
    -- (#724) once the owner has returned, the tasks its code started go on
    -- (`orphanBackground`); only they can read its frame's shared locals
    -- then, so metadata entering one is checked where they execute it,
    -- not refused as it enters; so too once the owner is being cancelled,
    -- whose children's cleanups run before its own (`cancelSteps`), which
    -- are checked where they execute it
    let orphaned := actor != 0 &&
      (c.actors[0]?.map (fun a => a.status == .done || a.canceling)).getD false
    modify fun st => { st with validateShared := baseValidateShared && !orphaned }
    match node with
    | .jump pc => work := work.push (advanceActor c actor pc)
    | .atom e dst next permission =>
      let info := match permission with
        | none => info
        | some p => { info with metadataWrites := p :: info.metadataWrites }
      let out ← expr env.fns env.infos env.fields fn info c.slots e
      if let some role := out.value then
        let (refs, memory) := MetadataReferences.eval env.fns a.pc c.refs e (← get).scalarReturns
        let changed := { c with
          slots := { putRole out.slots dst role out.valueParts with
            heap := MetadataCells.setLocal out.slots.heap (refBase + dst) out.valueRefs }
          refs := MetadataReferences.set memory dst refs }
        work := work.push (advanceActor changed actor next)
      if out.value.isNone || mayFail e then
        if let some restored := restoreTest c actor then work := work.push restored
    | .test condition yes no =>
      let out ← expr env.fns env.infos env.fields fn info c.slots condition
      if out.value.isSome then
        work := work.push (advanceActor { c with slots := out.slots } actor yes)
      work := work.push (advanceActor c actor no)
    | .beginTest no next =>
      let snapshot : Snapshot := {
        owner := actor, no, slots := c.slots, refs := c.refs
        actors := c.actors, groups := c.groups, startup := c.startup
        events := c.events, pending := c.pending, launches := c.launches
        tasks := c.tasks, taskResults := c.taskResults, pools := c.pools, signals := c.signals }
      work := work.push (advanceActor { c with tests := snapshot :: c.tests } actor next)
    | .passTest next =>
      work := work.push (advanceActor { c with tests := c.tests.tail } actor next)
    | .enterCall g offset args next =>
      let (out, _, _, _) ← invoke env.fns env.infos env.fields fn info c.slots g (args.map Expr.local) false
      if out.value.isNone then continue
      let callee := env.fns[g]!
      let ci := env.infos[g]?.getD {}
      let mut slots := out.slots
      let mut refs := c.refs
      for i in [:callee.nslots] do
        slots := { slots with
          values := slots.values.set! (offset + i) false
          tuples := slots.tuples.erase (offset + i)
          initialized := slots.initialized.set! (offset + i) false
          sharedMetadata := slots.sharedMetadata.set! (offset + i) false }
        refs := MetadataReferences.set refs (offset + i) []
        slots := { slots with heap := MetadataCells.setLocal slots.heap (refBase + offset + i) [] }
      for (source, i) in args.zipIdx do
        slots := putRole slots (offset + i) ((c.slots.values.get source) || ci.inputs.contains i)
          (if ci.inputs.contains i then none else c.slots.tuples[source]?)
        refs := MetadataReferences.set refs (offset + i) ((MetadataReferences.get c.refs source))
        slots := { slots with
          heap := MetadataCells.setLocal slots.heap (refBase + offset + i)
            (MetadataCells.getLocal c.slots.heap (refBase + source)) }
      let frame : CallFrame := { context := a.context, cleanups := a.cleanups, loops := a.loops }
      let c := { c with slots, refs, actors := c.actors.modify actor fun a =>
        { a with context := some (g, offset), cleanups := [], loops := [], frames := frame :: a.frames } }
      work := work.push (advanceActor c actor next)
    | .leaveCall dst next =>
      let metadata := a.context.any (fun (g, _) => (env.infos[g]?.getD {}).metadataResult)
      let c := if metadata then { c with slots := putRole c.slots dst true } else c
      work := work.push (queue c (cancelChildren env c actor false (some a.context) ++
        cancelChildren env c actor true (some a.context) ++ [.returnCall actor next]))
    | .cleanupDone =>
      work := work.push { c with current := none }
    | .drained =>
      if let resume :: returns := a.signalReturns then
        let c := { c with signals := c.signals.tail, actors := c.actors.modify actor fun a =>
          { a with signalReturns := returns } }
        match resume with
        | some next => work := work.push (advanceActor c actor next)
        | none => work := work.push (← completeScheduled env c actor)
    | .choose yes no =>
      work := work.push (advanceActor c actor yes)
      work := work.push (advanceActor c actor no)
    | .accumulate dst value next =>
      let role := (c.slots.values.get dst).or (c.slots.values.get value)
      work := work.push (advanceActor { c with
        slots := putRole c.slots dst role
        refs := MetadataReferences.accumulate c.refs a.pc dst value } actor next)
    | .call g args original dst next =>
      let (out, role, parts, mayYield) ← invoke env.fns env.infos env.fields fn info
        c.slots g (args.map Expr.local)
      if out.value.isNone then continue
      let name := (env.fns[g]?.map (·.name)).getD ""
      let duration := if name == "$Sleep" then original.head?.bind constantSleep else none
      let mayYield := if name == "$Sleep" then
          duration.map (fun n => decide (n > 0.0)) |>.getD true
        else mayYield
      let mustYield := name == "$EvAwait" ||
        (name == "$Sleep" && duration.any (fun n => decide (n > 0.0)))
      let slots := match role with
        | some role => { putRole out.slots dst role parts with
            heap := MetadataCells.setLocal out.slots.heap (refBase + dst) out.valueRefs }
        | none => out.slots
      let (references, memory) := MetadataReferences.call env.fns a.pc c.refs g
        (args.map fun i => (MetadataReferences.get c.refs i)) (← get).scalarReturns
      let c := { c with slots, refs := MetadataReferences.set memory dst references }
      let signaling := name == "$signalAll" ||
        (MetadataPlan.isEventSignal env.fns g && env.plan.signalFns[g]?.getD false)
      if name == "$Await" then
        let task := objectRefs (args.head?.map (fun i => (MetadataReferences.get c.refs i)) |>.getD [0])
        let options := taskOptions c task
        if options.contains 2 && role.isSome then
          let value := task.foldl (fun result task => unionRefs result (c.taskResults[task]?.getD [0])) []
          let c := { c with refs := MetadataReferences.set c.refs dst value }
          work := work.push (advanceActor c actor next)
        if options.contains 1 || options.contains 4 then
          let waiting := { c with
            events := c.events ++ [actor]
            actors := c.actors.modify actor fun a =>
              { a with
                pc := next, status := .waiting (options.contains 1 && role.isSome)
                event := some task, taskWait := true, waitDst := some dst } }
          work := work.push (nextActor waiting)
      else if name == "$cancelMark" then
        let task := objectRefs (args.head?.map (fun i => (MetadataReferences.get c.refs i)) |>.getD [0])
        let options := taskOptions c task
        if options.contains 2 then work := work.push (advanceActor (setTask c task 2) actor next)
        if options.contains 1 || options.contains 4 then
          let mut choices := [([] : List Pending)]
          for (taskActor, i) in c.actors.toList.zipIdx do
            let some identity := taskActor.task | continue
            if taskActor.status == .done || !MetadataReferences.aliases task identity then continue
            let certain := MetadataReferences.definitelyAliases c.refs task identity
            choices := choices.flatMap fun stops =>
              if certain then [stops ++ [.cancel i]] else [stops, stops ++ [.cancel i]]
          for stops in choices do
            work := work.push (queue (setTask c task 4) (stops ++ [.resume actor next]))
      else if signaling then
        let event := objectRefs (args.head?.map (fun i => (MetadataReferences.get c.refs i)) |>.getD [0])
        let payload := args[1]?.map (fun i => (MetadataReferences.get c.refs i))
        for awake in wake (beginSignal env.plan c actor (some next)) event false payload do work := work.push awake
      else if env.plan.signalFns[g]?.getD false then
        -- A recursive edge uses a finite may-signal summary instead of
        -- growing an unbounded stack of cloned frames. Repeat the edge
        -- nondeterministically to include repeated signals and re-awaits.
        let signatures ← match (← get).signalArguments with
          | some signatures => pure signatures
          | none => do
            let signatures := MetadataReferences.signalArguments env.fns
            modify fun st => { st with signalArguments := some signatures }
            pure signatures
        let roots := (signatures[g]?.getD []).flatMap fun i =>
          args[i]?.map (fun slot => (MetadataReferences.get c.refs slot)) |>.getD []
        let event := MetadataReferences.reachable c.refs roots
        if role.isSome then work := work.push (advanceActor c actor next)
        for awake in wake (beginSignal env.plan c actor (some a.pc)) event do
          if awake.current != some actor then work := work.push awake
        if mayYield then
          work := work.push (nextActor { c with actors := c.actors.modify actor fun a =>
            { a with pc := a.pc, status := .waiting role.isSome } })
      else
        if !mustYield && role.isSome then
          work := work.push (advanceActor c actor next)
        if mayYield then
          let event := if name == "$EvAwait" || name == "$StickyAwait" then
              some (objectRefs (args.head?.map (fun i => (MetadataReferences.get c.refs i)) |>.getD [0]))
            else none
          let waiting := { c with
            events := if event.isSome then c.events ++ [actor] else c.events
            actors := c.actors.modify actor fun a =>
              { a with pc := next, status := .waiting role.isSome, event, taskWait := false, waitDst := some dst } }
          work := work.push (nextActor waiting)
      if env.fns[g]!.decides then
        if let some restored := restoreTest c actor then work := work.push restored
    | .pushCleanup d next =>
      let c := { c with actors := c.actors.modify actor fun a =>
        { a with cleanups := d :: a.cleanups } }
      work := work.push (advanceActor c actor next)
    | .popCleanup next =>
      let c := { c with actors := c.actors.modify actor fun a =>
        { a with cleanups := a.cleanups.tail } }
      work := work.push (advanceActor c actor next)
    | .enterLoop scope next =>
      let c := { c with actors := c.actors.modify actor fun a =>
        { a with loops := {
          id := scope, cells := loopCells info.shared c.slots, cleanups := a.cleanups } :: a.loops } }
      work := work.push (advanceActor c actor next)
    | .backLoop scope next =>
      let entry := (a.loops.find? (·.id == scope)).getD {
        id := scope, cells := loopCells info.shared c.slots, cleanups := a.cleanups }
      let c := { c with
        slots := restoreLoopCells entry.cells c.slots
        actors := c.actors.modify actor fun a => { a with cleanups := entry.cleanups } }
      work := work.push (advanceActor c actor next)
    | .leaveLoop scope next =>
      let cleanups := (a.loops.find? (·.id == scope)).map (·.cleanups) |>.getD a.cleanups
      let c := { c with actors := c.actors.modify actor fun a =>
        { a with cleanups, loops := (a.loops.dropWhile (·.id != scope)).tail } }
      work := work.push (advanceActor c actor next)
    | .fork group =>
      let g := env.plan.groups[group]!
      let mut c := c
      if g.kind == .spawn then
        for (child, _) in g.children do c := capturePool env.plan c group child
      let mut canComplete := false
      let mut canSignal := false
      if let some target := g.target then
        let (_, role, _, _) ← invoke env.fns env.infos env.fields fn info c.slots target
          (g.arguments.map Expr.local)
        canComplete := role.isSome
        canSignal := env.plan.signalFns[target]?.getD false
      let mut actors := c.actors
      for (child, pc) in g.children do
        actors := actors.set! child {
          pc, context := a.context, canComplete, canSignal
          task := g.task.map fun slot => (MetadataReferences.get c.refs slot) }
      let started := { c with
        actors, groups := c.groups.set! group {
          active := true
          late := g.kind == .branch && c.actors.toList.zipIdx.any (fun (owner, i) =>
            owner.cancelRequested && !owner.canceling && (cancellationTree env.plan c i).contains actor) }
        launches := c.launches.filter (· != group) ++ [group] }
      let started := g.task.map (fun slot => setTask started (MetadataReferences.get started.refs slot) 1) |>.getD started
      work := work.push (advanceActor started actor g.advance)
    | .advance group =>
      let g := env.plan.groups[group]!
      let state := c.groups[group]!
      if groupReady env.plan c group then
        work := work.push (← finishGroup env c group)
      else if state.started < g.children.size then
        let (child, pc) := g.children[state.started]!
        let c := { c with
          startup := actor :: c.startup
          groups := c.groups.modify group fun g => { g with started := g.started + 1 } }
        work := work.push (advanceActor c child pc)
      else
        let c := { c with actors := c.actors.modify actor fun a =>
          { a with status := .joining group } }
        work := work.push (nextActor c)
    | .spawnCheck g args next =>
      let (_, role, _, _) ← invoke env.fns env.infos env.fields fn info c.slots g (args.map Expr.local)
      if (← get).validateUses && role.getD false then
        refuse fn info "enter a spawned task's result field containing executable data"
      work := work.push (advanceActor c actor next)
    | .finishTask value =>
      if (← get).validateUses && (c.slots.values.get value) then
        refuse fn info "enter a spawned task's result field containing executable data"
      let task := a.task.getD [0]
      let c := setTask c task 2 (some ((MetadataReferences.get c.refs value)))
      for awake in wake (beginSignal env.plan c actor none) task true
          (some ((MetadataReferences.get c.refs value))) do work := work.push awake
    | .finish value =>
      if actor == 0 then
        let role := (c.slots.values.get value)
        let c := orphanBackground env.plan { c with actors := c.actors.modify actor fun a =>
          { a with status := .done, cleanups := [] } }
        work := work.push (queue c [.cancel 0, .result role c.slots.tuples[value]? (if (← get).cellEnabled then some value else none)])
      else
        work := work.push (← completeScheduled env c actor)
    | .functionReturn owner value dst next target offset =>
      if let some late := lateReturnActor env.plan c actor owner then
        work := work.push (queue c [.cancel late])
        continue
      let caller := c.actors[owner]!
      let targetContext := some (target, offset)
      let mut context := caller.context
      let mut cleanups := caller.cleanups
      let mut frames := caller.frames
      let mut dropFrames := 0
      let mut steps := []
      while context != targetContext && !frames.isEmpty do
        let cleanup := cleanups.head?.toList.map fun d =>
          Pending.cleanup owner context env.plan.cleanupEntries[d]!
        steps := steps ++ cancelChildren env c owner false (some context) ++ cleanup ++
          cancelChildren env c owner true (some context)
        let frame := frames.head!
        context := frame.context
        cleanups := frame.cleanups
        frames := frames.tail
        dropFrames := dropFrames + 1
      let cleanup := if owner == actor then [] else cleanups.head?.toList.map fun d =>
        Pending.cleanup owner targetContext env.plan.cleanupEntries[d]!
      steps := steps ++ cancelChildren env c owner false (some targetContext) ++ cleanup ++
        cancelChildren env c owner true (some targetContext)
      let c := { c with
        slots := { putRole c.slots dst (c.slots.values.get value) c.slots.tuples[value]? with
          heap := MetadataCells.setLocal c.slots.heap (refBase + dst)
            (MetadataCells.getLocal c.slots.heap (refBase + value)) }
        refs := MetadataReferences.set c.refs dst (MetadataReferences.get c.refs value)
        events := c.events.filter (fun a => a != owner && a != actor)
        signals := c.signals.filter (fun a => a != owner && a != actor)
        startup := c.startup.filter (fun a => a != owner && a != actor)
        actors := c.actors.modify owner fun a =>
          { a with status := .running, event := none, signalReturns := [] } }
      let c := if owner == actor then { c with actors := c.actors.modify actor fun a =>
          { a with cleanups := [] } }
        else { c with actors := c.actors.modify actor fun a =>
            { a with status := .done, cleanups := [], loops := [], frames := [], signalReturns := [] } }
      work := work.push (queue c (steps ++ [.returnScope owner target offset dropFrames next]))
    | .ret value =>
      if let some late := lateReturnActor env.plan c actor 0 then
        work := work.push (queue c [.cancel late])
        continue
      let role := (c.slots.values.get value)
      let c := orphanBackground env.plan { c with actors := c.actors.modify actor fun a =>
        { a with status := .done, cleanups := [] } }
      work := work.push (queue c [.cancel 0, .result role c.slots.tuples[value]? (if (← get).cellEnabled then some value else none)])
  modify fun st => { st with validateShared := baseValidateShared }
  return { slots := finalSlots.getD slots, value := result, valueParts := resultParts, valueRefs := resultRefs, yielded }
end

/-- Check executable effects throughout the cleanup's call contexts without
    publishing those contexts as live. The caller's schedule determines
    whether cleanup and its calls can actually run. -/
private def probeCleanup (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots)
    (cleanup : Expr) (state : State) : Except String State := do
  let action : M Unit := do
    discard <| expr fns infos fields fn info slots cleanup
    let mut index := 0
    while index < (← get).live.size do
      let (i, args) := (← get).live[index]!
      index := index + 1
      let some callee := fns[i]? | throw "internal: cleanup call has no body"
      let ci := infos[i]?.getD {}
      let values := (List.range callee.nslots).map (fun j =>
        ci.inputs.contains j || (args[j]?.getD default).role) |>.toArray |> Bits.ofArray
      let entry : Slots := {
        values, sharedMetadata := values
        tuples := args.zipIdx.foldl (fun tuples (arg, j) =>
          putParts tuples j (if ci.inputs.contains j then none else arg.parts)) {}
        initialized := (List.range callee.nslots).map
          (fun j => j < callee.arity : Nat → Bool) |>.toArray |> Bits.ofArray
        written := Bits.replicate callee.nslots false }
      modify fun st => { st with seen := values }
      discard <| expr fns infos fields callee ci entry (ci.body.getD callee.body)
      let observed := (← get).seen
      let possible := { entry with
        values := observed, tuples := {}, initialized := Bits.replicate callee.nslots true
        sharedMetadata := Bits.replicate callee.nslots false }
      for d in ((← get).sites[i]?.getD (false, [])).2 do
        discard <| expr fns infos fields callee ci possible d
  let (_, result) ← action.run { state with
    discovery := false, validateUses := true, validateShared := true
    live := #[], liveSeen := {} }
  return result

/-- Copies into local slots cannot publish a value or run another actor.
    Return whether there was a write; calls, heap accesses and exits are excluded. -/
private partial def rollbackLocalCopies : Expr → Option Bool
  | .lit _ | .local _ => some false
  | .assign _ value => if (rollbackLocalCopies value).isSome then some true else none
  | .seq left right => do
    let left ← rollbackLocalCopies left
    let right ← rollbackLocalCopies right
    pure (left || right)
  | _ => none

/-- A literal failure after local copies rolls those copies back before
    any observer can run. Require an actual write: bare failures also form
    structural markers, including compiler-owned cleanup registrations. -/
private partial def failsAfterLocalCopies (condition : Expr) (written : Bool := false) : Bool :=
  match condition with
  | .prim .query [.lit (.logic false)] | .prim .query [.lit .none] => written
  | .prim .fail [] => written
  | .seq left right =>
    match rollbackLocalCopies left with
    | some copied => failsAfterLocalCopies right (written || copied)
    | none => false
  | _ => false

/-- This changes only the compiler's provenance view, never runtime Core.
    A source-frame cell may temporarily contain metadata in a failed test;
    no call, heap access, suspension or cleanup is hidden by this rule. -/
private partial def withoutRolledBackCopies : Expr → Expr
  | .ite condition yes no =>
    if failsAfterLocalCopies condition then withoutRolledBackCopies no else
      .ite (withoutRolledBackCopies condition) (withoutRolledBackCopies yes) (withoutRolledBackCopies no)
  | .assign slot value => .assign slot (withoutRolledBackCopies value)
  | .seq left right => .seq (withoutRolledBackCopies left) (withoutRolledBackCopies right)
  | .call fn args => .call fn (args.map withoutRolledBackCopies)
  | .prim op args => .prim op (args.map withoutRolledBackCopies)
  | .heap op args => .heap op (args.map withoutRolledBackCopies)
  | .forE slot source filter body =>
    .forE slot (withoutRolledBackCopies source) (withoutRolledBackCopies filter) (withoutRolledBackCopies body)
  | .loop body => .loop (withoutRolledBackCopies body)
  | .ret value => .ret (withoutRolledBackCopies value)
  | .print value => .print (withoutRolledBackCopies value)
  | other => other

/-- Private-frame dead stores cannot cross an explicit frame export,
    concurrent group, cancellation boundary or cleanup registration. -/
private partial def privateStoreBarrier (fns : Array Fn) : Expr → Bool
  | .seq (.ite (.prim .fail []) _ (.lit .void)) _ => true
  | .heap (.get slot) [] => slot == FrameRefs.currentSlot
  | .call g args =>
    (fns[g]?).isNone || ["$branchMark", "$syncMark", "$raceMark", "$rushMark", "$spawnMark", "$cancelMark", "$signalAll"].contains
      ((fns[g]?.map (·.name)).getD "") || MetadataPlan.isEventSignal fns g ||
      args.any (privateStoreBarrier fns)
  | .assign _ value | .loop value | .ret value | .print value => privateStoreBarrier fns value
  | .seq left right => privateStoreBarrier fns left || privateStoreBarrier fns right
  | .prim _ args | .heap _ args => args.any (privateStoreBarrier fns)
  | .ite condition yes no =>
    privateStoreBarrier fns condition || privateStoreBarrier fns yes || privateStoreBarrier fns no
  | .forE _ source filter body =>
    privateStoreBarrier fns source || privateStoreBarrier fns filter || privateStoreBarrier fns body
  | _ => false

/-- Observer/export facts include physical lowering code and transitives:
    a source-level call name alone cannot establish that its callee is inert. -/
private def privateStoreBarriers (fns : Array Fn) (infos : Array Info) : Array Bool := Id.run do
  let bodies := fns.mapIdx fun index fn => (infos[index]?.getD {}).body.getD fn.body
  let calls := fns.mapIdx fun index fn => MetadataPlan.calls fn.body ++ MetadataPlan.calls bodies[index]!
  let mut barriers := fns.mapIdx fun index fn =>
    privateStoreBarrier fns fn.body || privateStoreBarrier fns bodies[index]!
  let mut callers := Array.replicate fns.size ([] : List Nat)
  for index in [:fns.size] do
    for callee in calls[index]! do
      if callee < fns.size then
        callers := callers.modify callee (index :: ·)
  let mut queue := (List.range fns.size).filter (fun index => barriers[index]!) |>.toArray
  let mut next := 0
  while next < queue.size do
    let callee := queue[next]!
    next := next + 1
    for caller in callers[callee]! do
      if !barriers[caller]! then
        barriers := barriers.set! caller true
        queue := queue.push caller
  return barriers

/-- References from a different function protect an entire source owner.
    Compute them once rather than rescanning the program for every local. -/
private def referencedPrivateOwners (fns : Array Fn) (infos : Array Info) : Std.HashMap String Bool := Id.run do
  let mut owners := {}
  for index in [:fns.size] do
    let fn := fns[index]!
    let source := (infos[index]?.getD {}).source
    for (_, origin) in source.slots do
      if origin.frame != fn.name then owners := owners.insert origin.frame true
    for origin in source.forwarded do
      if origin.frame != fn.name then owners := owners.insert origin.frame true
  return owners

/-- A write-only local in a fresh, unexported owner frame has no observer.
    Keep every parameter, seed, protocol copy, reader and borrowed frame.
    A single foreign reference conservatively protects the whole owner. -/
private def privateWriteOnlySlots (fns : Array Fn) (infos : Array Info) (barriers : Array Bool)
    (referencedOwners : Std.HashMap String Bool) (index : Nat) : List Nat := Id.run do
  let some fn := fns[index]? | return []
  let info := infos[index]?.getD {}
  if info.source.slots.isEmpty || info.shared.isEmpty then return []
  let body := info.body.getD fn.body
  if !info.source.forwarded.isEmpty || info.borrowTasks ||
      info.source.slots.any (fun (_, origin) => origin.frame != fn.name) || barriers[index]?.getD true then return []
  if referencedOwners.contains fn.name then return []
  let reads := MetadataPlan.reads body ++ MetadataPlan.reads fn.body
  return info.source.slots.filterMap fun (slot, origin) =>
    if origin.frame == fn.name && slot >= fn.arity && info.shared.contains slot &&
        !info.inputs.contains slot && !info.required.contains slot && !info.seeds.contains slot &&
        !info.uses.contains slot && !reads.contains slot &&
        !info.source.slots.any (fun (other, alias) => other != slot &&
          alias.frame == origin.frame && alias.name == origin.name) &&
        !info.source.copies.any (fun copy => copy.target == slot || copy.result == slot) then some slot else none

/-- Only a dead destination disappears; its RHS still runs and retains its
    value/provenance, including any calls, errors or metadata execution. -/
private partial def withoutPrivateDeadStores (dead : List Nat) : Expr → Expr
  | .assign slot value =>
    let value := withoutPrivateDeadStores dead value
    if dead.contains slot then value else .assign slot value
  | .seq left right => .seq (withoutPrivateDeadStores dead left) (withoutPrivateDeadStores dead right)
  | .call fn args => .call fn (args.map (withoutPrivateDeadStores dead))
  | .prim op args => .prim op (args.map (withoutPrivateDeadStores dead))
  | .heap op args => .heap op (args.map (withoutPrivateDeadStores dead))
  | .ite condition yes no => .ite (withoutPrivateDeadStores dead condition)
      (withoutPrivateDeadStores dead yes) (withoutPrivateDeadStores dead no)
  | .forE slot source filter body => .forE slot (withoutPrivateDeadStores dead source)
      (withoutPrivateDeadStores dead filter) (withoutPrivateDeadStores dead body)
  | .loop body => .loop (withoutPrivateDeadStores dead body)
  | .ret value => .ret (withoutPrivateDeadStores dead value)
  | .print value => .print (withoutPrivateDeadStores dead value)
  | other => other

private partial def cellConstructor (tag : Nat) : Expr → Bool
  | .heap (.new actual) _ => actual == tag
  | .assign _ value | .loop value | .ret value | .print value => cellConstructor tag value
  | .seq left right => cellConstructor tag left || cellConstructor tag right
  | .call _ args | .prim _ args | .heap _ args => args.any (cellConstructor tag)
  | .ite condition yes no => cellConstructor tag condition || cellConstructor tag yes || cellConstructor tag no
  | .forE _ source filter body => cellConstructor tag source || cellConstructor tag filter || cellConstructor tag body
  | _ => false

/-- Incoming private references need interpretation even when this body
    never constructs a cell. Only a Source-certified local receiver excludes
    a possible payload read; unknown inline projections remain conservative. -/
private partial def cellPotentialRead (info : Info) : Expr → Bool
  | .heap (.get 0) [receiver] =>
    let excluded := match receiver with
      | .local slot => info.nonCellMask.testBit slot
      | _ => false
    !excluded || cellPotentialRead info receiver
  | .assign _ value | .loop value | .ret value | .print value => cellPotentialRead info value
  | .seq left right => cellPotentialRead info left || cellPotentialRead info right
  | .call _ args | .prim _ args | .heap _ args => args.any (cellPotentialRead info)
  | .ite condition yes no => cellPotentialRead info condition || cellPotentialRead info yes || cellPotentialRead info no
  | .forE _ source filter body => cellPotentialRead info source || cellPotentialRead info filter || cellPotentialRead info body
  | _ => false

private def cellCapabilities (fns : Array Fn) (infos : Array Info) (tag : Option Nat) : Array Bool := Id.run do
  let some tag := tag | return Array.replicate fns.size false
  let mut capable := fns.mapIdx fun i fn =>
    let info := infos[i]?.getD {}
    let body := info.body.getD fn.body
    !info.cellSlots.isEmpty || !info.cellParams.isEmpty || cellConstructor tag body || cellPotentialRead info body
  let mut callers := Array.replicate fns.size ([] : List Nat)
  for index in [:fns.size] do
    for callee in MetadataPlan.calls ((infos[index]?.getD {}).body.getD fns[index]!.body) do
      if callee < fns.size then callers := callers.modify callee (index :: ·)
  let mut queue := (List.range fns.size).filter (fun i => capable[i]!) |>.toArray
  let mut cursor := 0
  while cursor < queue.size do
    let callee := queue[cursor]!
    cursor := cursor + 1
    for caller in callers[callee]! do
      if !capable[caller]! then
        capable := capable.set! caller true
        queue := queue.push caller
  return capable

private partial def cellReferenceLiteral (cleanPrototypes : Array Bool) : Expr → Bool
  | .lit value => MetadataValues.hasUnsafeObjectRef cleanPrototypes value
  | .assign _ value | .loop value | .ret value | .print value => cellReferenceLiteral cleanPrototypes value
  | .seq left right => cellReferenceLiteral cleanPrototypes left || cellReferenceLiteral cleanPrototypes right
  | .call _ args | .prim _ args | .heap _ args => args.any (cellReferenceLiteral cleanPrototypes)
  | .ite condition yes no => cellReferenceLiteral cleanPrototypes condition || cellReferenceLiteral cleanPrototypes yes || cellReferenceLiteral cleanPrototypes no
  | .forE _ source filter body => cellReferenceLiteral cleanPrototypes source || cellReferenceLiteral cleanPrototypes filter || cellReferenceLiteral cleanPrototypes body
  | _ => false

/-- Completed-transfer reuse excludes every transitive protocol whose
    validation observes scheduler, borrowed-frame or callback state. -/
private def closedTransferSafety (fns : Array Fn) (infos : Array Info) (referencedOwners : Std.HashMap String Bool) : Array Bool := Id.run do
  let mut excluded := fns.mapIdx fun i fn =>
    let info := infos[i]?.getD {}
    let body := info.body.getD fn.body
    let protocolName (name : String) : Bool :=
      ["$Sleep", "$WaitDone", "$EvAwait", "$StickyAwait", "$Await", "$cancelMark", "$signalAll"].contains name
    let unsafeBody (body : Expr) : Bool :=
      let (background, cleanups) := MetadataPlan.sites fns body
      background || !cleanups.isEmpty || cellConcurrentBody fns body ||
        (MetadataPlan.calls body).any (fun g =>
          g ≥ fns.size || MetadataPlan.isEventSignal fns g ||
          protocolName ((fns[g]?.map (·.name)).getD ""))
    !info.source.slots.isEmpty || !info.source.copies.isEmpty || referencedOwners.contains fn.name ||
      privateStoreBarrier fns fn.body || privateStoreBarrier fns body ||
      protocolName fn.name || MetadataPlan.isEventSignal fns i || info.borrowTasks || !info.source.forwarded.isEmpty ||
      info.source.slots.any (fun (_, origin) => origin.frame != fn.name) ||
      unsafeBody fn.body || unsafeBody body
  let mut callers := Array.replicate fns.size ([] : List Nat)
  for i in [:fns.size] do
    for g in MetadataPlan.calls fns[i]!.body ++ MetadataPlan.calls ((infos[i]?.getD {}).body.getD fns[i]!.body) do
      if g < fns.size then callers := callers.modify g (i :: ·)
  let mut queue := (List.range fns.size).filter (fun i => excluded[i]!) |>.toArray
  let mut cursor := 0
  while cursor < queue.size do
    let callee := queue[cursor]!
    cursor := cursor + 1
    for caller in callers[callee]! do
      if !excluded[caller]! then
        excluded := excluded.set! caller true
        queue := queue.push caller
  return excluded.map (! ·)

/-- Conservative metadata origins reachable through either analysis or physical calls. -/
private def metadataOriginFlags (fns : Array Fn) (infos : Array Info)
    (cleanPrototypes : Array Bool) : Array Bool := Id.run do
  let mut origins := fns.mapIdx fun i fn =>
    let info := infos[i]?.getD {}
    !info.inputs.isEmpty || !info.seeds.isEmpty || info.metadataResult ||
      !info.metadataWrites.isEmpty || info.borrowTasks || !info.source.forwarded.isEmpty ||
      info.source.slots.any (fun (_, origin) => origin.frame != fn.name) ||
      cellReferenceLiteral cleanPrototypes fn.body || cellReferenceLiteral cleanPrototypes (info.body.getD fn.body) ||
      (MetadataPlan.calls fn.body ++ MetadataPlan.calls (info.body.getD fn.body)).any (· ≥ fns.size)
  let mut callers := Array.replicate fns.size ([] : List Nat)
  for index in [:fns.size] do
    for callee in MetadataPlan.calls fns[index]!.body ++
        MetadataPlan.calls ((infos[index]?.getD {}).body.getD fns[index]!.body) do
      if callee < fns.size then callers := callers.modify callee (index :: ·)
  let mut queue := (List.range fns.size).filter (fun i => origins[i]!) |>.toArray
  let mut cursor := 0
  while cursor < queue.size do
    let callee := queue[cursor]!
    cursor := cursor + 1
    for caller in callers[callee]! do
      if !origins[caller]! then
        origins := origins.set! caller true
        queue := queue.push caller
  return origins

/-- Solve recursive call contexts and loop back edges to a fixed point.
    Hidden witnesses do not taint an unrelated result: return roles come
    from the body, rather than the union of physical call arguments. -/
def check (fns : Array Fn) (infos : Array Info) (fields : Array (List Nat))
    (debug : Bool := false) (scalarReturns : Array Bool := #[])
    (dataReturns : Array Bool := #[]) (cleanPrototypes : Array Bool := #[]) : Except String Unit := do
  let privateBarriers := privateStoreBarriers fns infos
  let referencedOwners := referencedPrivateOwners fns infos
  let infos := infos.mapIdx fun index info =>
    let dead := privateWriteOnlySlots fns infos privateBarriers referencedOwners index
    { info with body := info.body.map fun body =>
        let body := withoutRolledBackCopies body
        if dead.isEmpty then body else withoutPrivateDeadStores dead body }
  -- Virtual receiver locals belong exclusively to this analysis view.
  -- Keep the original physical frame for the ownership/dead-store proof above.
  let fns := fns.mapIdx fun i fn => { fn with nslots := fn.nslots + (infos[i]?.getD {}).extraSlots }
  let infos := infos.map fun info => { info with
    nonCellMask := info.nonCellSlots.foldl (fun mask slot => mask ||| (1 <<< slot)) 0
    objectFreeMask := info.objectFreeSlots.foldl (fun mask slot => mask ||| (1 <<< slot)) 0
    dataOnlyMask := info.dataOnlySlots.foldl (fun mask slot => mask ||| (1 <<< slot)) 0 }
  let cellTag := infos.findSome? (·.cellTag)
  -- Use exactly the same independent entries for the closed-program proof
  -- and ordinary validation. Compiler-owned bridges are reached by calls.
  let roots := (List.range fns.size).filter fun i =>
    let info := infos[i]?.getD {}
    !(info.borrowTasks || info.cellHelper ||
      info.source.slots.any (fun (_, origin) => origin.frame != fns[i]!.name) ||
      info.source.forwarded.any (fun origin => origin.frame != fns[i]!.name))
  let originFlags := if cellTag.isSome || debug then metadataOriginFlags fns infos cleanPrototypes else #[]
  -- Every independent entry starts with a fresh heap. Source-certified
  -- object-free parameters contain no object aliases. The separate strict
  -- data certificate permits ordinary object aliases whose entire typed graph
  -- excludes private cells and metadata-bearing fields. In either case the
  -- entry has no private input identity; absence of every reachable role
  -- origin then establishes that no metadata payload exists.
  -- Keep the ordinary role/admission checker, while avoiding an unnecessary
  -- private alias interpretation under this closed entry premise.
  let closedEntry (i : Nat) : Bool :=
    let info := infos[i]?.getD {}
    cellTag.isSome && !(originFlags[i]?.getD true) &&
      (List.range fns[i]!.arity).all (fun slot =>
        info.objectFreeMask.testBit slot || info.dataOnlyMask.testBit slot)
  let closedRoots := roots.filter closedEntry
  let openRoots := roots.filter (fun i => !closedEntry i)
  let capable := cellCapabilities fns infos cellTag
  let transportTag := infos.findSome? (·.cellTransportTag)
  let borrowed := MetadataPlan.borrows fns (infos.map (·.source))
  let bodies := fns.mapIdx fun i f => { f with body := (infos[i]?.getD {}).body.getD f.body }
  let borrowedWork := MetadataPlan.borrowedWork bodies (infos.map (·.source)) (infos.map (·.borrowTasks))
  let borrowedTasks := MetadataPlan.borrowedTasks bodies (infos.map (·.borrowTasks))
  let sites := fns.mapIdx fun i fn =>
    let (background, cleanups) := MetadataPlan.sites fns ((infos[i]?.getD {}).body.getD fn.body)
    (background || borrowedWork[i]!, cleanups)
  -- Tracking a body's own pending frames is a sequential interpretation of
  -- its heap. A body that starts concurrent work, or that runs as a
  -- background task, keeps the conservative summary: enabling cells there
  -- would demand a schedule replay that immutable frames do not need.
  let localTransport := fns.mapIdx fun i fn =>
    let body := (infos[i]?.getD {}).body.getD fn.body
    !(sites[i]?.getD (false, [])).1 && !cellConcurrentBody fns body &&
      transportTag.any fun tag => cellConstructor tag body
  let transferSafe := if cellTag.isSome then closedTransferSafety fns infos referencedOwners else #[]
  -- The static path proves private-irrelevant formal inputs. Other functions may
  -- use the same all-real transfer only in a caller context whose complete
  -- alias state proves that no private input identity is reachable.
  let freshFunctions := (List.range fns.size).filter fun i =>
    cellTag.isSome && !(originFlags[i]?.getD true) &&
      ((scalarReturns[i]?.getD false) || (dataReturns[i]?.getD false)) &&
      (transferSafe[i]?.getD false)
  let closedRootSet := closedRoots.foldl (fun set i => set.insert i ()) ({} : Std.HashMap Nat Unit)
  let closedSeeds := closedRoots ++ freshFunctions.filter (fun i => !closedRootSet.contains i)
  if debug then
    dbg_trace s!"metadata closed-real entries={closedRoots.length} open={openRoots.length}"
  let action (roots : List Nat) (trackTransports : Bool) : M Unit := do
    let runContext (key : Key) : M Flow := do
      let (i, args) := key
      let some fn := fns[i]? | throw "internal: metadata call has no body"
      let info := infos[i]?.getD {}
      modify fun st => { st with
        active := some key, captureMismatch := false, contextDeferred := false, cellPath := [0]
        cellEnabled := (st.cellCapable[i]?.getD false) ||
          (trackTransports && (localTransport[i]?.getD false)), cellRefBase := 0,
        cellScope := i, cellGraphOwner := none }
      let values := (List.range fn.nslots).map (fun i =>
        info.inputs.contains i || (args[i]?.getD default).role) |>.toArray |> Bits.ofArray
      let initialized := (List.range fn.nslots).map (fun i => i < fn.arity : Nat → Bool) |>.toArray |> Bits.ofArray
      let enabled := (← get).cellEnabled
      let mut heap := if enabled then MetadataCells.initialRefs fn.nslots (fun _ => []) else {}
      let privateFormals := info.cellParams.filter (· < fn.arity)
      if enabled then
        for slot in [:fn.arity] do
          if !info.objectFreeMask.testBit slot && !info.dataOnlyMask.testBit slot &&
              !privateFormals.contains slot then
            let site ← cellInputSite i slot
            let (refs, registered) := MetadataCells.registerExternal heap site
            heap := MetadataCells.setLocal registered slot refs
      if enabled && !privateFormals.isEmpty then
        let site ← cellExternalSite i
        let (refs, allocated) := MetadataCells.allocate heap site true [{ role := true, refs := [0] }]
        heap := MetadataCells.markEscaped allocated refs
        heap := { heap with nodes := refs.foldl (fun nodes object =>
          nodes.modify object (fun node => { node with unique := false, external := true })) heap.nodes }
        for slot in privateFormals do heap := MetadataCells.setLocal heap slot refs
      let slots : Slots := {
        heap
        values, initialized, sharedMetadata := values
        tuples := args.zipIdx.foldl (fun tuples (arg, j) =>
          putParts tuples j (if info.inputs.contains j then none else arg.parts)) {}
        written := Bits.replicate fn.nslots false }
      let body := info.body.getD fn.body
      modify fun st => { st with seen := values }
      let (background, cleanups) := (← get).sites[i]?.getD (false, [])
      let privateConcurrent := (← get).cellEnabled && cellConcurrentBody fns body
      if !background && cleanups.isEmpty && !privateConcurrent && !((← get).borrowers[i]?.getD false) then
        return ← expr fns infos fields fn info slots body
      let saved ← get
      -- Discover potential metadata without validating provisional or
      -- unreachable call contexts. Only the actual replay queues live calls.
      modify fun st => { st with
        seen := values, discovery := true
        validateUses := false, validateShared := false }
      let out ← expr fns infos fields fn info slots body
      let seen := (← get).seen
      let captureMismatch := (← get).captureMismatch
      modify fun st => { st with
        discovery := saved.discovery
        validateUses := saved.validateUses, validateShared := saved.validateShared }
      -- Opaque witness forwarding in cleanup needs no schedule exploration.
      -- Probe every potentially observed role against executable boundaries;
      -- shared writes also matter because another continuation can read them.
      let cleanupSlots := { slots with
        values := seen
        tuples := {}
        initialized := Bits.replicate fn.nslots true
        sharedMetadata := Bits.replicate fn.nslots false }
      let mut metadataCleanup := false
      for d in cleanups do
        match probeCleanup fns infos fields fn info cleanupSlots d (← get) with
        | .error _ => metadataCleanup := true
        | .ok discovered =>
          modify fun st => { st with
            summaries := discovered.summaries
            indices := discovered.indices, changed := discovered.changed
            dependencies := discovered.dependencies }
        if (MetadataPlan.assigns d).any (fun i =>
            info.shared.contains i && seen.get i) then
          metadataCleanup := true
      -- A lifted task needs the caller's schedule only when it can observe
      -- metadata at an executable boundary. Hidden type witnesses alone do
      -- not make an ordinary default argument relevant to this analysis.
      let mut metadataTask := false
      if (← get).borrowedTasks[i]?.getD false then
        match probeCleanup fns infos fields fn info cleanupSlots body (← get) with
        | .error _ => metadataTask := true
        | .ok discovered =>
          modify fun st => { st with
            summaries := discovered.summaries
            indices := discovered.indices, changed := discovered.changed
            dependencies := discovered.dependencies }
      -- A background actor can introduce metadata directly into a private
      -- payload and then never return. Completed scalar/heap outputs do not
      -- witness that write, so all private-cell concurrency needs replay.
      let cellSensitive := (← get).cellEnabled &&
        (background || privateConcurrent || (!cleanups.isEmpty &&
          (slots.values.bits != 0 || (← get).seen.bits != 0 ||
            out.slots.heap.cells.any (fun _ payload => payload.role) ||
            out.returnedHeap.any (fun heap => heap.cells.any (fun _ payload => payload.role)))))
      let needsSchedule := cellSensitive || captureMismatch || metadataCleanup || metadataTask || (background &&
        (info.shared.any (fun i => seen.get i) ||
          out.value.getD false || out.returned.getD false))
      if needsSchedule then
        let st ← get
        -- First settle ordinary transfers. Expensive schedule transfers run
        -- in a forced pass once those summaries stop changing.
        if st.deferSchedules then
          modify fun st => { st with contextDeferred := true }
          return { slots, value := none }
        let cached := (← get).plans[i]?.getD none
        let plan ← match cached with
          | some plan => pure plan
          | none => do
            let bodies := fns.mapIdx fun j f => { f with body := (infos[j]?.getD {}).body.getD f.body }
            let plan := MetadataPlan.build bodies info.metadataWrites fn.nslots body (some i)
              (infos.map (·.metadataWrites)) (infos.map (·.source))
              (infos.map (·.borrowTasks))
            modify fun st => { st with plans := st.plans.set! i (some plan) }
            pure plan
        if debug then dbg_trace s!"metadata selected {fn.name}: slots={plan.slots}, actors={plan.actors}"
        let referenceLive ← match (← get).referenceLives[i]?.getD none with
          | some live => pure live
          | none => do
            let live := MetadataLiveness.build fns plan
            modify fun st => { st with referenceLives := st.referenceLives.set! i (some live) }
            pure live
        -- Atomic expression fallbacks can run their own ordinary concurrent
        -- fixed point. Keep the original replay for those conservative cases.
        let cacheable := !(plan.nodes.any fun
          | .atom e .. | .test e .. => !(MetadataPlan.calls e).isEmpty
          | _ => false)
        let st ← get
        if cacheable && st.validateUses && st.validateShared then
          if let some proof := st.scheduleProofs[key]? then
            if proof.calls.all (fun (callee, result, parts, yielded) =>
                match st.indices[callee]? with
                | some j => let summary := st.summaries[j]!
                            summary.result == result && summary.parts == parts && summary.yielded == yielded
                | none => false) then
              -- Publish only calls actually observed by this graph, never
              -- provisional calls from its relevance/cleanup discovery.
              for (callee, _, _, _) in proof.calls do discard <| request callee
              modify fun st => { st with
                seen := (st.seen.appendZeros (proof.seen.size - st.seen.size)).union
                  (proof.seen.appendZeros (st.seen.size - proof.seen.size))
                captureMismatch := st.captureMismatch || proof.captureMismatch
                signalArguments := st.signalArguments.or proof.signalArguments }
              if debug then dbg_trace s!"metadata scheduled proof reused {fn.name}"
              return proof.flow
        let savedCalls := st.scheduledCalls
        let savedCallOrder := st.scheduledCallOrder
        let savedSuppressed := st.suppressedSharedWrite
        modify fun st => { st with scheduledCalls := some {}, scheduledCallOrder := #[], suppressedSharedWrite := false }
        let out ← schedule { fns, infos, fields, fn, info, plan, referenceLive } slots
        let checked ← get
        let calls := checked.scheduledCallOrder.map fun key =>
          let (result, parts, yielded) := (checked.scheduledCalls.getD {})[key]!
          (key, result, parts, yielded)
        modify fun st => { st with
          scheduledCalls := savedCalls, scheduledCallOrder := savedCallOrder
          suppressedSharedWrite := savedSuppressed || checked.suppressedSharedWrite
          scheduleProofs := if cacheable && checked.validateUses && !checked.suppressedSharedWrite then
            st.scheduleProofs.insert key {
              flow := out, calls, seen := checked.seen
              captureMismatch := checked.captureMismatch, signalArguments := checked.signalArguments }
            else st.scheduleProofs.erase key }
        return out
      if saved.validateUses then
        return ← expr fns infos fields fn info slots body
      return out
    let seedRoots : M Unit := do
      for i in roots do
        let info := infos[i]?.getD {}
        discard <| request (i, (List.range fns[i]!.arity).map (fun j => ({ role := info.inputs.contains j } : Argument)))
    seedRoots
    let mut growing := true
    let mut forceSchedules := false
    while growing do
      modify fun st => { st with changed := false, deferSchedules := !forceSchedules }
      let mut deferred := false
      let summaries := (← get).summaries
      for (summary, index) in summaries.zipIdx do
        let i := summary.key.1
        let info := infos[i]?.getD {}
        -- Summary solving caches stable dependencies. Final validation
        -- checks every live context, reusing only checked schedule proofs.
        -- Cleanup
        -- relevance probes have private call queues, so keep those frames
        -- out of this dependency cache.
        let cacheable := ((← get).sites[i]?.getD (false, [])).2.isEmpty
        let current := (← get).summaries
        if cacheable && summary.cached && summary.dependencies.all (fun (j, result, parts, yielded) =>
            let s := current[j]!
            s.result == result && s.parts == parts && s.yielded == yielded) then continue
        modify fun st => { st with dependencies := if cacheable then some {} else none }
        let validate := (← get).validateUses
        -- Borrowed locals are validated against their actual owner by the
        -- inlined graph. Discovery can also request a provisional summary
        -- using old capture arguments; that summary is not a live frame.
        if info.borrowTasks || info.source.slots.any (fun (_, s) => s.frame != fns[i]!.name) then
          modify fun st => { st with validateUses := false }
        let out ← runContext summary.key
        let contextDeferred := (← get).contextDeferred
        deferred := deferred || contextDeferred
        modify fun st => { st with validateUses := validate }
        let dependencies := ((← get).dependencies.getD {}).toList.toArray.map fun (j, result, parts, yielded) =>
          (j, result, parts, yielded)
        modify fun st => { st with
          dependencies := none
          summaries := st.summaries.modify index fun s => { s with dependencies, cached := cacheable && !contextDeferred } }
        let returned := (joinRole out.value out.returned).map (· || info.metadataResult)
        let returnedParts := if info.metadataResult then none else
          joinParts out.value out.valueParts out.returned out.returnedParts
        let parts := joinParts summary.result summary.parts returned returnedParts
        let result := joinRole summary.result returned
        let yielded := summary.yielded || out.yielded
        if result != summary.result || parts != summary.parts || yielded != summary.yielded then
          modify fun st => { st with summaries := st.summaries.modify index (fun s => { s with result, parts, yielded }), changed := true }
      let changed := (← get).changed
      growing := changed || deferred
      -- If a recursive dependency component cannot progress without a
      -- schedule, run the deferred transfers in the next pass.
      forceSchedules := !changed && deferred
    -- A summary may grow from a real return to a metadata return. Follow
    -- calls again from the roots using the stable summaries: provisional
    -- argument contexts can disappear and must not be validated as live.
    modify fun st => { st with validateShared := true, validateUses := true, deferSchedules := false }
    seedRoots
    let mut index := 0
    while index < (← get).live.size do
      let key := (← get).live[index]!
      index := index + 1
      discard <| runContext key
  -- Each premise owns fresh queues, summaries, proofs, aliases and graph
  -- state. A callable root with open arguments is still checked independently
  -- even when it is also reached from a certified closed entry.
  let run (entries : List Nat) (tag : Option Nat) (capabilities : Array Bool)
      (closed : Std.HashMap Nat (Bool × Option Bool × TupleParts × Bool)) (trackTransports : Bool) :
      Except String State := do
    let (_, final) ← (action entries trackTransports).run {
      debug := debug, scalarReturns
      cellTag := tag, cellCapable := capabilities, closedTransfers := closed
      cellTransportTag := transportTag
      plans := Array.replicate fns.size none
      referenceLives := Array.replicate fns.size none
      sites := sites
      borrowers := borrowed
      borrowedWork := borrowedWork
      borrowedTasks := borrowedTasks }
    return final
  let closedState ← if closedSeeds.isEmpty then pure ({} : State)
    else run closedSeeds none (Array.replicate fns.size false) {} false
  let closedResults := freshFunctions.foldl (fun out g =>
    let key := (g, List.replicate fns[g]!.arity ({} : Argument))
    match closedState.indices[key]? with
    | none => out
    | some index =>
      let summary := closedState.summaries[index]!
      out.insert g (!closedEntry g, summary.result, summary.parts, summary.yielded)) {}
  if !openRoots.isEmpty then
    -- The ordinary summary decides nearly every program. Interpreting the
    -- pending frames a body builds costs several times as much, so it runs
    -- only for a program the summary refuses. Either proof admits it; a
    -- program neither admits keeps the summary's diagnostic.
    match run openRoots cellTag capable closedResults false with
    | .ok _ => pure ()
    | .error refusal =>
      unless localTransport.any id do throw refusal
      match run openRoots cellTag capable closedResults true with
      | .ok _ => pure ()
      | .error _ => throw refusal

end OpenVerse.Front.MetadataFlow
