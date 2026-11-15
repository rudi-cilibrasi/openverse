/- Compiler-only provenance analysis. Metadata is not a Core runtime tag. -/
import OpenVerse.Front.Syntax
import OpenVerse.Core.Syntax
import OpenVerse.Front.MetadataPlan
import OpenVerse.Front.MetadataReferences
import Std.Data.HashMap

namespace OpenVerse.Front.MetadataFlow
open OpenVerse

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
  source : FrameRefs.Info := {}
  body : Option Expr := none
  deriving Inhabited

private structure Slots where
  values : Array Bool := #[]
  initialized : Array Bool := #[]
  sharedMetadata : Array Bool := #[]
  /-- Writes performed by this arm, excluding roles received from siblings. -/
  written : Array Bool := #[]
  deriving BEq, Inhabited

private def joinSlots (a b : Slots) : Slots := {
  values := a.values.zipWith (· || ·) b.values
  initialized := a.initialized.zipWith (· || ·) b.initialized
  written := a.written.zipWith (· || ·) b.written
  sharedMetadata := a.sharedMetadata.mapIdx fun i role =>
    if !(a.initialized[i]?.getD false) then b.sharedMetadata[i]?.getD false
    else if !(b.initialized[i]?.getD false) then role
    else role && b.sharedMetadata[i]?.getD false }

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
      ready && (entry.initialized[i]?.getD false || !shared.contains i)
    sharedMetadata := head.sharedMetadata.mapIdx fun i role =>
      if entry.initialized[i]?.getD false || !shared.contains i then role
      else entry.sharedMetadata[i]?.getD false }

private def joinRole (a b : Option Bool) : Option Bool :=
  match a, b with
  | some a, some b => some (a || b)
  | some a, none | none, some a => some a
  | none, none => none

private structure Flow where
  slots : Slots
  value : Option Bool := some false
  returned : Option Bool := none
  broken : Option Slots := none
  /-- May yield before normal completion or a nonreturning path. -/
  yielded : Bool := false

private def withExits (a b : Flow) : Flow := { b with
  returned := joinRole a.returned b.returned
  broken := joinOpt a.broken b.broken
  yielded := a.yielded || b.yielded }

private abbrev Key := Nat × List Bool

private structure Summary where
  key : Key
  result : Option Bool := none
  yielded : Bool := false
  dependencies : Array (Nat × Option Bool × Bool) := #[]
  cached : Bool := false
  deriving Inhabited

private inductive ActorStatus where
  | idle | running | ready | waiting (resumable : Bool) | joining (group : Nat) | done
  deriving BEq, Inhabited

private structure LoopEntry where
  id : Nat
  slots : Slots
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
  task : Option MetadataReferences.Refs := none
  taskWait : Bool := false
  waitDst : Option Nat := none
  signalReturns : List (Option Nat) := []
  canComplete : Bool := false
  canSignal : Bool := false
  deriving BEq, Inhabited

private structure GroupStatus where
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
  | result (role : Bool)
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

private def contextKey : Option (Nat × Nat) → List Nat
  | none => [0]
  | some (fn, offset) => [fn + 1, offset]

private def loopsKey (loops : List LoopEntry) : List Nat :=
  loops.length :: loops.flatMap (fun s => [s.id, s.cleanups.length] ++ s.cleanups)

private def actorsKey (actors : Array Actor) : List Nat :=
  actors.toList.flatMap fun a =>
    let (tag, data) := match a.status with
      | .idle => (0, 0) | .running => (1, 0) | .ready => (5, 0)
      | .waiting ready => (2, if ready then 1 else 0)
      | .joining g => (3, g) | .done => (4, 0)
    [a.pc, tag, data, if a.canceling then 1 else 0, if a.taskWait then 1 else 0, a.cleanups.length] ++ a.cleanups ++ [a.waitDst.map (· + 1) |>.getD 0,
      if a.canComplete then 1 else 0, if a.canSignal then 1 else 0, a.signalReturns.length] ++
      a.signalReturns.map (fun pc => pc.map (· + 1) |>.getD 0) ++
      loopsKey a.loops ++ contextKey a.context ++ [a.frames.length] ++
      a.frames.flatMap (fun f => contextKey f.context ++ [f.cleanups.length] ++
        f.cleanups ++ loopsKey f.loops)

private def groupsKey (groups : Array GroupStatus) : List Nat :=
  groups.toList.flatMap fun g =>
    [if g.active then 1 else 0, g.started, g.winner.map (· + 1) |>.getD 0]

private def pendingKey (pending : List Pending) : List Nat :=
  pending.length :: pending.flatMap fun
    | .cancel a => [0, a]
    | .cleanup a ctx pc => [1, a, pc] ++ contextKey ctx
    | .stop a => [2, a]
    | .resume a pc => [3, a, pc]
    | .returnCall a pc => [4, a, pc]
    | .returnScope a f o n pc => [7, a, f, o, n, pc]
    | .result role => [5, if role then 1 else 0]
    | .discard => [6]

private def configurationKey (c : Configuration) : List Nat :=
  [c.current.getD c.actors.size, c.startup.length] ++ c.startup ++
  [c.events.length] ++ c.events ++ actorsKey c.actors ++ groupsKey c.groups ++
  [c.signals.length] ++ c.signals ++ [c.launches.length] ++ c.launches ++ pendingKey c.pending ++ [c.tests.length] ++ c.tests.flatMap (fun t =>
    [t.owner, t.no, t.startup.length] ++ t.startup ++ [t.events.length] ++ t.events ++
    actorsKey t.actors ++ groupsKey t.groups ++ [t.signals.length] ++ t.signals ++ [t.launches.length] ++ t.launches ++ pendingKey t.pending)

private def joinLoops (a b : List LoopEntry) : List LoopEntry :=
  a.zipWith (fun s t => { t with slots := joinSlots s.slots t.slots }) b

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

private def putRole (s : Slots) (i : Nat) (role : Bool) : Slots := { s with
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
    if a.canceling || a.status != .waiting true || a.taskWait != task then continue
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

private structure State where
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
  seen : Array Bool := #[]
  plans : Array (Option MetadataPlan.Plan) := #[]
  sites : Array (Bool × List Expr) := #[]
  live : Array Key := #[]
  liveSeen : Std.HashMap Key Unit := {}
  debug : Bool := false
  active : Option Key := none
  signalArguments : Option (Array (List Nat)) := none
  dependencies : Option (Std.HashMap Nat (Option Bool × Bool)) := none

private abbrev M := StateT State (Except String)

private def refuse (fn : Fn) (info : Info) (what : String) (details : String := "") : M α := do
  let st ← get
  let context := if st.debug then
    s!"\nmetadata context: {reprStr st.active}\ninputs: {info.inputs}; seeds: {info.seeds}\n{details}\n{reprStr (info.body.getD fn.body)}" else ""
  throw s!"{info.pos.show}: dummy type value cannot {what} (in {fn.name}){context}"

private def request (key : Key) : M (Option Bool × Bool) := do
  let st ← get
  if st.validateUses && st.validateShared && !st.discovery && !st.liveSeen.contains key then
    set { st with live := st.live.push key, liveSeen := st.liveSeen.insert key () }
  let st ← get
  if let some i := st.indices[key]? then
    let value := (st.summaries[i]!.result, st.summaries[i]!.yielded)
    if let some dependencies := st.dependencies then
      if !dependencies.contains i then
        modify fun st => { st with dependencies := some (dependencies.insert i value) }
    return value
  let i := st.summaries.size
  let dependencies := st.dependencies.map (·.insert i (none, false))
  set { st with
    indices := st.indices.insert key i
    summaries := st.summaries.push { key }, changed := true, dependencies }
  return (none, false)

mutual
private partial def expr (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots) : Expr → M Flow
  | .lit _ => pure { slots }
  | .local i => pure { slots, value := some (slots.values[i]?.getD false) }
  | .assign i e => do
    let out ← expr fns infos fields fn info slots e
    let some role := out.value | return out
    let role := role || info.seeds.contains i
    if role then modify fun st => { st with seen := st.seen.set! i true }
    if (← get).validateUses && role && info.uses.contains i then
      refuse fn info "be an executable function or method receiver" s!"receiver slot {i}, value {reprStr e}"
    if info.shared.contains i && out.slots.initialized[i]?.getD false && role &&
        !(out.slots.sharedMetadata[i]?.getD false) then
      if (← get).validateShared then
        refuse fn info "enter a shared local containing executable data" s!"shared slot {i}, value {reprStr e}"
    let first := !(out.slots.initialized[i]?.getD false)
    return { out with
      value := some role
      slots := {
        values := out.slots.values.set! i role
        initialized := out.slots.initialized.set! i true
        written := if info.shared.contains i then out.slots.written.set! i true else out.slots.written
        -- Once real data enters a shared cell, waiting aliases can execute it.
        -- A later metadata write must not reuse its original metadata mode.
        sharedMetadata := out.slots.sharedMetadata.set! i
          (role && (first || out.slots.sharedMetadata[i]?.getD false)) } }
  | .seq a b => do
    let a ← expr fns infos fields fn info slots a
    if a.value.isNone then return a
    return withExits a (← expr fns infos fields fn info a.slots b)
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
    let (out, result, yielded) ← invoke fns infos fields fn info slots g es
    return { out with
      value := if name == "$branchMark" then
          -- The child releases its owner when it completes or first waits.
          if out.value.isSome || out.yielded then some false else none
        else if out.value.isSome then result else none
      -- A branch starts its body to its first wait without yielding its owner.
      yielded := if name == "$branchMark" then false else out.yielded || yielded }
  | .prim op es => do
    let (args, out) ← arguments fns infos fields fn info slots es
    if out.value.isNone then return out
    let value := match op, es with
      | .fail, _ | .userErr, _ | .query, [.lit (.logic false)] | .query, [.lit .none] => none
      | .query, _ | .mkArr, _ | .mkTup, _ | .mkSome, _ | .concat, _ | .index, _ |
          .arrSet, _ | .flatten, _ | .tupGet _, _ |
          .lt, _ | .le, _ | .gt, _ | .ge, _ | .eq, _ | .ne, _ |
          .flt, _ | .fle, _ | .fgt, _ | .fge, _ => some (args.any id)
      -- Length, formatting and arithmetic construct fresh scalar data;
      -- they cannot preserve a dictionary, function or opaque payload.
      | _, _ => some false
    return { out with value }
  | .heap op es => do
    let (args, out) ← arguments fns infos fields fn info slots es
    if out.value.isNone then return out
    let role ← match op with
      | .new tag => pure (args.zipIdx.any fun (role, i) => role && !(fields[tag]?.getD []).contains i)
      | .set k => do
        let metadataField := match es.head? with
          | some (.local obj) => info.metadataWrites.contains (obj, k)
          | _ => false
        if (← get).validateUses && args[1]?.getD false && !metadataField then
          refuse fn info "enter a shared object field containing executable data"
        pure (args[1]?.getD false)
      | .get _ | .isTag _ => pure (args.headD false)
      | .tag => pure false
    return { out with value := some role }
  | .ite c t e => do
    let c ← expr fns infos fields fn info slots c
    let t ← if c.value.isSome then expr fns infos fields fn info c.slots t
      else pure { slots := c.slots, value := none }
    -- The failure arm starts before c, including its mutable-local roles.
    let e ← expr fns infos fields fn info slots e
    let merged := match t.value, e.value with
      | some _, some _ => joinSlots t.slots e.slots
      | some _, none => t.slots
      | _, _ => e.slots
    return withExits c {
      slots := merged, value := joinRole t.value e.value
      returned := joinRole t.returned e.returned, broken := joinOpt t.broken e.broken
      yielded := t.yielded || e.yielded }
  | .forE i source filt body => do
    let source ← expr fns infos fields fn info slots source
    let some item := source.value | return source
    if item then modify fun st => { st with seen := st.seen.set! i true }
    let mut head := source.slots
    let mut result := false
    let mut exits := source
    let mut growing := true
    while growing do
      let entry := { head with values := head.values.set! i item }
      let filt ← expr fns infos fields fn info entry filt
      let body ← if filt.value.isSome then expr fns infos fields fn info filt.slots body
        else pure { slots := entry, value := none }
      exits := withExits filt (withExits body exits)
      result := result || body.value.getD false
      let next := if body.value.isSome then freshLocals info.shared source.slots (joinSlots head body.slots) else head
      growing := next != head
      head := next
    return { exits with slots := head, value := some result }
  | .loop body => do
    let mut head := slots
    let mut returned := none
    let mut broken := none
    let mut yielded := false
    let mut growing := true
    while growing do
      let out ← expr fns infos fields fn info head body
      returned := joinRole returned out.returned
      broken := joinOpt broken out.broken
      yielded := yielded || out.yielded
      let next := if out.value.isSome then freshLocals info.shared slots (joinSlots head out.slots) else head
      growing := next != head
      head := next
    return { slots := broken.getD head, value := broken.map (fun _ => false), returned, yielded }
  | .brk => pure { slots, value := none, broken := some slots }
  | .ret e => do
    let out ← expr fns infos fields fn info slots e
    return { out with value := none, returned := joinRole out.returned out.value }
  | .print e => do
    let out ← expr fns infos fields fn info slots e
    return { out with value := out.value.map (fun _ => false) }

/-- A spawn evaluates the selected call's arguments now. Its result belongs
    to the task; returning or yielding lets its caller continue. A task that
    does neither holds the caller. Dispatch and argument exits run normally. -/
private partial def spawned (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots) :
    Expr → M (Option Bool × Flow)
  | .call g es => do
    let (out, result, yielded) ← invoke fns infos fields fn info slots g es
    return (result, { out with value :=
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
      returned := joinRole t.returned e.returned, broken := joinOpt t.broken e.broken
      yielded := t.yielded || e.yielded })
  | .assign i e => do
    let (result, out) ← spawned fns infos fields fn info slots e
    return (result.map (· || info.seeds.contains i), out)
  | e => do
    let out ← expr fns infos fields fn info slots e
    return (out.value, { out with value := out.value.map (fun _ => false) })

private partial def invoke (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots)
    (g : Nat) (es : List Expr) (summarize : Bool := true) : M (Flow × Option Bool × Bool) := do
  let (args, out) ← arguments fns infos fields fn info slots es
  if out.value.isNone then return (out, none, false)
  let gi := infos[g]?.getD {}
  let roles := args.zipIdx.map fun (role, i) => role || gi.inputs.contains i
  if (← get).validateUses && gi.required.any (fun i => roles[i]?.getD false) then
    refuse fn info s!"provide executable evidence or a receiver to {(fns[g]?.map (·.name)).getD "a call"}"
  if !summarize then return (out, none, false)
  let (result, yielded) ← request (g, roles)
  let name := (fns[g]?.map (·.name)).getD ""
  let yielded : Bool := if name == "$Sleep" then
    match es with
    | [.lit (.float bits)] => decide (VFloat.ofBits bits > 0.0)
    | [.prim .fneg [.lit (.float bits)]] => decide (-(VFloat.ofBits bits) > 0.0)
    | _ => true
    else name == "$WaitDone" || yielded
  return (out, result, yielded)

private partial def concurrent (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots)
    (sync : Bool) (arms : List Expr) : M Flow := do
  -- Only cells already in scope can be shared by sibling arms. A local
  -- declared inside an arm starts fresh on each analysis of that arm.
  let shared := info.shared.filter fun i => slots.initialized[i]?.getD false
  let entry (outs : Array Flow) (own : Nat) : Slots := Id.run do
    let mut joined := slots
    for (out, i) in outs.zipIdx do
      if i != own then
        let incoming := { out.slots with
          values := out.slots.values.mapIdx fun k role =>
            if out.slots.written[k]?.getD false then role else slots.values[k]?.getD false
          sharedMetadata := out.slots.sharedMetadata.mapIdx fun k role =>
            if out.slots.written[k]?.getD false then role else slots.sharedMetadata[k]?.getD false }
        joined := joinSlots joined incoming
    return {
      values := slots.values.mapIdx fun i role =>
        if shared.contains i then joined.values[i]?.getD false else role
      initialized := slots.initialized
      written := Array.replicate slots.values.size false
      sharedMetadata := slots.sharedMetadata.mapIdx fun i role =>
        if shared.contains i then joined.sharedMetadata[i]?.getD false else role }
  let runArms (outs : Array Flow) : M (Array Flow) := do
    let mut next := #[]
    for (arm, i) in arms.toArray.zipIdx do
      let out ← expr fns infos fields fn info (entry outs i) arm
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
        returned := joinRole old.returned out.returned
        broken := joinOpt old.broken out.broken
        yielded := old.yielded || out.yielded }
    growing := next.map (·.slots) != outs.map (·.slots)
    outs := next
  modify fun st => { st with validateShared := validate }
  if validate then outs ← runArms outs
  let mut joined : Option Slots := none
  let mut returned := none
  let mut broken := none
  for out in outs do
    joined := joinOpt joined (some out.slots)
    returned := joinRole returned out.returned
    broken := joinOpt broken out.broken
  let merged := joined.getD slots
  let merged := { merged with written := slots.written.zipWith (· || ·) merged.written }
  -- A successful sync completes every arm. With metadata reentry barred,
  -- any arm that definitely leaves real data makes that shared cell real.
  -- Race/rush can finish with another arm still pending, so retain may roles.
  let finalSlots := if sync then { merged with
    values := merged.values.mapIdx fun i role =>
      if shared.contains i then outs.all (fun out => out.slots.values[i]?.getD false) else role }
    else merged
  let normal := if sync then outs.all (·.value.isSome) else outs.any (·.value.isSome)
  let yielded := if sync then
      outs.all (fun out => out.value.isSome || out.yielded) && outs.any (·.yielded)
    else outs.all (·.yielded)
  return { slots := finalSlots, value := if normal then some false else none, returned, broken, yielded }

private partial def arguments (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots)
    (es : List Expr) : M (List Bool × Flow) := do
  let mut out : Flow := { slots }
  let mut roles := []
  for e in es do
    if out.value.isSome then
      out := withExits out (← expr fns infos fields fn info out.slots e)
      roles := roles ++ [out.value.getD false]
  return (roles, out)

private partial def actorEnvironment (env : ScheduleEnv) (a : Actor) : Fn × Info :=
  match a.context with
  | none => (env.fn, env.info)
  | some (g, offset) =>
    let info := env.infos[g]?.getD {}
    let alias (i : Nat) := (env.plan.aliases.lookup (i + offset)).getD (i + offset)
    (env.fns[g]!, { info with
      inputs := info.inputs.filterMap fun i => if (env.plan.aliases.lookup (i + offset)).isSome then none else some (i + offset)
      seeds := info.seeds.filterMap fun i => if (env.plan.aliases.lookup (i + offset)).isSome then none else some (i + offset)
      uses := info.uses.map (· + offset)
      shared := info.shared.map alias
      metadataWrites := info.metadataWrites.map fun (i, k) => (i + offset, k) })

private partial def cancelChildren (env : ScheduleEnv) (c : Configuration) (actor : Nat) (branch : Bool)
    (context : Option (Option (Nat × Nat)) := none) : List Pending :=
  c.launches.reverse.flatMap fun i =>
    let g := env.plan.groups[i]!
    if g.owner == actor && g.kind != .spawn && (g.kind == .branch) == branch &&
        (context.isNone || context == some g.context) then
      g.children.toList.reverse.map (fun (child, _) => .cancel child)
    else []

private partial def queue (c : Configuration) (steps : List Pending) : Configuration :=
  { c with current := none, pending := steps ++ c.pending }

private partial def cancelSteps (env : ScheduleEnv) (c : Configuration) (actor : Nat) : Configuration :=
  let a := c.actors[actor]!
  if a.canceling then c else
    let cleanups := if a.status == .done || a.status == .idle then [] else
      (a.cleanups.head?.toList.map fun d =>
        Pending.cleanup actor a.context env.plan.cleanupEntries[d]!) ++
      a.frames.flatMap (fun f => f.cleanups.head?.toList.map fun d =>
        Pending.cleanup actor f.context env.plan.cleanupEntries[d]!)
    let c := { c with
      events := c.events.filter (· != actor)
      actors := c.actors.modify actor fun a => { a with canceling := true, event := none } }
    queue c (cancelChildren env c actor false ++ cleanups ++ [.stop actor] ++
      cancelChildren env c actor true)

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

private partial def schedule (env : ScheduleEnv) (entry : Slots) : M Flow := do
  let extra := env.plan.slots - entry.values.size
  let pad (a : Array Bool) := a ++ Array.replicate extra false
  let slots : Slots := {
    values := pad entry.values, initialized := pad entry.initialized
    sharedMetadata := pad entry.sharedMetadata, written := pad entry.written }
  let initial : Configuration := {
    slots
    refs := { slots := Array.ofFn (n := env.plan.slots) fun i =>
      if i.val < env.fn.arity then [i.val + 2] else [] }
    actors := (Array.replicate env.plan.actors {}).set! 0 {
      pc := env.plan.entry, status := .running }
    groups := Array.replicate env.plan.groups.size {} }
  modify fun st => { st with seen := st.seen ++ Array.replicate extra false }
  let mut work := #[initial]
  let mut cursor := 0
  let mut known : Std.HashMap (List Nat) Configuration := {}
  let mut result : Option Bool := none
  let mut finalSlots : Option Slots := none
  let mut yielded := false
  while cursor < work.size do
    if (← get).debug && cursor % 10000 == 0 then
      dbg_trace s!"metadata schedule {env.fn.name}: visited={cursor}, queued={work.size}, states={known.size}"
    let incoming := work[cursor]!
    -- Processed configurations remain in `known`; release their queued
    -- copies while exploring long lifted consumers.
    work := work.set! cursor default
    cursor := cursor + 1
    let key := configurationKey incoming
    let c := match known[key]? with
      | none => incoming
      | some old => joinConfiguration old incoming
    if (known[key]?).any (· == c) then continue
    known := known.insert key c
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
        | .result role =>
          result := joinRole result (some role)
          finalSlots := joinOpt finalSlots (some c.slots)
        | .discard => pure ()
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
        for i in [:c.actors.size] do
          let a := c.actors[i]!
          let resumableTask := !a.taskWait || a.event.any (fun task =>
            (taskOptions c task).any (fun state => state == 1 || state == 2))
          if a.status == .waiting true && !a.canceling && resumableTask then
            work := work.push (advanceActor c i c.actors[i]!.pc)
      continue
    let a := c.actors[actor]!
    let lexical := env.plan.contexts[a.pc]?.getD a.context
    let (fn, info) := actorEnvironment env { a with context := lexical }
    let node := env.plan.nodes[a.pc]!
    let boundary := match node with
      | .call g args _ _ _ =>
        let name := env.fns[g]!.name
        let receiver := objectRefs (args.head?.map (fun i => c.refs.slots[i]!) |>.getD [0])
        if name == "$signalAll" || MetadataPlan.isEventSignal env.fns g then
          some (PoolCause.event receiver)
        else if name == "$cancelMark" then some (.cancel receiver)
        else if !c.signals.isEmpty then some .inside else none
      | .finishTask _ => some (.task (a.task.getD [0]))
      | .drained => none
      | _ => if !c.signals.isEmpty then some .inside else none
    if let some cause := boundary then
      for transition in poolTransitions env.plan c cause do work := work.push transition
    match node with
    | .jump pc => work := work.push (advanceActor c actor pc)
    | .atom e dst next permission =>
      let info := match permission with
        | none => info
        | some p => { info with metadataWrites := p :: info.metadataWrites }
      let out ← expr env.fns env.infos env.fields fn info c.slots e
      if let some role := out.value then
        let (refs, memory) := MetadataReferences.eval env.fns a.pc c.refs e
        let changed := { c with
          slots := putRole out.slots dst role
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
      let (out, _, _) ← invoke env.fns env.infos env.fields fn info c.slots g (args.map Expr.local) false
      if out.value.isNone then continue
      let callee := env.fns[g]!
      let ci := env.infos[g]?.getD {}
      let mut slots := out.slots
      let mut refs := c.refs
      for i in [:callee.nslots] do
        slots := { slots with
          values := slots.values.set! (offset + i) false
          initialized := slots.initialized.set! (offset + i) false
          sharedMetadata := slots.sharedMetadata.set! (offset + i) false }
        refs := MetadataReferences.set refs (offset + i) []
      for (source, i) in args.zipIdx do
        slots := putRole slots (offset + i) (c.slots.values[source]! || ci.inputs.contains i)
        refs := MetadataReferences.set refs (offset + i) (c.refs.slots[source]!)
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
      let role := c.slots.values[dst]!.or c.slots.values[value]!
      work := work.push (advanceActor { c with
        slots := putRole c.slots dst role
        refs := MetadataReferences.accumulate c.refs a.pc dst value } actor next)
    | .call g args original dst next =>
      let (out, role, mayYield) ← invoke env.fns env.infos env.fields fn info
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
        | some role => putRole out.slots dst role
        | none => out.slots
      let (references, memory) := MetadataReferences.call env.fns a.pc c.refs g
        (args.map fun i => c.refs.slots[i]!)
      let c := { c with slots, refs := MetadataReferences.set memory dst references }
      let signaling := name == "$signalAll" ||
        (MetadataPlan.isEventSignal env.fns g && env.plan.signalFns[g]?.getD false)
      if name == "$Await" then
        let task := objectRefs (args.head?.map (fun i => c.refs.slots[i]!) |>.getD [0])
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
        let task := objectRefs (args.head?.map (fun i => c.refs.slots[i]!) |>.getD [0])
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
        let event := objectRefs (args.head?.map (fun i => c.refs.slots[i]!) |>.getD [0])
        let payload := args[1]?.map (fun i => c.refs.slots[i]!)
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
          args[i]?.map (fun slot => c.refs.slots[slot]!) |>.getD []
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
              some (objectRefs (args.head?.map (fun i => c.refs.slots[i]!) |>.getD [0]))
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
        { a with loops := { id := scope, slots := c.slots, cleanups := a.cleanups } :: a.loops } }
      work := work.push (advanceActor c actor next)
    | .backLoop scope next =>
      let entry := (a.loops.find? (·.id == scope)).getD {
        id := scope, slots := c.slots, cleanups := a.cleanups }
      let c := { c with
        slots := freshLocals info.shared entry.slots c.slots
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
        let (_, role, _) ← invoke env.fns env.infos env.fields fn info c.slots target
          (g.arguments.map Expr.local)
        canComplete := role.isSome
        canSignal := env.plan.signalFns[target]?.getD false
      let mut actors := c.actors
      for (child, pc) in g.children do
        actors := actors.set! child {
          pc, context := a.context, canComplete, canSignal
          task := g.task.map fun slot => c.refs.slots[slot]! }
      let started := { c with
        actors, groups := c.groups.set! group { active := true }
        launches := c.launches.filter (· != group) ++ [group] }
      let started := g.task.map (fun slot => setTask started (started.refs.slots[slot]!) 1) |>.getD started
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
      let (_, role, _) ← invoke env.fns env.infos env.fields fn info c.slots g (args.map Expr.local)
      if (← get).validateUses && role.getD false then
        refuse fn info "enter a spawned task's result field containing executable data"
      work := work.push (advanceActor c actor next)
    | .finishTask value =>
      if (← get).validateUses && c.slots.values[value]! then
        refuse fn info "enter a spawned task's result field containing executable data"
      let task := a.task.getD [0]
      let c := setTask c task 2 (some (c.refs.slots[value]!))
      for awake in wake (beginSignal env.plan c actor none) task true
          (some (c.refs.slots[value]!)) do work := work.push awake
    | .finish value =>
      if actor == 0 then
        let role := c.slots.values[value]!
        let c := { c with actors := c.actors.modify actor fun a =>
          { a with status := .done, cleanups := [] } }
        work := work.push (queue c [.cancel 0, .result role])
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
        slots := putRole c.slots dst c.slots.values[value]!
        refs := MetadataReferences.set c.refs dst c.refs.slots[value]!
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
      let role := c.slots.values[value]!
      let c := { c with actors := c.actors.modify actor fun a =>
        { a with status := .done, cleanups := [] } }
      work := work.push (queue c [.cancel 0, .result role])
  return { slots := finalSlots.getD slots, value := result, yielded }
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
        ci.inputs.contains j || args[j]?.getD false) |>.toArray
      let entry : Slots := {
        values, sharedMetadata := values
        initialized := (List.range callee.nslots).map
          (fun j => j < callee.arity : Nat → Bool) |>.toArray
        written := Array.replicate callee.nslots false }
      modify fun st => { st with seen := values }
      discard <| expr fns infos fields callee ci entry (ci.body.getD callee.body)
      let observed := (← get).seen
      let possible := { entry with
        values := observed, initialized := Array.replicate callee.nslots true
        sharedMetadata := Array.replicate callee.nslots false }
      for d in ((← get).sites[i]?.getD (false, [])).2 do
        discard <| expr fns infos fields callee ci possible d
  let (_, result) ← action.run { state with
    discovery := false, validateUses := true, validateShared := true
    live := #[], liveSeen := {} }
  return result

/-- Solve recursive call contexts and loop back edges to a fixed point.
    Hidden witnesses do not taint an unrelated result: return roles come
    from the body, rather than the union of physical call arguments. -/
def check (fns : Array Fn) (infos : Array Info) (fields : Array (List Nat))
    (debug : Bool := false) : Except String Unit := do
  let action : M Unit := do
    let runContext (key : Key) : M Flow := do
      let (i, args) := key
      let some fn := fns[i]? | throw "internal: metadata call has no body"
      let info := infos[i]?.getD {}
      modify fun st => { st with active := some key }
      let values := (List.range fn.nslots).map (fun i =>
        info.inputs.contains i || args[i]?.getD false) |>.toArray
      let initialized := (List.range fn.nslots).map (fun i => i < fn.arity : Nat → Bool) |>.toArray
      let slots : Slots := {
        values, initialized, sharedMetadata := values
        written := Array.replicate fn.nslots false }
      let body := info.body.getD fn.body
      modify fun st => { st with seen := values }
      let (background, cleanups) := (← get).sites[i]?.getD (false, [])
      if !background && cleanups.isEmpty then
        return ← expr fns infos fields fn info slots body
      let saved ← get
      -- Discover potential metadata without validating provisional or
      -- unreachable call contexts. Only the actual replay queues live calls.
      modify fun st => { st with
        seen := values, discovery := true
        validateUses := false, validateShared := false }
      let out ← expr fns infos fields fn info slots body
      let seen := (← get).seen
      modify fun st => { st with
        discovery := saved.discovery
        validateUses := saved.validateUses, validateShared := saved.validateShared }
      -- Opaque witness forwarding in cleanup needs no schedule exploration.
      -- Probe every potentially observed role against executable boundaries;
      -- shared writes also matter because another continuation can read them.
      let cleanupSlots := { slots with
        values := seen
        initialized := Array.replicate fn.nslots true
        sharedMetadata := Array.replicate fn.nslots false }
      let mut metadataCleanup := false
      for d in cleanups do
        match probeCleanup fns infos fields fn info cleanupSlots d (← get) with
        | .error _ => metadataCleanup := true
        | .ok discovered =>
          modify fun st => { st with
            summaries := discovered.summaries
            indices := discovered.indices, changed := discovered.changed }
        if (MetadataPlan.assigns d).any (fun i =>
            info.shared.contains i && seen[i]?.getD false) then
          metadataCleanup := true
      let needsSchedule := metadataCleanup || (background &&
        (info.shared.any (fun i => seen[i]?.getD false) ||
          out.value.getD false || out.returned.getD false))
      if needsSchedule then
        let cached := (← get).plans[i]?.getD none
        let plan ← match cached with
          | some plan => pure plan
          | none => do
            let bodies := fns.mapIdx fun j f => { f with body := (infos[j]?.getD {}).body.getD f.body }
            let plan := MetadataPlan.build bodies info.metadataWrites fn.nslots body (some i)
              (infos.map (·.metadataWrites)) (infos.map (·.source))
            modify fun st => { st with plans := st.plans.set! i (some plan) }
            pure plan
        if debug then dbg_trace s!"metadata selected {fn.name}: slots={plan.slots}, actors={plan.actors}"
        return ← schedule { fns, infos, fields, fn, info, plan } slots
      if saved.validateUses then
        return ← expr fns infos fields fn info slots body
      return out
    let seedRoots : M Unit := do
      for i in [:fns.size] do
        let info := infos[i]?.getD {}
        if info.source.slots.any (fun (_, s) => s.frame != fns[i]!.name) then continue
        discard <| request (i, (List.range fns[i]!.arity).map info.inputs.contains)
    seedRoots
    let mut growing := true
    while growing do
      modify fun st => { st with changed := false }
      let summaries := (← get).summaries
      for (summary, index) in summaries.zipIdx do
        let i := summary.key.1
        let info := infos[i]?.getD {}
        -- Only summary solving is cached. The final replay still checks
        -- every live context with stable shared-storage modes. Cleanup
        -- relevance probes have private call queues, so keep those frames
        -- out of this dependency cache.
        let cacheable := ((← get).sites[i]?.getD (false, [])).2.isEmpty
        let current := (← get).summaries
        if cacheable && summary.cached && summary.dependencies.all (fun (j, result, yielded) =>
            let s := current[j]!
            s.result == result && s.yielded == yielded) then continue
        modify fun st => { st with dependencies := if cacheable then some {} else none }
        let validate := (← get).validateUses
        -- Borrowed locals are validated against their actual owner by the
        -- inlined graph. Discovery can also request a provisional summary
        -- using old capture arguments; that summary is not a live frame.
        if info.source.slots.any (fun (_, s) => s.frame != fns[i]!.name) then
          modify fun st => { st with validateUses := false }
        let out ← runContext summary.key
        modify fun st => { st with validateUses := validate }
        let dependencies := ((← get).dependencies.getD {}).toList.toArray.map fun (j, result, yielded) =>
          (j, result, yielded)
        modify fun st => { st with
          dependencies := none
          summaries := st.summaries.modify index fun s => { s with dependencies, cached := cacheable } }
        let returned := (joinRole out.value out.returned).map (· || info.metadataResult)
        let result := joinRole summary.result returned
        let yielded := summary.yielded || out.yielded
        if result != summary.result || yielded != summary.yielded then
          modify fun st => { st with summaries := st.summaries.modify index (fun s => { s with result, yielded }), changed := true }
      growing := (← get).changed
    -- A summary may grow from a real return to a metadata return. Follow
    -- calls again from the roots using the stable summaries: provisional
    -- argument contexts can disappear and must not be validated as live.
    modify fun st => { st with validateShared := true, validateUses := true }
    seedRoots
    let mut index := 0
    while index < (← get).live.size do
      let key := (← get).live[index]!
      index := index + 1
      discard <| runContext key
  let borrowed := MetadataPlan.borrows fns (infos.map (·.source))
  let sites := fns.mapIdx fun i fn =>
    let (background, cleanups) := MetadataPlan.sites fns ((infos[i]?.getD {}).body.getD fn.body)
    (background || borrowed[i]!, cleanups)
  discard <| action.run { debug, plans := Array.replicate fns.size none, sites }

end OpenVerse.Front.MetadataFlow
