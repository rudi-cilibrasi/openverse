/- Compiler-only provenance analysis. Metadata is not a Core runtime tag. -/
import OpenVerse.Front.Syntax
import OpenVerse.Core.Syntax
import OpenVerse.Front.MetadataPlan
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
  deriving Inhabited

private inductive ActorStatus where
  | idle | running | waiting (resumable : Bool) | joining (group : Nat) | done
  deriving BEq, Inhabited

private structure LoopEntry where
  id : Nat
  slots : Slots
  cleanups : List Nat
  deriving BEq, Inhabited

private structure Actor where
  pc : Nat := 0
  status : ActorStatus := .idle
  cleanups : List Nat := []
  loops : List LoopEntry := []
  deriving BEq, Inhabited

private structure GroupStatus where
  active : Bool := false
  started : Nat := 0
  winner : Option Nat := none
  deriving BEq, Inhabited

private structure Configuration where
  slots : Slots
  actors : Array Actor
  groups : Array GroupStatus
  current : Option Nat := some 0
  startup : List Nat := []
  deriving BEq, Inhabited

private def configurationKey (c : Configuration) : List Nat :=
  [c.current.getD c.actors.size, c.startup.length] ++ c.startup ++
  c.actors.toList.flatMap (fun a =>
    let (tag, data) := match a.status with
      | .idle => (0, 0) | .running => (1, 0)
      | .waiting ready => (2, if ready then 1 else 0)
      | .joining g => (3, g) | .done => (4, 0)
    [a.pc, tag, data, a.cleanups.length] ++ a.cleanups ++
      [a.loops.length] ++ a.loops.flatMap (fun s => [s.id, s.cleanups.length] ++ s.cleanups)) ++
  c.groups.toList.flatMap (fun g =>
    [if g.active then 1 else 0, g.started, g.winner.map (· + 1) |>.getD 0])

private def joinConfiguration (a b : Configuration) : Configuration := { b with
  slots := joinSlots a.slots b.slots
  actors := a.actors.zipWith (fun x y => { y with
    loops := x.loops.zipWith (fun s t => { t with slots := joinSlots s.slots t.slots }) y.loops }) b.actors }

private def putRole (s : Slots) (i : Nat) (role : Bool) : Slots := { s with
  values := s.values.set! i role
  initialized := s.initialized.set! i true
  sharedMetadata := s.sharedMetadata.set! i role }

private def nextActor (c : Configuration) : Configuration :=
  match c.startup with
  | a :: rest => { c with current := some a, startup := rest }
  | [] => { c with current := none }

private def advanceActor (c : Configuration) (a pc : Nat) : Configuration := { c with
  current := some a
  actors := c.actors.modify a fun t => { t with pc, status := .running } }

private def groupReady (p : MetadataPlan.Plan) (c : Configuration) (i : Nat) : Bool :=
  let g := p.groups[i]!
  let state := c.groups[i]!
  if g.kind == .branch then state.started > 0
  else if g.kind == .sync then
    state.started == g.children.size &&
      g.children.all (fun (a, _) => c.actors[a]!.status == .done)
  else state.winner.isSome

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
  validateUses : Bool := false
  discovery : Bool := false
  seen : Array Bool := #[]
  plans : Array (Option MetadataPlan.Plan) := #[]
  sites : Array (Bool × List Expr) := #[]
  live : Array Key := #[]
  liveSeen : Std.HashMap Key Unit := {}
  debug : Bool := false
  active : Option Key := none

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
    return (st.summaries[i]!.result, st.summaries[i]!.yielded)
  set { st with
    indices := st.indices.insert key st.summaries.size
    summaries := st.summaries.push { key }, changed := true }
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
    (g : Nat) (es : List Expr) : M (Flow × Option Bool × Bool) := do
  let (args, out) ← arguments fns infos fields fn info slots es
  if out.value.isNone then return (out, none, false)
  let gi := infos[g]?.getD {}
  let roles := args.zipIdx.map fun (role, i) => role || gi.inputs.contains i
  if (← get).validateUses && gi.required.any (fun i => roles[i]?.getD false) then
    refuse fn info s!"provide executable evidence or a receiver to {(fns[g]?.map (·.name)).getD "a call"}"
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

/-- Cancel the current structured wait before its cleanup, then stop the
    background children owned by the frame. Completed arms can still own
    background work, so their descendants must also be visited. -/
private partial def cancelScheduled (env : ScheduleEnv) (c : Configuration)
    (actor : Nat) : M Configuration := do
  let mut c := c
  for g in env.plan.groups.toList.reverse do
    if g.owner == actor && g.kind != .branch then
      for (child, _) in g.children.toList.reverse do
        c ← cancelScheduled env c child
  let a := c.actors[actor]!
  if a.status != .done && a.status != .idle then
    if let some d := a.cleanups.head? then
      let out ← expr env.fns env.infos env.fields env.fn env.info c.slots env.plan.cleanups[d]!
      c := { c with slots := out.slots }
  c := { c with actors := c.actors.modify actor fun a =>
    { a with status := .done, cleanups := [], loops := [] } }
  for g in env.plan.groups.toList.reverse do
    if g.owner == actor && g.kind == .branch then
      for (child, _) in g.children.toList.reverse do
        c ← cancelScheduled env c child
  return c

private partial def finishGroup (env : ScheduleEnv) (c : Configuration)
    (group : Nat) : M Configuration := do
  let g := env.plan.groups[group]!
  let mut c := c
  if g.kind == .race then
    for (child, _) in g.children.toList.reverse do
      if some child != c.groups[group]!.winner then
        c ← cancelScheduled env c child
  c := { c with
    groups := c.groups.modify group fun s => { s with active := false }
    slots := putRole c.slots g.dst false }
  return advanceActor c g.owner g.next

private partial def completeScheduled (env : ScheduleEnv) (c : Configuration)
    (actor : Nat) : M Configuration := do
  let mut c := { c with actors := c.actors.modify actor fun a =>
    { a with status := .done, cleanups := [], loops := [] } }
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
    actors := (Array.replicate env.plan.actors {}).set! 0 {
      pc := env.plan.entry, status := .running }
    groups := Array.replicate env.plan.groups.size {} }
  let mut work := #[initial]
  let mut cursor := 0
  let mut known : Std.HashMap (List Nat) Configuration := {}
  let mut result : Option Bool := none
  let mut finalSlots : Option Slots := none
  let mut yielded := false
  while cursor < work.size do
    let incoming := work[cursor]!
    cursor := cursor + 1
    let key := configurationKey incoming
    let c := match known[key]? with
      | none => incoming
      | some old => joinConfiguration old incoming
    if (known[key]?).any (· == c) then continue
    known := known.insert key c
    let some actor := c.current | do
      -- Only a global wait admits cancellation or a different runnable
      -- child. Startup prefixes and nonwaiting loops remain atomic.
      if c.actors.any (fun a => match a.status with
          | .waiting _ | .joining _ => true | _ => false) then
        yielded := true
        discard <| cancelScheduled env c 0
        for i in [:c.actors.size] do
          if c.actors[i]!.status == .waiting true then
            work := work.push (advanceActor c i c.actors[i]!.pc)
      continue
    let a := c.actors[actor]!
    match env.plan.nodes[a.pc]! with
    | .jump pc => work := work.push (advanceActor c actor pc)
    | .atom e dst next permission =>
      let info := match permission with
        | none => env.info
        | some p => { env.info with metadataWrites := p :: env.info.metadataWrites }
      let out ← expr env.fns env.infos env.fields env.fn info c.slots e
      if let some role := out.value then
        work := work.push (advanceActor { c with slots := putRole out.slots dst role } actor next)
    | .test condition yes no =>
      let out ← expr env.fns env.infos env.fields env.fn env.info c.slots condition
      if out.value.isSome then
        work := work.push (advanceActor { c with slots := out.slots } actor yes)
      work := work.push (advanceActor c actor no)
    | .choose yes no =>
      work := work.push (advanceActor c actor yes)
      work := work.push (advanceActor c actor no)
    | .accumulate dst value next =>
      let role := c.slots.values[dst]!.or c.slots.values[value]!
      work := work.push (advanceActor { c with slots := putRole c.slots dst role } actor next)
    | .call g args original dst next =>
      let (out, role, mayYield) ← invoke env.fns env.infos env.fields env.fn env.info
        c.slots g (args.map Expr.local)
      if out.value.isNone then continue
      let name := (env.fns[g]?.map (·.name)).getD ""
      let duration := if name == "$Sleep" then original.head?.bind constantSleep else none
      let mayYield := if name == "$Sleep" then
          duration.map (fun n => decide (n > 0.0)) |>.getD true
        else mayYield
      let mustYield := name == "$Sleep" && duration.any (fun n => decide (n > 0.0))
      let slots := match role with
        | some role => putRole out.slots dst role
        | none => out.slots
      if !mustYield && role.isSome then
        work := work.push (advanceActor { c with slots } actor next)
      if mayYield then
        let waiting := { c with slots, actors := c.actors.modify actor fun a =>
          { a with pc := next, status := .waiting role.isSome } }
        work := work.push (nextActor waiting)
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
        slots := freshLocals env.info.shared entry.slots c.slots
        actors := c.actors.modify actor fun a => { a with cleanups := entry.cleanups } }
      work := work.push (advanceActor c actor next)
    | .leaveLoop scope next =>
      let cleanups := (a.loops.find? (·.id == scope)).map (·.cleanups) |>.getD a.cleanups
      let c := { c with actors := c.actors.modify actor fun a =>
        { a with cleanups, loops := (a.loops.dropWhile (·.id != scope)).tail } }
      work := work.push (advanceActor c actor next)
    | .fork group =>
      let g := env.plan.groups[group]!
      let mut actors := c.actors
      for (child, pc) in g.children do actors := actors.set! child { pc }
      let c := { c with actors, groups := c.groups.set! group { active := true } }
      work := work.push (advanceActor c actor g.advance)
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
    | .finish value =>
      if actor == 0 then
        let role := c.slots.values[value]!
        let c := { c with actors := c.actors.modify actor fun a =>
          { a with status := .done, cleanups := [] } }
        let c ← cancelScheduled env c 0
        result := joinRole result (some role)
        finalSlots := joinOpt finalSlots (some c.slots)
      else
        work := work.push (← completeScheduled env c actor)
    | .ret value =>
      let role := c.slots.values[value]!
      let c := { c with actors := c.actors.modify actor fun a =>
        { a with status := .done, cleanups := [] } }
      let c ← cancelScheduled env c 0
      result := joinRole result (some role)
      finalSlots := joinOpt finalSlots (some c.slots)
  return { slots := finalSlots.getD slots, value := result, yielded }
end

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
        let probe := { (← get) with
          discovery := true
          validateUses := true, validateShared := true }
        match (expr fns infos fields fn info cleanupSlots d).run probe with
        | .error _ => metadataCleanup := true
        | .ok (_, discovered) =>
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
            let plan := MetadataPlan.build fns info.metadataWrites fn.nslots body
            modify fun st => { st with plans := st.plans.set! i (some plan) }
            pure plan
        return ← schedule { fns, infos, fields, fn, info, plan } slots
      if saved.validateUses then
        return ← expr fns infos fields fn info slots body
      return out
    let seedRoots : M Unit := do
      for i in [:fns.size] do
        let info := infos[i]?.getD {}
        discard <| request (i, (List.range fns[i]!.arity).map info.inputs.contains)
    seedRoots
    let mut growing := true
    while growing do
      modify fun st => { st with changed := false }
      let summaries := (← get).summaries
      for (summary, index) in summaries.zipIdx do
        let i := summary.key.1
        let info := infos[i]?.getD {}
        let out ← runContext summary.key
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
  let sites := fns.mapIdx fun i fn =>
    MetadataPlan.sites fns ((infos[i]?.getD {}).body.getD fn.body)
  discard <| action.run { debug, plans := Array.replicate fns.size none, sites }

end OpenVerse.Front.MetadataFlow
