/- Compiler-only provenance analysis. Metadata is not a Core runtime tag. -/
import OpenVerse.Front.Syntax
import OpenVerse.Core.Syntax
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

private def withExits (a b : Flow) : Flow := { b with
  returned := joinRole a.returned b.returned
  broken := joinOpt a.broken b.broken }

private abbrev Key := Nat × List Bool

private structure Summary where
  key : Key
  result : Option Bool := none
  deriving Inhabited

private structure State where
  summaries : Array Summary := #[]
  indices : Std.HashMap Key Nat := {}
  changed : Bool := false
  /-- Shared-local modes depend on complete return summaries, not an early
      real-only approximation of a recursive initializer. -/
  validateShared : Bool := false
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

private def request (key : Key) : M (Option Bool) := do
  let st ← get
  if st.validateShared && !st.liveSeen.contains key then
    set { st with live := st.live.push key, liveSeen := st.liveSeen.insert key () }
  let st ← get
  if let some i := st.indices[key]? then return st.summaries[i]!.result
  set { st with
    indices := st.indices.insert key st.summaries.size
    summaries := st.summaries.push { key }, changed := true }
  return none

mutual
private partial def expr (fns : Array Fn) (infos : Array Info)
    (fields : Array (List Nat)) (fn : Fn) (info : Info) (slots : Slots) : Expr → M Flow
  | .lit _ => pure { slots }
  | .local i => pure { slots, value := some (slots.values[i]?.getD false) }
  | .assign i e => do
    let out ← expr fns infos fields fn info slots e
    let some role := out.value | return out
    let role := role || info.seeds.contains i
    if role && info.uses.contains i then
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
        written := out.slots.written.set! i true
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
    if ["$syncMark", "$raceMark", "$rushMark"].contains name then
      if let [.prim .mkArr arms] := es then
        return ← concurrent fns infos fields fn info slots (name == "$syncMark") arms
    let (args, out) ← arguments fns infos fields fn info slots es
    if out.value.isNone then return out
    let gi := infos[g]?.getD {}
    let roles := args.zipIdx.map fun (role, i) => role || gi.inputs.contains i
    if gi.required.any (fun i => roles[i]?.getD false) then
      refuse fn info s!"provide executable evidence or a receiver to {(fns[g]?.map (·.name)).getD "a call"}"
    let result ← request (g, roles)
    return { out with value := result }
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
        if args[1]?.getD false && !metadataField then
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
      returned := joinRole t.returned e.returned, broken := joinOpt t.broken e.broken }
  | .forE i source filt body => do
    let source ← expr fns infos fields fn info slots source
    let some item := source.value | return source
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
    let mut growing := true
    while growing do
      let out ← expr fns infos fields fn info head body
      returned := joinRole returned out.returned
      broken := joinOpt broken out.broken
      let next := if out.value.isSome then freshLocals info.shared slots (joinSlots head out.slots) else head
      growing := next != head
      head := next
    return { slots := broken.getD head, value := broken.map (fun _ => false), returned }
  | .brk => pure { slots, value := none, broken := some slots }
  | .ret e => do
    let out ← expr fns infos fields fn info slots e
    return { out with value := none, returned := joinRole out.returned out.value }
  | .print e => do
    let out ← expr fns infos fields fn info slots e
    return { out with value := out.value.map (fun _ => false) }

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
  let runArms (outs : Array Flow) : M (Array Flow) :=
    arms.toArray.zipIdx.mapM fun (arm, i) =>
      expr fns infos fields fn info (entry outs i) arm
  -- Every arm starts independently, including when a sibling has no
  -- normal return. Exchange their shared-cell roles until they stabilize.
  let validate := (← get).validateShared
  modify fun st => { st with validateShared := false }
  let mut outs : Array Flow := arms.toArray.map fun _ => { slots }
  let mut growing := true
  while growing do
    let next ← runArms outs
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
  return { slots := finalSlots, value := if normal then some false else none, returned, broken }

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
      expr fns infos fields fn info slots (info.body.getD fn.body)
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
        if result != summary.result then
          modify fun st => { st with summaries := st.summaries.modify index (fun s => { s with result }), changed := true }
      growing := (← get).changed
    -- A summary may grow from a real return to a metadata return. Follow
    -- calls again from the roots using the stable summaries: provisional
    -- argument contexts can disappear and must not be validated as live.
    modify fun st => { st with validateShared := true }
    seedRoots
    let mut index := 0
    while index < (← get).live.size do
      let key := (← get).live[index]!
      index := index + 1
      discard <| runContext key
  discard <| action.run { debug }

end OpenVerse.Front.MetadataFlow
