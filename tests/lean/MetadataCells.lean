import OpenVerse.Front.MetadataCells

open OpenVerse.Front.MetadataCells

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def payload (m : Memory) (refs : Refs) : IO Payload := do
  let some value := readCell m refs | throw <| IO.userError "expected a private cell"
  return value

private def write (m : Memory) (refs : Refs) (value : Payload) : IO Memory := do
  let some m := writeCell m refs value | throw <| IO.userError "expected a private write"
  return m

private def models : IO Unit := do
  let real : Payload := {}
  let metadata : Payload := { role := true }
  let (a, m) := allocate (initialRefs 4 fun _ => []) 0 true [metadata]
  let m := setLocal m 0 a
  let (frame, m) := allocate m 1 false [{ refs := a }]
  let m := setLocal m 1 frame
  let m ← write m a real
  expect (!(← payload m (loadRefs m frame 0)).role) "frame aliases must see strong overwrites"
  let (b, m) := allocate m 0 true [metadata]
  let old := getLocal m 0
  expect (old == [older 0] && b == [recent 0]) "allocation must demote saved local aliases"
  expect (loadRefs m (getLocal m 1) 0 == old) "allocation must demote frame-field aliases"
  expect (!(← payload m old).role && (← payload m b).role) "two live cells must remain distinct"
  let m ← write m b real
  expect (!(← payload m old).role) "writing the recent cell must not relabel an older cell"
  let m ← write m old metadata
  expect ((← payload m old).role && !(← payload m b).role) "one older object is independently writable"
  let (c, m) := allocate m 0 true [real]
  expect (!(m.nodes[older 0]?.getD {}).unique) "several older instances must lose uniqueness"
  let m ← write m old real
  expect ((← payload m old).role) "weak overwrite must preserve another older instance's metadata"
  let m ← write m c metadata
  let m ← write m c real
  expect (!(← payload m c).role) "the newest instance remains strongly writable"
  expect ((← payload m old).role) "strong recent overwrite must preserve the older summary"

  let (original, m) := allocate empty 8 true [real]
  let pending := demotePayloadForAllocation m 8 { refs := original }
  let (next, m) := allocate m 8 true [{ refs := original }]
  expect ((← payload m next).refs == [older 8]) "constructor operands refer to the previous object"
  expect (pending.refs == (← payload m next).refs) "pending caller values need the same allocation demotion"
  expect (loadRefs m next 0 == [older 8]) "payload reference fields must match constructor demotion"
  let (left, m) := allocate m 9 true [metadata]
  let (right, m) := allocate m 10 true [real]
  let targets := joinRefs left right
  let m ← write m targets real
  expect ((← payload m left).role) "a may-alias write cannot erase an untouched metadata cell"
  expect (!(← payload m right).role) "a weak real write need not taint an independently real cell"

  let pair : Payload := { role := true, parts := some [true, false] }
  let (cell, m) := allocate empty 20 true [pair]
  expect ((← payload m cell).parts == some [true, false]) "preserve immediate tuple columns"
  let snapshot := m
  let changed ← write m cell real
  expect (!(← payload changed cell).role && (← payload snapshot cell).role) "snapshots retain pre-write payloads"
  let merged := join snapshot changed
  expect ((← payload merged cell).parts == some [true, false]) "join a real overwrite with known tuple columns"
  expect (join m m == m) "memory joins must be idempotent"
  expect ((joinPayload pair metadata).parts.isNone) "an opaque metadata path erases column precision"
  expect ((joinPayload pair { role := true, parts := some [false, true] }).parts == some [true, true])
    "tuple branches join component roles"
  expect ((joinPayload pair { role := true, parts := some [true] }).parts.isNone)
    "different tuple shapes lose column precision"

  let (env, m) := allocate m 21 false [{ refs := cell }]
  let (wrapper, m) := allocate m 22 false [{ refs := env }]
  expect ((readCell m env).isNone) "ordinary transport objects must not become private cells"
  expect ((readCell m [0]).isNone && (readCell m [1]).isNone && (readCell m []).isNone)
    "unknown and caller objects do not justify private permissions"
  let escaped := markEscaped m wrapper
  expect ((escaped.nodes[cell.head!]?.getD {}).escaped && (← payload escaped cell).role)
    "escape must reach containers without dropping known payload metadata"
  expect ((writeCell escaped cell real).isNone) "an escaped cell cannot receive private write permissions"
  expect ((← payload (widen m wrapper) cell).role) "unmodeled writers widen reachable cells"
  expect ((writeCell (storeRefs m cell 0 []) cell real).isNone)
    "ordinary reference writes cannot bypass payload role updates"
  expect ((writeCell (storeRefs m [0] 0 cell) cell real).isNone)
    "unknown stores cannot retain a private-cell permission"
  let (fresh, recovered) := allocate escaped 20 true [real]
  expect (!(← payload recovered fresh).role) "a new recent cell does not inherit an older escape"
  expect ((writeCell recovered [older 20] real).isNone && (← payload recovered [older 20]).role)
    "saved aliases of the escaped instance retain taint and lose write permissions"
  expect ((← payload (writeKnownCells escaped cell real) cell).role)
    "ordinary admitted real writes weakly retain prior escaped payload metadata"
  let (onlyReal, realMemory) := allocate empty 23 true [real]
  let realEscaped := markEscaped realMemory onlyReal
  expect (!(← payload (writeKnownCells realEscaped onlyReal real) onlyReal).role)
    "ordinary real writes must not invent metadata"
  expect ((← payload (widen realMemory onlyReal) onlyReal).role)
    "unknown writers conservatively widen payload roles"
  expect (loadRefs escaped wrapper 0 == env) "escape alone retains known container aliases"
  expect ((loadRefs (widen m wrapper) wrapper 0).contains 0)
    "unknown writers also widen ordinary container fields"
  expect ((readCell m (joinRefs cell env)).isNone && mayPrivate m (joinRefs cell env))
    "mixed private and ordinary references need conservative payload fallback"
  let (_, ordinary) := allocate empty 20 false [real]
  let mixed := join snapshot ordinary
  expect ((readCell mixed cell).isNone && mayPrivate mixed cell)
    "a join can lose private proof without losing possible private payloads"
  let exposed := writeKnownCells realMemory [0] real
  expect ((writeCell exposed onlyReal metadata).isNone)
    "an unknown ordinary writer cannot preserve private write permissions"
  let (wrongShape, m) := allocate empty 30 true [real, metadata]
  expect ((readCell m wrongShape).isNone) "a private cell has exactly one payload field"
  IO.println "PASS private-cell recency, aliases, tuple columns, snapshots and escape models"

private def fieldPayloadModels : IO Unit := do
  let tuple : Payload := { role := true, parts := some [true, false] }
  let other : Payload := { role := true, parts := some [false, true] }
  let (frame, m) := allocate empty 100 false [tuple, {}]
  expect ((readFieldPayload m frame 0).map (·.parts) == some (some [true, false]))
    "lazy transport must preserve the real tuple column beside metadata"
  let changed := storeFieldPayload m frame 0 other
  expect ((readFieldPayload changed frame 0).map (·.parts) == some (some [false, true]))
    "a unique transport field can strongly replace its tuple payload"
  let forgotten := storeRefs m frame 0 []
  expect ((readFieldPayload forgotten frame 0).isNone)
    "an ordinary reference write invalidates payload facts"
  expect ((readFieldPayload (join m forgotten) frame 0).isNone &&
    (readFieldPayload (join forgotten m) frame 0).isNone)
    "joins must not resurrect a field forgotten on an existing-object path"
  expect ((readFieldPayload (join m empty) frame 0).map (·.parts) == some (some [true, false]))
    "an absent-object path contributes no field value"
  expect ((readFieldPayload (markEscaped m frame) frame 0).isNone &&
    (readFieldPayload (widen m frame) frame 0).isNone)
    "escaped or unknown-written transport fields do not retain precise permissions"

  let (cell, m) := allocate empty 101 true [{}]
  let (frame, m) := allocate m 102 false [{ tuple with refs := cell }]
  let (_, m) := allocate m 101 true [{ role := true }]
  expect ((readFieldPayload m frame 0).map (·.refs) == some [older 101])
    "recency must rebase references inside transport payload facts"
  let (_, m) := allocate m 102 false [{}]
  expect ((readFieldPayload m [older 102] 0).map (·.parts) == some (some [true, false]))
    "recency must rebase transport payload owner identities"
  let (_, m) := allocate m 102 false [{}]
  let weak := storeFieldPayload m [older 102] 0 {}
  expect ((readFieldPayload weak [older 102] 0).map (·.parts) == some (some [true, false]))
    "a summary write cannot erase another older transport's tuple metadata"
  expect ((readFieldPayload weak [recent 102] 0).map (·.role) == some false)
    "summary writes do not taint a separate recent transport"

  let (first, m) := allocate empty 103 false [tuple]
  let m := storeRefs m first 0 []
  let (_, m) := allocate m 103 false [{}]
  let (_, m) := allocate m 103 false [tuple]
  expect ((readFieldPayload m [older 103] 0).isNone)
    "demotion cannot recover a fact missing from an older instance"
  let (_, m) := allocate empty 104 false [tuple]
  let (second, m) := allocate m 104 false [{}]
  let m := storeRefs m second 0 []
  let (_, m) := allocate m 104 false [tuple]
  expect ((readFieldPayload m [older 104] 0).isNone)
    "demotion cannot retain a fact missing from the previous recent instance"
  IO.println "PASS compiler transport field payloads, tuple columns, invalidation and recency joins"

private def reachabilityModels : IO Unit := do
  expect (!mayReachPrivate empty [0] && !mayReachPrivate empty [1])
    "unknown roots without tracked cells leave activation to callee capabilities"
  let (cell, m) := allocate empty 200 true [{ role := true }]
  let (tuple, m) := allocate m 201 false [{ refs := cell }]
  let (array, m) := allocate m 202 false [{ refs := tuple }]
  let (frame, m) := allocate m 203 false [{ refs := array }]
  expect (mayReachPrivate m cell && mayReachPrivate m tuple && mayReachPrivate m array && mayReachPrivate m frame)
    "callee replay must follow private identities through all container layers"
  expect (mayReachPrivate m [0] && mayReachPrivate m [1])
    "caller and unknown roots can alias a tracked private cell"
  let (unrelated, m) := allocate m 204 false [{}]
  expect (!mayReachPrivate m unrelated && !mayReachPrivate m [])
    "unrelated ordinary data must not acquire a private call capability"
  let (a, m) := allocate m 205 false [{}]
  let (b, m) := allocate m 206 false [{ refs := a }]
  let m := storeRefs m a 0 b
  expect (!mayReachPrivate m a) "an ordinary cycle without a cell must terminate"
  let m := storeFieldPayload m b 0 { refs := frame }
  expect (mayReachPrivate m a) "a container cycle can lead to a private cell"
  let (_, ordinary) := allocate empty 200 false [{}]
  let mixed := join m ordinary
  expect (mayReachPrivate mixed cell)
    "possible private payloads survive loss of an all-private node proof"
  let external := storeRefs m [1] 0 frame
  expect (mayReachPrivate external [1])
    "actual calls through caller-owned carriers retain private reachability"
  IO.println "PASS transitive private call capability through carriers, cycles and caller aliases"

private def reachabilityScale : IO Unit := do
  let count := 32000
  let started ← IO.monoMsNow
  let (leaf, initial) := allocate empty 0 true [{}]
  let mut m := initial
  let mut refs := leaf
  for site in [1:count] do
    let (head, next) := allocate m site false [{ refs }]
    m := next
    refs := head
  expect (mayReachPrivate m refs) "callee capability must traverse a 32k transport chain"
  let (unrelated, completed) := allocate m count false [{}]
  expect (!mayReachPrivate completed unrelated) "an unrelated carrier stays outside the private chain"
  IO.println s!"PASS {count} indexed transport reachability ({(← IO.monoMsNow) - started}ms)"

private def scale : IO Unit := do
  let count := 32000
  let started ← IO.monoMsNow
  let mut m := empty
  let mut previous : Refs := []
  for site in [:count] do
    let (refs, next) := allocate m site true [{ refs := previous }]
    m := next
    previous := refs
  expect (m.nodes.size == count && m.cells.size == count) "dense allocation sites must remain distinct"
  expect (!(← payload m previous).role) "the long chain is initially real"
  let escaped := markEscaped m previous
  expect (escaped.nodes.size == count && escaped.nodes.all (fun _ n => n.escaped))
    "escape must visit the complete 32k container/cell chain"
  expect ((writeCell escaped previous {}).isNone && !(← payload escaped previous).role)
    "escape loses write permissions without inventing metadata in an all-real chain"
  IO.println s!"PASS {count} distinct allocations and transitive escape ({(← IO.monoMsNow) - started}ms)"

/-- A concrete reference remains its allocation index forever. This model
    does not use the abstract heap's recency identities or update rules. -/
private structure ConcreteObject where
  site : Nat
  metadata : Bool
  escaped : Bool := false
  deriving Inhabited

private structure Concrete where
  objects : Array ConcreteObject := #[]
  locals : Array (Option Nat) := #[none, none, none]

private def representedBy (c : Concrete) (index : Nat) : Nat :=
  let site := c.objects[index]!.site
  if (c.objects.toList.zipIdx).any (fun (object, later) => later > index && object.site == site) then
    older site else recent site

private def refines (c : Concrete) (m : Memory) : IO Unit := do
  for (object, index) in c.objects.toList.zipIdx do
    let id := representedBy c index
    let value ← payload m [id]
    expect (!object.metadata || value.role) "abstract payload lost a concrete metadata value"
    if let some field := readFieldPayload m [id] 0 then
      expect (!object.metadata || field.role) "transport field facts lost a concrete metadata value"
    let some node := m.nodes[id]? | throw <| IO.userError "missing concrete allocation identity"
    expect (!object.escaped || node.escaped) "abstract heap lost a concrete escape"
    if node.unique then
      let represented := (c.objects.toList.zipIdx).filter fun (_, i) => representedBy c i == id
      expect (represented.length ≤ 1) "strong-update permission covers several concrete cells"
  for (value, slot) in c.locals.toList.zipIdx do
    if let some index := value then
      expect ((getLocal m slot).contains (representedBy c index)) "saved alias points to another allocation"

private def modelStep (action : Nat) (c : Concrete) (m : Memory) : IO (Concrete × Memory) := do
  if action < 4 then
    let site := action / 2
    let metadata := action % 2 == 1
    let allocated := allocate m site true [{ role := metadata }]
    let index := c.objects.size
    return ({ objects := c.objects.push { site, metadata }, locals := c.locals.set! 2 (some index) },
      setLocal allocated.2 2 allocated.1)
  if action < 6 then
    let slot := action - 4
    return ({ c with locals := c.locals.set! slot (c.locals[2]?.getD none) },
      setLocal m slot (getLocal m 2))
  let slot := if action < 10 then (action - 6) / 2 else action - 10
  let some index := c.locals[slot]?.getD none | return (c, m)
  let refs := getLocal m slot
  if action ≥ 10 then
    return ({ c with objects := c.objects.modify index fun object => { object with escaped := true } },
      markEscaped m refs)
  let metadata := action % 2 == 1
  match writeCell m refs { role := metadata } with
  | some changed =>
    expect (!c.objects[index]!.escaped) "private write permission escaped a concrete boundary"
    return ({ c with objects := c.objects.modify index fun object => { object with metadata } }, changed)
  | none =>
    -- The ordinary object policy admits a real value. Metadata does not
    -- acquire a permission merely because its private proof was lost.
    if metadata then return (c, m)
    return ({ c with objects := c.objects.modify index fun object => { object with metadata := false } },
      writeKnownCells m refs {})

private partial def explore (depth : Nat) (c : Concrete) (m : Memory) : IO Nat := do
  refines c m
  if depth == 0 then return 1
  let mut count := 1
  for action in [:12] do
    let (next, memory) ← modelStep action c m
    count := count + (← explore (depth - 1) next memory)
  return count

private def concreteModel : IO Unit := do
  let initial := initialRefs 3 fun _ => []
  let exhaustive ← explore 4 {} initial
  let mut seed := 572
  let mut transitions := 0
  for _ in [:512] do
    let mut c : Concrete := {}
    let mut m := initial
    let mut snapshot := initial
    for step in [:40] do
      seed := (seed * 1664525 + 1013904223) % 4294967296
      let (next, memory) ← modelStep ((seed / 65536) % 12) c m
      c := next
      m := memory
      if step % 7 == 0 then
        m := join m snapshot
        snapshot := memory
      refines c m
      transitions := transitions + 1
  IO.println s!"PASS concrete heap refinement: {exhaustive} exhaustive states, {transitions} seeded transitions with joins"

def main (args : List String) : IO Unit :=
  if args.contains "--scale" then scale
  else if args.contains "--reach-scale" then reachabilityScale
  else if args.contains "--model" then concreteModel else do
    models
    fieldPayloadModels
    reachabilityModels
