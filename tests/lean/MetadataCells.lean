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

def main (args : List String) : IO Unit :=
  if args.contains "--scale" then scale else models
