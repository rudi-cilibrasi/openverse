/- Compiler-only identities and payload roles for lowered logical locals. -/
import Std.Data.HashMap.Lemmas

namespace OpenVerse.Front.MetadataCells

/-- Zero denotes an unknown object, one an object supplied by a caller.
    Each dense allocation site owns two other identities: its most recent
    object and a summary of its older objects. -/
abbrev Refs := List Nat

private def normalize (refs : Refs) : Refs :=
  (refs.mergeSort (· ≤ ·)).eraseReps

def joinRefs (a b : Refs) : Refs :=
  ((normalize a).merge (normalize b) (· ≤ ·)).eraseReps

structure Payload where
  role : Bool := false
  parts : Option (List Bool) := none
  refs : Refs := []
  deriving BEq, Inhabited, Repr

/-- Immediate tuple columns follow the ordinary metadata domain. A missing
    shape with a metadata whole value cannot prove any column real. -/
def joinPayload (a b : Payload) : Payload := {
  role := a.role || b.role
  parts := match a.parts, b.parts with
    | some xs, some ys =>
      if xs.length == ys.length then some (xs.zipWith (· || ·) ys) else none
    | some xs, none => if b.role then none else some xs
    | none, some ys => if a.role then none else some ys
    | none, none => none
  refs := joinRefs a.refs b.refs }

structure Node where
  privateCell : Bool := false
  unique : Bool := true
  escaped : Bool := false
  deriving BEq, Inhabited, Repr

structure Memory where
  nslots : Nat := 0
  locals : Std.HashMap Nat Refs := {}
  fields : Std.HashMap (Nat × Nat) Refs := {}
  fieldPayloads : Std.HashMap (Nat × Nat) Payload := {}
  cells : Std.HashMap Nat Payload := {}
  nodes : Std.HashMap Nat Node := {}
  deriving BEq, Inhabited

def empty : Memory := {}

def initialRefs (nslots : Nat) (value : Nat → Refs) : Memory := Id.run do
  let mut locals := {}
  for i in [:nslots] do
    let refs := normalize (value i)
    if !refs.isEmpty then locals := locals.insert i refs
  return { nslots, locals }

def getLocal (m : Memory) (slot : Nat) : Refs :=
  if slot < m.nslots then m.locals[slot]?.getD [] else [0]

def setLocal (m : Memory) (slot : Nat) (refs : Refs) : Memory :=
  if slot ≥ m.nslots then m else
    let refs := normalize refs
    { m with locals := if refs.isEmpty then m.locals.erase slot else m.locals.insert slot refs }

private def joinNode (a b : Node) : Node := {
  privateCell := a.privateCell && b.privateCell
  unique := a.unique && b.unique
  escaped := a.escaped || b.escaped }

private def joinField (fields : Std.HashMap (Nat × Nat) Refs)
    (key : Nat × Nat) (refs : Refs) : Std.HashMap (Nat × Nat) Refs :=
  fields.insert key (joinRefs (fields[key]?.getD []) refs)

private def joinCell (cells : Std.HashMap Nat Payload) (id : Nat)
    (payload : Payload) : Std.HashMap Nat Payload :=
  cells.insert id (cells[id]?.map (joinPayload · payload) |>.getD payload)

private def joinFieldPayload (facts : Std.HashMap (Nat × Nat) Payload)
    (key : Nat × Nat) (value : Payload) : Std.HashMap (Nat × Nat) Payload :=
  facts.insert key (facts[key]?.map (joinPayload · value) |>.getD value)

/-- Missing facts on an existing object mean an unknown field, rather than
    a real field. A path where the object is absent contributes no value. -/
private def joinFieldPayloads (a b : Memory) : Std.HashMap (Nat × Nat) Payload :=
  a.fieldPayloads.fold (fun out key value =>
    match b.fieldPayloads[key]? with
    | some other => out.insert key (joinPayload value other)
    | none => if b.nodes.contains key.1 then out else out.insert key value)
    (b.fieldPayloads.fold (fun out key value =>
      if a.nodes.contains key.1 then out else out.insert key value) {})

/-- Missing nodes describe paths on which that allocation has not occurred.
    A node present on both paths is unique only when both paths prove it. -/
def join (a b : Memory) : Memory := {
  nslots := min a.nslots b.nslots
  locals := b.locals.fold (fun out i refs =>
    if i < min a.nslots b.nslots then
      out.insert i (joinRefs (out[i]?.getD []) refs) else out)
    (a.locals.filter fun i _ => i < min a.nslots b.nslots)
  fields := b.fields.fold joinField a.fields
  fieldPayloads := joinFieldPayloads a b
  cells := b.cells.fold joinCell a.cells
  nodes := b.nodes.fold (fun out id node =>
    out.insert id (out[id]?.map (joinNode · node) |>.getD node)) a.nodes }

def recent (site : Nat) : Nat := 2 + 2 * site

def older (site : Nat) : Nat := 3 + 2 * site

private def replace (old fresh : Nat) (refs : Refs) : Refs :=
  normalize (refs.map fun r => if r == old then fresh else r)

/-- Rebase a pending value kept outside Memory when the next allocation at
    this site demotes its previous instance. Use the pre-allocation memory. -/
def demotePayloadForAllocation (before : Memory) (site : Nat) (payload : Payload) : Payload :=
  if before.nodes.contains (recent site) then
    { payload with refs := replace (recent site) (older site) payload.refs }
  else payload

/-- A new instance moves every alias of the previous recent object to the
    older identity, including aliases inside cell payloads and containers.
    Two different old instances force the summary's uniqueness to false. -/
private def demote (m : Memory) (site : Nat) : Memory :=
  let previous := recent site
  let summary := older site
  if !m.nodes.contains previous then m else {
    m with
    locals := m.locals.map fun _ refs => replace previous summary refs
    fields := m.fields.fold (fun out (object, field) refs =>
      joinField out (if object == previous then summary else object, field) (replace previous summary refs)) {}
    fieldPayloads := m.fieldPayloads.fold (fun out (object, field) value =>
      let missing := if object == previous then
          m.nodes.contains summary && !m.fieldPayloads.contains (summary, field)
        else object == summary && !m.fieldPayloads.contains (previous, field)
      if missing then out else
        joinFieldPayload out (if object == previous then summary else object, field)
          { value with refs := replace previous summary value.refs }) {}
    cells := m.cells.fold (fun out id payload =>
      joinCell out (if id == previous then summary else id)
        { payload with refs := replace previous summary payload.refs }) {}
    nodes := m.nodes.fold (fun out id node =>
      let id := if id == previous then summary else id
      let node := match out[id]? with
        | none => node
        | some old => { joinNode old node with unique := false }
      out.insert id node) {} }

/-- The caller assigns distinct dense sites to distinct allocation nodes.
    Private cells have exactly one payload field. Other objects transport
    references but never acquire permission to store metadata payloads.
    All live aliases must be in Memory or the operands; callers rebase any
    other pending values or saved caller locals with the same demotion. -/
def allocate (m : Memory) (site : Nat) (isPrivate : Bool)
    (values : List Payload) : Refs × Memory := Id.run do
  let values := values.map (demotePayloadForAllocation m site)
  let m := demote m site
  -- Operands were evaluated before allocation; their references denote the
  -- former recent object, not the fresh object now taking its identity.
  let id := recent site
  let privateCell := isPrivate && values.length == 1
  let mut m := { m with nodes := m.nodes.insert id { privateCell } }
  for (payload, field) in values.zipIdx do
    m := { m with fields := m.fields.insert (id, field) (normalize payload.refs)
                  fieldPayloads := m.fieldPayloads.insert (id, field)
                    { payload with refs := normalize payload.refs } }
  if privateCell then
    let payload := values.head!
    m := { m with cells := m.cells.insert id { payload with refs := normalize payload.refs } }
  return ([id], m)

/-- Ordinary containers carry aliases without granting access to cell
    payloads. Caller and unknown objects can contain unseen references. -/
def loadRefs (m : Memory) (objects : Refs) (field : Nat) : Refs :=
  objects.foldl (fun out object =>
    let unknown := object ≤ 1 || !m.nodes.contains object
    joinRefs out (joinRefs (if unknown then [0] else [])
      (m.fields[(object, field)]?.getD (if unknown then [0] else [])))) []

/-- Complete payload facts for proven compiler transport objects. Callers
    use this only for their approved transport tags, never to grant a heap
    write permission. Unknown, escaped or incompletely tracked fields fail;
    absence of a fact cannot prove that a transport field is real. -/
def readFieldPayload (m : Memory) (objects : Refs) (field : Nat) : Option Payload := do
  let first :: rest := normalize objects | none
  let read (object : Nat) : Option Payload := do
    let node ← m.nodes[object]?
    if object ≤ 1 || node.escaped then none else m.fieldPayloads[(object, field)]?
  let mut value ← read first
  for object in rest do value := joinPayload value (← read object)
  return value

private def cell? (m : Memory) (object : Nat) : Option Payload := do
  let node ← m.nodes[object]?
  if object ≤ 1 || !node.privateCell then none else m.cells[object]?

/-- Read payloads even after escape: the physical identity remains real,
    so falling back to the receiver role would lose existing payload taint.
    None means not all references are proven private cells. -/
def readCell (m : Memory) (objects : Refs) : Option Payload := do
  let objects := normalize objects
  let first :: rest := objects | none
  let mut payload ← cell? m first
  for object in rest do payload := joinPayload payload (← cell? m object)
  return payload

def writeCell (m : Memory) (objects : Refs) (payload : Payload) : Option Memory := do
  let objects := normalize objects
  if objects.isEmpty then none else pure ()
  for object in objects do
    discard <| cell? m object
    if (m.nodes[object]?.map (·.escaped)).getD true then none else pure ()
  let strong : Bool := match objects with
    | [object] => (m.nodes[object]?.map (·.unique)).getD false
    | _ => false
  let payload := { payload with refs := normalize payload.refs }
  let mut m : Memory := m
  for object in objects do
    let old ← cell? m object
    let next := if strong then payload else joinPayload old payload
    m := { m with cells := m.cells.insert object next
                  fields := m.fields.insert (object, 0) next.refs
                  fieldPayloads := m.fieldPayloads.insert (object, 0) next }
  return m

/-- Reachability uses an adjacency index and a work list rather than
    rescanning the complete heap at each edge of a long frame chain. -/
private def reachable (m : Memory) (roots : Refs) : Refs := Id.run do
  if roots.any (· ≤ 1) then return m.nodes.toList.map (·.1)
  let edges := m.fields.fold (fun out (object, _) refs =>
    out.insert object (joinRefs (out[object]?.getD []) refs)) ({} : Std.HashMap Nat Refs)
  let mut seen : Std.HashMap Nat Unit := {}
  let mut pending := roots
  while let object :: tail := pending do
    pending := tail
    if object ≤ 1 then return m.nodes.toList.map (·.1)
    if seen.contains object then continue
    seen := seen.insert object ()
    pending := (edges[object]?.getD []) ++ pending
  return seen.toList.map (·.1)

/-- Actual call replay also follows private identities hidden in tuples,
    arrays or heap frames. Unknown/caller roots may reach any tracked cell;
    an empty private heap leaves activation to the callee capability check. -/
def mayReachPrivate (m : Memory) (roots : Refs) : Bool :=
  if roots.isEmpty then false
  else if roots.any (fun object => m.cells.contains object ||
      (m.nodes[object]?.map (·.privateCell)).getD false) then true
  else if m.cells.isEmpty then false
  else (reachable m roots).any fun object => m.cells.contains object ||
      (m.nodes[object]?.map (·.privateCell)).getD false

/-- Unknown or mixed references need a conservative payload fallback when
    they may denote a private cell. This grants no write permission. -/
def mayPrivate (m : Memory) (objects : Refs) : Bool :=
  objects.any fun object => object ≤ 1 ||
    m.cells.contains object || (m.nodes[object]?.map (·.privateCell)).getD false

/-- Escape prevents future private writes without erasing known payloads.
    Transport through compiler-owned containers is not itself an escape. -/
def markEscaped (m : Memory) (roots : Refs) : Memory := Id.run do
  let mut m : Memory := m
  for object in reachable m roots do
    if let some node := m.nodes[object]? then
      m := { m with nodes := m.nodes.insert object { node with escaped := true } }
  return m

/-- An unmodeled writer can change each reachable payload to unknown data. -/
def widen (m : Memory) (roots : Refs) : Memory := Id.run do
  let objects := reachable m roots
  let mut m := markEscaped m roots
  let affected : Std.HashMap Nat Unit := objects.foldl (fun out object => out.insert object ()) {}
  m := { m with
    fields := m.fields.map (fun (object, _) refs =>
      if affected.contains object then joinRefs refs [0] else refs)
    fieldPayloads := m.fieldPayloads.filter fun (object, _) _ => !affected.contains object }
  for object in objects do
    if m.cells.contains object then
      let refs := joinRefs (m.cells[object]?.getD {}).refs [0]
      m := { m with cells := m.cells.insert object { role := true, refs }
                    fields := m.fields.insert (object, 0) refs }
  return m

/-- Update possible private targets only AFTER the caller's ordinary heap
    write policy has admitted the value. Unlike writeCell, this grants no
    metadata permission and never performs a strong overwrite. -/
def writeKnownCells (m : Memory) (objects : Refs) (value : Payload) : Memory := Id.run do
  let targets := if objects.any (· ≤ 1) then m.cells.toList.map (·.1) else normalize objects
  let mut m : Memory := m
  for object in targets do
    if let some old := m.cells[object]? then
      let payload := joinPayload old value
      m := { m with cells := m.cells.insert object payload
                    fields := m.fields.insert (object, 0) payload.refs
                    fieldPayloads := m.fieldPayloads.insert (object, 0) payload
                    nodes := m.nodes.modify object fun node => { node with escaped := true } }
  return m

/-- Transfer references after an ordinary object write has been admitted.
    This grants no private payload permission. Unknown or escaped
    destinations make stored references available to unknown consumers. -/
def storeRefs (m : Memory) (objects : Refs) (field : Nat) (value : Refs) : Memory := Id.run do
  let unknown := objects.any fun object => object ≤ 1 ||
    (m.nodes[object]?.map (·.escaped)).getD true
  let privateObjects := objects.filter fun object =>
    (m.nodes[object]?.map (·.privateCell)).getD false
  let m := if unknown then markEscaped m (0 :: value) else markEscaped m privateObjects
  let strong : Bool := match objects with
    | [object] => (m.nodes[object]?.map fun n => n.unique && !n.escaped).getD false
    | _ => false
  let mut m := writeKnownCells m objects { refs := value }
  m := { m with fieldPayloads := if unknown then
      m.fieldPayloads.filter (fun (_, k) _ => k != field)
    else objects.foldl (fun facts object => facts.erase (object, field)) m.fieldPayloads }
  for object in normalize objects do
    let fields := if strong then m.fields.insert (object, field) (normalize value)
      else joinField m.fields (object, field) value
    m := { m with fields }
  return m

/-- Preserve a compiler transport field AFTER the ordinary write policy
    admits its payload. No private-cell or unknown-object permission is
    introduced here. Uncertain identities receive only weak updates. -/
def storeFieldPayload (m : Memory) (objects : Refs) (field : Nat)
    (value : Payload) : Memory := Id.run do
  let objects := normalize objects
  let qualified := !objects.isEmpty && objects.all fun object =>
    object > 1 && (m.nodes[object]?.map fun n => !n.escaped && !n.privateCell).getD false
  if !qualified then return storeRefs m objects field value.refs
  let strong : Bool := match objects with
    | [object] => (m.nodes[object]?.map (·.unique)).getD false
    | _ => false
  let value := { value with refs := normalize value.refs }
  let mut m : Memory := m
  for object in objects do
    let previous := m.fieldPayloads[(object, field)]?.getD
      { role := true, refs := joinRefs (loadRefs m [object] field) [0] }
    let next := if strong then value else joinPayload previous value
    m := { m with fields := m.fields.insert (object, field) next.refs
                  fieldPayloads := m.fieldPayloads.insert (object, field) next }
  return m

end OpenVerse.Front.MetadataCells
