/- Abstract object identities used by the compiler's provenance scheduler. -/
import OpenVerse.Core.Syntax
import Std.Data.HashMap

namespace OpenVerse.Front.MetadataReferences
open OpenVerse

/-- 0 may denote any object; 1 denotes an object supplied by the caller.
    Allocation sites have identities above 1. Repeated allocations at one
    site are joined, so these are may-alias identities, not runtime tags. -/
abbrev Refs := List Nat

private def union (a b : Refs) : Refs := (a ++ b).mergeSort (· ≤ ·) |>.eraseDups

structure Memory where
  slots : Array Refs := #[]
  fields : Std.HashMap (Nat × Nat) Refs := {}
  uncertain : Refs := []
  deriving BEq, Inhabited

def join (a b : Memory) : Memory := {
  slots := a.slots.zipWith union b.slots
  fields := b.fields.fold (fun m k v => m.insert k (union (m[k]?.getD []) v)) a.fields
  uncertain := union a.uncertain b.uncertain }

def set (m : Memory) (slot : Nat) (value : Refs) : Memory :=
  { m with slots := m.slots.set! slot value }

/-- Summarized workers may mutate any heap field, but cannot replace the
    caller's local reference bindings. -/
def widenFields (m : Memory) : Memory :=
  { m with fields := m.fields.map fun _ value => union value [0] }

def aliases (a b : Refs) : Bool :=
  !a.isEmpty && !b.isEmpty && (a.contains 0 || b.contains 0 || a.any b.contains ||
    (a.any (· < 4294967296) && b.any (· < 4294967296)))

def definitelyAliases (m : Memory) (a b : Refs) : Bool :=
  match a, b with
  | [x], [y] => x == y && x > 1 && !m.uncertain.contains x
  | _, _ => false

private def child (site index : Nat) : Nat :=
  (site * 16777619 + index + 1) % 4294967296

private def allocation (site : Nat) : Nat := site + 4294967296

private def store (m : Memory) (objects : Refs) (field : Nat) (value : Refs) : Memory := Id.run do
  let fields := m.fields.fold (fun h (object, k) old =>
    if k == field && aliases objects [object] then h.insert (object, k) (union old value)
    else h) m.fields
  return { m with fields := objects.foldl (fun h object =>
    h.insert (object, field) (union (h[(object, field)]?.getD []) value)) fields }

private def load (m : Memory) (objects : Refs) (field : Nat) : Refs :=
  objects.foldl (fun r object => union r
    (if object < 4294967296 then m.fields.fold (fun values (o, k) v =>
        if k == field && aliases [object] [o] then union values v else values)
        [if object == 0 then 0 else 1]
      else m.fields[(object, field)]?.getD [0])) []

private def elements (m : Memory) (objects : Refs) : Refs :=
  objects.foldl (fun r object =>
    if object < 4294967296 then union r [if object == 0 then 0 else 1]
    else m.fields.fold (fun r (o, _) v => if o == object then union r v else r) r) []

private def make (m : Memory) (site : Nat) (values : List Refs) : Refs × Memory := Id.run do
  let object := allocation site
  let repeated := m.fields.toList.any fun ((o, _), _) => o == object
  let mut m := if repeated then { m with uncertain := union m.uncertain [object] } else m
  for (value, i) in values.zipIdx do m := store m [object] i value
  return ([object], m)

private structure Flow where
  memory : Memory
  value : Option Refs := some []
  returned : Option Refs := none
  broken : Option Memory := none
  deriving Inhabited

private def joinValue (a b : Option Refs) : Option Refs :=
  match a, b with
  | some a, some b => some (union a b)
  | some a, none | none, some a => some a
  | none, none => none

private def joinMemory (a b : Option Memory) : Option Memory :=
  match a, b with
  | some a, some b => some (join a b)
  | some a, none | none, some a => some a
  | none, none => none

private def exits (a b : Flow) : Flow := { b with
  returned := joinValue a.returned b.returned
  broken := joinMemory a.broken b.broken }

mutual
private partial def expr (fns : Array Fn) (stack : List Nat) (site : Nat)
    (memory : Memory) : Expr → Flow
  | .lit _ => { memory }
  | .local i => { memory, value := some (memory.slots[i]?.getD [0]) }
  | .assign i e =>
    let out := expr fns stack (child site 0) memory e
    { out with memory := out.value.map (set out.memory i) |>.getD out.memory }
  | .seq a b =>
    let out := expr fns stack (child site 0) memory a
    if out.value.isNone then out
    else exits out (expr fns stack (child site 1) out.memory b)
  | .call g es =>
    let (args, out) := operands fns stack site memory es
    if out.value.isNone then out
    else
      let (value, memory) := invoke fns stack (child site g) out.memory g args
      { out with memory, value := some value }
  | .heap op es => Id.run do
    let (args, out) := operands fns stack site memory es
    if out.value.isNone then return out
    let (value, memory) := match op with
      | .new _ => make out.memory site args
      | .get k => (load out.memory (args.headD [0]) k, out.memory)
      | .isTag _ => (args.headD [0], out.memory)
      | .set k =>
        let value := args[1]?.getD [0]
        (value, store out.memory (args.headD [0]) k value)
      | .tag => ([], out.memory)
    return { out with memory, value := some value }
  | .prim op es => Id.run do
    let (args, out) := operands fns stack site memory es
    if out.value.isNone then return out
    let (value, memory) := match op with
      | .mkArr | .mkTup => make out.memory site args
      | .mkSome | .query => (args.headD [], out.memory)
      | .tupGet k => (load out.memory (args.headD [0]) k, out.memory)
      | .index =>
        let value := match (es[1]? : Option Expr) with
          | some (.lit (.int i)) => if i ≥ 0 then load out.memory (args.headD [0]) i.toNat else []
          | _ => elements out.memory (args.headD [0])
        (value, out.memory)
      | .arrSet =>
        let value := union (elements out.memory (args.headD [0])) (args[2]?.getD [0])
        make out.memory site [value]
      | .concat =>
        make out.memory site [args.foldl (fun r a => union r (elements out.memory a)) []]
      | .flatten =>
        -- The outer array stores row identities, not the flattened values.
        let rows := args.foldl (fun r a => union r (elements out.memory a)) []
        make out.memory site [elements out.memory rows]
      | _ => ([], out.memory)
    let value := match op, es with
      | .fail, _ | .userErr, _ | .query, [.lit (.logic false)] | .query, [.lit .none] => none
      | _, _ => some value
    return { out with memory, value }
  | .ite c t e =>
    let condition := expr fns stack (child site 0) memory c
    let yes := if condition.value.isSome then expr fns stack (child site 1) condition.memory t
      else { memory := condition.memory, value := none }
    let no := expr fns stack (child site 2) memory e
    let memory := match yes.value, no.value with
      | some _, some _ => join yes.memory no.memory
      | some _, none => yes.memory
      | _, _ => no.memory
    exits condition {
      memory, value := joinValue yes.value no.value
      returned := joinValue yes.returned no.returned, broken := joinMemory yes.broken no.broken }
  | .loop body => Id.run do
    let mut head := memory
    let mut returned := none
    let mut broken := none
    repeat
      let out := expr fns stack (child site 0) head body
      returned := joinValue returned out.returned
      broken := joinMemory broken out.broken
      let next := if out.value.isSome then join head out.memory else head
      if next == head then break
      head := next
    return { memory := broken.getD head, value := broken.map (fun _ => []), returned }
  | .forE i source filter body => Id.run do
    let source := expr fns stack (child site 0) memory source
    if source.value.isNone then return source
    let item := elements source.memory (source.value.getD [0])
    let mut head := source.memory
    let mut value := []
    let mut out := source
    repeat
      let filter := expr fns stack (child site 1) (set head i item) filter
      let body := if filter.value.isSome then expr fns stack (child site 2) filter.memory body
        else { memory := head, value := none }
      out := exits filter (exits body out)
      value := union value (body.value.getD [])
      let next := if body.value.isSome then join head body.memory else head
      if next == head then break
      head := next
    let (result, memory) := make head site [value]
    return { out with memory, value := some result }
  | .brk => { memory, value := none, broken := some memory }
  | .ret e =>
    let out := expr fns stack (child site 0) memory e
    { out with returned := joinValue out.returned out.value, value := none }
  | .print e =>
    let out := expr fns stack (child site 0) memory e
    { out with value := out.value.map (fun _ => []) }

private partial def operands (fns : Array Fn) (stack : List Nat) (site : Nat)
    (memory : Memory) (es : List Expr) : List Refs × Flow := Id.run do
  let mut out : Flow := { memory }
  let mut args := []
  for (e, i) in es.zipIdx do
    if out.value.isSome then
      out := exits out (expr fns stack (child site i) out.memory e)
      args := args ++ [out.value.getD []]
  return (args, out)

private partial def invoke (fns : Array Fn) (stack : List Nat) (site : Nat)
    (memory : Memory) (g : Nat) (args : List Refs) : Refs × Memory := Id.run do
  let some fn := fns[g]? | return ([0], memory)
  if ["$Sleep", "$WaitDone", "$signalAll"].contains fn.name then return ([], memory)
  if ["$EvAwait", "$StickyAwait", "$Await"].contains fn.name then return ([0], memory)
  if stack.contains g then
    -- A recursive call can return an alias and mutate reachable fields.
    -- Readonly calls cannot replace fields of existing objects. Keep those
    -- identities precise; a returned allocation is still an unknown alias.
    -- Widen writable calls rather than impose an analysis fuel limit.
    return ([0], if fn.writes then widenFields memory else memory)
  let slots := Array.ofFn (n := fn.nslots) fun i => args[i.val]?.getD []
  let out := expr fns (g :: stack) site { memory with slots } fn.body
  return ((joinValue out.value out.returned).getD [0], { memory with fields := out.memory.fields, uncertain := out.memory.uncertain })
end

private structure Dependency where
  slots : Array Refs
  value : Refs := []
  returned : Refs := []
  signals : Refs := []
  deriving Inhabited

private structure Signature where
  result : Refs := []
  signals : Refs := []
  deriving BEq, Inhabited

private partial def dependency (signatures : Array Signature)
    (state : Dependency) : Expr → Dependency
  | .local i => { state with value := state.slots[i]?.getD [] }
  | .lit _ | .brk => { state with value := [] }
  | .assign i e =>
    let out := dependency signatures state e
    { out with slots := out.slots.set! i out.value }
  | .seq a b => dependency signatures (dependency signatures state a) b
  | .ite c t e =>
    let yes := dependency signatures (dependency signatures state c) t
    let no := dependency signatures state e
    { no with
      slots := yes.slots.zipWith union no.slots
      value := union yes.value no.value, returned := union yes.returned no.returned
      signals := union yes.signals no.signals }
  | .loop body => Id.run do
    let mut out := state
    repeat
      let step := dependency signatures out body
      let next := { step with
        slots := out.slots.zipWith union step.slots
        returned := union out.returned step.returned, signals := union out.signals step.signals }
      if next.slots == out.slots && next.returned == out.returned && next.signals == out.signals then
        return { next with value := [] }
      out := next
    return out
  | .forE i source filter body =>
    let source := dependency signatures state source
    let entry := { source with slots := source.slots.set! i source.value }
    let out := dependency signatures entry (.loop (.seq filter body))
    { out with value := (dependency signatures out body).value }
  | .ret e =>
    let out := dependency signatures state e
    { out with returned := union out.returned out.value }
  | .print e => { dependency signatures state e with value := [] }
  | node => Id.run do
    let es := match node with
      | .call _ es | .heap _ es | .prim _ es => es
      | _ => []
    let mut out := state
    let mut values := []
    for e in es do
      out := dependency signatures out e
      values := values ++ [out.value]
    let all := values.foldl union []
    match node with
    | .call g _ =>
      let summary := signatures[g]?.getD {}
      let mapped (indices : Refs) := indices.foldl (fun r i => union r (values[i]?.getD [])) []
      return { out with
        value := mapped summary.result
        signals := union out.signals (mapped summary.signals) }
    | .heap .tag _ => return { out with value := [] }
    | .heap (.set _) _ => return { out with value := values[1]?.getD [] }
    | .heap _ _ => return { out with value := all }
    | .prim op _ =>
      return { out with value := if [.mkArr, .mkTup, .mkSome, .query, .index, .arrSet,
        .concat, .flatten].contains op then all else
        match op with | .tupGet _ => all | _ => [] }
    | _ => return { out with value := [] }

/-- Formal parameters whose reachable references can be signaled. The
    finite dependency lattice includes recursive argument permutations. -/
def signalArguments (fns : Array Fn) : Array Refs := Id.run do
  let mut summaries := fns.map fun f =>
    { signals := if f.name == "$signalAll" then [0] else [] : Signature }
  let mut growing := true
  while growing do
    growing := false
    for i in [:fns.size] do
      let f := fns[i]!
      let slots := Array.ofFn (n := f.nslots) fun j => if j.val < f.arity then [j.val] else []
      let out := dependency summaries { slots } f.body
      let old := summaries[i]!
      let next : Signature := {
        result := union old.result (union out.value out.returned)
        signals := union old.signals out.signals }
      if next != old then
        summaries := summaries.set! i next
        growing := true
  return summaries.map (·.signals)

/-- Include references stored inside object/array arguments of a recursive
    signaling helper. Unknown references remain unknown. -/
def reachable (memory : Memory) (roots : Refs) : Refs := Id.run do
  let mut found := roots
  repeat
    let next := memory.fields.fold (fun refs (object, _) value =>
      if aliases found [object] then union refs value else refs) found
    if next == found then return found
    found := next
  return found

/-- Preserve the element identities accumulated by a source `for`. -/
def accumulate (memory : Memory) (site dst value : Nat) : Memory :=
  let items := union (elements memory (memory.slots[dst]?.getD []))
    (memory.slots[value]?.getD [0])
  let (refs, memory) := make memory site [items]
  set memory dst refs

/-- Transfer references through one graph atom. -/
def eval (fns : Array Fn) (site : Nat) (memory : Memory) (e : Expr) : Refs × Memory :=
  let out := expr fns [] site memory e
  (out.value.getD [0], out.memory)

/-- Preserve argument aliases and fresh constructor identities through helpers. -/
def call (fns : Array Fn) (site : Nat) (memory : Memory) (g : Nat)
    (args : List Refs) : Refs × Memory := invoke fns [] site memory g args

end OpenVerse.Front.MetadataReferences
