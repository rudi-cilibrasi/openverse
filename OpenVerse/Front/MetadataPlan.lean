/- Control positions for compiler-only provenance analysis across waits. -/
import OpenVerse.Core.Syntax

namespace OpenVerse.Front.MetadataPlan
open OpenVerse

inductive Kind where
  | branch | spawn | sync | race | rush
  deriving BEq, Inhabited

inductive Node where
  | jump (next : Nat)
  | atom (e : Expr) (dst next : Nat) (permission : Option (Nat × Nat))
  | test (condition : Expr) (yes no : Nat)
  | beginTest (no next : Nat)
  | passTest (next : Nat)
  | enterCall (fn offset : Nat) (args : List Nat) (next : Nat)
  | leaveCall (dst next : Nat)
  | cleanupDone
  | drained
  | spawnCheck (fn : Nat) (args : List Nat) (group : Nat)
  | finishTask (value : Nat)
  | call (fn : Nat) (args : List Nat) (original : List Expr) (dst next : Nat)
  | fork (group : Nat)
  | advance (group : Nat)
  | finish (value : Nat)
  | ret (value : Nat)
  | functionReturn (owner value dst next fn offset : Nat)
  | pushCleanup (cleanup next : Nat)
  | popCleanup (next : Nat)
  | enterLoop (scope next : Nat)
  | backLoop (scope next : Nat)
  | leaveLoop (scope next : Nat)
  | choose (yes no : Nat)
  | accumulate (dst value next : Nat)
  deriving Inhabited

structure Group where
  kind : Kind := .branch
  owner : Nat := 0
  children : Array (Nat × Nat) := #[]
  advance : Nat := 0
  dst : Nat := 0
  next : Nat := 0
  context : Option (Nat × Nat) := none
  task : Option Nat := none
  target : Option Nat := none
  arguments : List Nat := []
  deriving Inhabited

structure Plan where
  nodes : Array Node := #[]
  contexts : Array (Option (Nat × Nat)) := #[]
  groups : Array Group := #[]
  cleanups : Array Expr := #[]
  cleanupEntries : Array Nat := #[]
  inlineFns : Array Bool := #[]
  signalFns : Array Bool := #[]
  context : Option (Nat × Nat) := none
  permissions : Array (List (Nat × Nat)) := #[]
  callStack : List Nat := []
  returnTo : Option (Nat × Nat × Nat) := none
  slots : Nat := 0
  actors : Nat := 1
  scopes : Nat := 0
  entry : Nat := 0
  drain : Nat := 0
  deriving Inhabited

private abbrev B := StateM Plan

private def node (n : Node) : B Nat := do
  let i := (← get).nodes.size
  modify fun p => { p with nodes := p.nodes.push n, contexts := p.contexts.push p.context }
  return i

private def slot : B Nat := do
  let i := (← get).slots
  modify fun p => { p with slots := i + 1 }
  return i

private def scope : B Nat := do
  let i := (← get).scopes
  modify fun p => { p with scopes := i + 1 }
  return i

private def argument (original : Expr) (temporary : Nat) : Expr :=
  match original with
  | .lit v => .lit v
  | _ => .local temporary

private partial def shift (offset : Nat) : Expr → Expr
  | .local i => .local (i + offset)
  | .assign i e => .assign (i + offset) (shift offset e)
  | .seq a b => .seq (shift offset a) (shift offset b)
  | .ite c t e => .ite (shift offset c) (shift offset t) (shift offset e)
  | .prim op es => .prim op (es.map (shift offset))
  | .heap op es => .heap op (es.map (shift offset))
  | .call g es => .call g (es.map (shift offset))
  | .loop e => .loop (shift offset e)
  | .forE i a f b => .forE (i + offset) (shift offset a) (shift offset f) (shift offset b)
  | .ret e => .ret (shift offset e)
  | .print e => .print (shift offset e)
  | e => e

private partial def callees : Expr → List Nat
  | .call g es => g :: es.flatMap callees
  | .assign _ e | .loop e | .ret e | .print e => callees e
  | .seq a b => callees a ++ callees b
  | .ite c t e => callees c ++ callees t ++ callees e
  | .prim _ es | .heap _ es => es.flatMap callees
  | .forE _ a f b => callees a ++ callees f ++ callees b
  | _ => []

/-- Prelude types move under `$` when a user declaration shadows them. -/
def isEventSignal (fns : Array Fn) (g : Nat) : Bool :=
  let name := (fns[g]?.map (·.name)).getD ""
  ["$event.Signal", "$sticky_event.Signal"].contains name ||
    (name == "event.Signal" && !fns.any (·.name == "$event.Signal")) ||
    (name == "sticky_event.Signal" && !fns.any (·.name == "$sticky_event.Signal"))

private def effects (fns : Array Fn) (signalsOnly : Bool := false) : Array Bool := Id.run do
  let mut result := fns.map fun f =>
    if signalsOnly then f.name == "$signalAll" else
      ["$Sleep", "$WaitDone", "$EvAwait", "$StickyAwait", "$Await", "$cancelMark", "$signalAll"].contains f.name
  let mut grew := true
  while grew do
    grew := false
    for i in [:fns.size] do
      if !result[i]! && (callees fns[i]!.body).any (fun g => result[g]?.getD false) then
        result := result.set! i true
        grew := true
  return result

mutual
private partial def lower (fns : Array Fn) (permissions : List (Nat × Nat))
    (actor dst next : Nat) (breakTo : Option Nat) : Expr → B Nat
  | .seq (.ite (.prim .fail []) cleanup (.lit .void)) body => do
    let i := (← get).cleanups.size
    modify fun p => { p with
      cleanups := p.cleanups.push cleanup
      cleanupEntries := p.cleanupEntries.push 0 }
    let finish ← node .cleanupDone
    let start ← lower fns permissions actor (← slot) finish none cleanup
    modify fun p => { p with cleanupEntries := p.cleanupEntries.set! i start }
    let after ← node (.popCleanup next)
    let body ← lower fns permissions actor dst after breakTo body
    node (.pushCleanup i body)
  | .seq a b => do
    let b ← lower fns permissions actor dst next breakTo b
    lower fns permissions actor (← slot) b breakTo a
  | .assign i e => do
    let value ← slot
    let after ← node (.atom (.assign i (.local value)) dst next none)
    lower fns permissions actor value after breakTo e
  | .ite c t e => do
    let yes ← lower fns permissions actor dst next breakTo t
    let no ← lower fns permissions actor dst next breakTo e
    let pass ← node (.passTest yes)
    let condition ← lower fns permissions actor (← slot) pass breakTo c
    node (.beginTest no condition)
  | .call g es => do
    let name := (fns[g]?.map (·.name)).getD ""
    if let [.prim .mkArr arms] := es then
      if ["$branchMark", "$syncMark", "$raceMark", "$rushMark"].contains name then
        let kind := if name == "$branchMark" then Kind.branch
          else if name == "$syncMark" then .sync
          else if name == "$raceMark" then .race else .rush
        let group := (← get).groups.size
        modify fun p => { p with groups := p.groups.push {} }
        let advance ← node (.advance group)
        let mut children := #[]
        for arm in arms do
          let child := (← get).actors
          modify fun p => { p with actors := child + 1 }
          let value ← slot
          let done ← node (.finish value)
          let start ← lower fns permissions child value done none arm
          children := children.push (child, start)
        let definition : Group := {
          kind, owner := actor, children, advance, dst, next
          context := (← get).context }
        modify fun p => { p with groups := p.groups.set! group definition }
        return ← node (.fork group)
    if name == "$spawnMark" then
      if let [.prim .mkArr [.seq target _, .seq (.local task) _]] := es then
        return ← spawn fns permissions actor dst next task target
      return ← node (.atom (.call g es) dst next none)
    operands fns permissions actor breakTo es fun args => do
      let p ← get
      let leaf := ["$Sleep", "$WaitDone", "$EvAwait", "$StickyAwait", "$Await", "$cancelMark", "$signalAll"].contains name ||
        isEventSignal fns g
      if p.inlineFns[g]?.getD false && !leaf && !p.callStack.contains g then
        let callee := fns[g]!
        let offset := p.slots
        let savedStack := p.callStack
        let savedReturn := p.returnTo
        let savedContext := p.context
        let leave ← node (.leaveCall dst next)
        modify fun p => { p with
          slots := offset + callee.nslots
          callStack := g :: savedStack, returnTo := some (actor, dst, leave)
          context := some (g, offset) }
        let own := (p.permissions[g]?.getD []).map fun (i, k) => (i + offset, k)
        let entry ← lower fns own actor dst leave none (shift offset callee.body)
        modify fun p => { p with callStack := savedStack, returnTo := savedReturn, context := savedContext }
        node (.enterCall g offset args entry)
      else node (.call g args es dst next)
  | .prim op es => operands fns permissions actor breakTo es fun args =>
    node (.atom (.prim op (es.zipWith argument args)) dst next none)
  | .heap op es => operands fns permissions actor breakTo es fun args => do
    let permission := match op, es, args with
      | .set k, .local obj :: _, tmp :: _ =>
        if permissions.contains (obj, k) then some (tmp, k) else none
      | _, _, _ => none
    node (.atom (.heap op (es.zipWith argument args)) dst next permission)
  | .loop body => do
    let s ← scope
    let exit ← node (.leaveLoop s next)
    let exit ← node (.atom (.lit .void) dst exit none)
    let back ← node (.jump 0)
    let body ← lower fns permissions actor (← slot) back (some exit) body
    modify fun p => { p with nodes := p.nodes.set! back (.backLoop s body) }
    node (.enterLoop s body)
  | .forE i source filter body => do
    let sourceSlot ← slot
    let result ← slot
    let value ← slot
    let s ← scope
    let exit ← node (.leaveLoop s next)
    let exit ← node (.atom (.local result) dst exit none)
    let head ← node (.jump 0)
    let back ← node (.backLoop s head)
    let add ← node (.accumulate result value back)
    let body ← lower fns permissions actor value add breakTo body
    let pass ← node (.passTest body)
    let filter ← lower fns permissions actor (← slot) pass breakTo filter
    let filter ← node (.beginTest back filter)
    let item ← node (.atom (.assign i (.local sourceSlot)) value filter none)
    modify fun p => { p with nodes := p.nodes.set! head (.choose item exit) }
    let start ← node (.enterLoop s head)
    let start ← node (.atom (.lit .void) result start none)
    lower fns permissions actor sourceSlot start breakTo source
  | .brk => node (.jump (breakTo.getD next))
  | .ret e => do
    if let some (owner, dst, next) := (← get).returnTo then
      let value ← slot
      let (fn, offset) := (← get).context.getD (0, 0)
      let finish ← node (.functionReturn owner value dst next fn offset)
      return ← lower fns permissions actor value finish breakTo e
    let value ← slot
    let stop ← node (.ret value)
    lower fns permissions actor value stop breakTo e
  | .print e => do
    let value ← slot
    let after ← node (.atom (.print (.local value)) dst next none)
    lower fns permissions actor value after breakTo e
  | e => node (.atom e dst next none)

private partial def spawn (fns : Array Fn) (permissions : List (Nat × Nat))
    (actor dst next task : Nat) : Expr → B Nat
  | .call g es => operands fns permissions actor none es fun args => do
    let group := (← get).groups.size
    let child := (← get).actors
    modify fun p => { p with actors := child + 1, groups := p.groups.push {} }
    let advance ← node (.advance group)
    let value ← slot
    let done ← node (.finishTask value)
    let entry ← lower fns permissions child value done none (.call g (args.map Expr.local))
    let definition : Group := {
      kind := .spawn, owner := actor, children := #[(child, entry)]
      advance, dst, next, task := some task, context := (← get).context
      target := some g, arguments := args }
    modify fun p => { p with groups := p.groups.set! group definition }
    let fork ← node (.fork group)
    node (.spawnCheck g args fork)
  | .seq a b => do
    let b ← spawn fns permissions actor dst next task b
    lower fns permissions actor (← slot) b none a
  | .ite c t e => do
    let yes ← spawn fns permissions actor dst next task t
    let no ← spawn fns permissions actor dst next task e
    let pass ← node (.passTest yes)
    let condition ← lower fns permissions actor (← slot) pass none c
    node (.beginTest no condition)
  | .assign _ e => spawn fns permissions actor dst next task e
  | e => lower fns permissions actor dst next none e

private partial def operands (fns : Array Fn) (permissions : List (Nat × Nat))
    (actor : Nat) (breakTo : Option Nat) (es : List Expr)
    (finish : List Nat → B Nat) : B Nat := do
  let slots ← es.mapM fun _ => slot
  let mut next ← finish slots
  for (e, dst) in (es.zip slots).reverse do
    next ← lower fns permissions actor dst next breakTo e
  return next
end

def build (fns : Array Fn) (permissions : List (Nat × Nat)) (nslots : Nat)
    (body : Expr) (root : Option Nat := none)
    (allPermissions : Array (List (Nat × Nat)) := #[]) : Plan := Id.run do
  let action : B Unit := do
    let drain ← node .drained
    modify fun p => { p with drain }
    let result ← slot
    let done ← node (.finish result)
    let entry ← lower fns permissions 0 result done none body
    modify fun p => { p with entry }
  return (action.run {
    slots := nslots, inlineFns := effects fns, signalFns := effects fns true
    permissions := allPermissions, callStack := root.toList }).2

partial def reads : Expr → List Nat
  | .local i => [i]
  | .lit _ | .brk => []
  | .assign _ e | .loop e | .ret e | .print e => reads e
  | .seq a b => reads a ++ reads b
  | .prim _ es | .heap _ es | .call _ es => es.flatMap reads
  | .ite c t e => reads c ++ reads t ++ reads e
  | .forE _ a f b => reads a ++ reads f ++ reads b

partial def calls : Expr → List Nat
  | .call g es => g :: es.flatMap calls
  | .lit _ | .local _ | .brk => []
  | .assign _ e | .loop e | .ret e | .print e => calls e
  | .seq a b => calls a ++ calls b
  | .prim _ es | .heap _ es => es.flatMap calls
  | .ite c t e => calls c ++ calls t ++ calls e
  | .forE _ a f b => calls a ++ calls f ++ calls b

partial def assigns : Expr → List Nat
  | .assign i e => i :: assigns e
  | .lit _ | .local _ | .brk => []
  | .loop e | .ret e | .print e => assigns e
  | .seq a b => assigns a ++ assigns b
  | .prim _ es | .heap _ es | .call _ es => es.flatMap assigns
  | .ite c t e => assigns c ++ assigns t ++ assigns e
  | .forE i a f b => i :: assigns a ++ assigns f ++ assigns b

/-- Escaping work and cancellation registrations in this frame. -/
partial def sites (fns : Array Fn) : Expr → Bool × List Expr
  | .seq (.ite (.prim .fail []) d (.lit .void)) b =>
    let (background, cleanups) := sites fns b
    (background, d :: cleanups)
  | e => Id.run do
    let children := match e with
      | .assign _ e | .loop e | .ret e | .print e => [e]
      | .seq a b => [a, b]
      | .prim _ es | .heap _ es | .call _ es => es
      | .ite c t e => [c, t, e]
      | .forE _ a f b => [a, f, b]
      | _ => []
    let own := match e with
      | .call g _ => (fns[g]?.map (·.name)).any fun n =>
        n == "$branchMark" || n == "$rushMark"
      | _ => false
    return children.foldl (fun (background, cleanups) e =>
      let (b, ds) := sites fns e
      (background || b, cleanups ++ ds)) (own, [])

end OpenVerse.Front.MetadataPlan
