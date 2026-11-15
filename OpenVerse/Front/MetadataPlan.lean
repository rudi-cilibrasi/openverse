/- Control positions for compiler-only provenance analysis across waits. -/
import OpenVerse.Core.Syntax

namespace OpenVerse.Front.MetadataPlan
open OpenVerse

inductive Kind where
  | branch | sync | race | rush
  deriving BEq, Inhabited

inductive Node where
  | jump (next : Nat)
  | atom (e : Expr) (dst next : Nat) (permission : Option (Nat × Nat))
  | test (condition : Expr) (yes no : Nat)
  | call (fn : Nat) (args : List Nat) (original : List Expr) (dst next : Nat)
  | fork (group : Nat)
  | advance (group : Nat)
  | finish (value : Nat)
  | ret (value : Nat)
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
  deriving Inhabited

structure Plan where
  nodes : Array Node := #[]
  groups : Array Group := #[]
  cleanups : Array Expr := #[]
  slots : Nat := 0
  actors : Nat := 1
  scopes : Nat := 0
  entry : Nat := 0
  deriving Inhabited

private abbrev B := StateM Plan

private def node (n : Node) : B Nat := do
  let i := (← get).nodes.size
  modify fun p => { p with nodes := p.nodes.push n }
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

mutual
private partial def lower (fns : Array Fn) (permissions : List (Nat × Nat))
    (actor dst next : Nat) (breakTo : Option Nat) : Expr → B Nat
  | .seq (.ite (.prim .fail []) cleanup (.lit .void)) body => do
    let i := (← get).cleanups.size
    modify fun p => { p with cleanups := p.cleanups.push cleanup }
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
    node (.test c yes no)
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
        let definition : Group := { kind, owner := actor, children, advance, dst, next }
        modify fun p => { p with groups := p.groups.set! group definition }
        return ← node (.fork group)
    if name == "$spawnMark" then
      -- Its arguments run now; its callee has a separate frame and result.
      return ← node (.atom (.call g es) dst next none)
    operands fns permissions actor breakTo es fun args =>
      node (.call g args es dst next)
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
    let filter ← node (.test filter body back)
    let item ← node (.atom (.assign i (.local sourceSlot)) value filter none)
    modify fun p => { p with nodes := p.nodes.set! head (.choose item exit) }
    let start ← node (.enterLoop s head)
    let start ← node (.atom (.lit .void) result start none)
    lower fns permissions actor sourceSlot start breakTo source
  | .brk => node (.jump (breakTo.getD next))
  | .ret e => do
    let value ← slot
    let stop ← node (.ret value)
    lower fns permissions actor value stop breakTo e
  | .print e => do
    let value ← slot
    let after ← node (.atom (.print (.local value)) dst next none)
    lower fns permissions actor value after breakTo e
  | e => node (.atom e dst next none)

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
    (body : Expr) : Plan := Id.run do
  let action : B Unit := do
    let result ← slot
    let done ← node (.finish result)
    let entry ← lower fns permissions 0 result done none body
    modify fun p => { p with entry }
  return (action.run { slots := nslots }).2

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
