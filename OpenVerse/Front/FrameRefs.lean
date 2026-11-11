/- Shared source-frame accesses used by lifted refining branches. -/
import OpenVerse.Core.TypeCheck

namespace OpenVerse.Front.FrameRefs
open OpenVerse

/-- Source identity survives discovery elaborations, whose temporary slots
    need not agree with the final generated function's slots. -/
structure Origin where
  frame : String
  name : String
  args : List VTy
  deriving Inhabited

/-- A local alias of a field in an ancestor frame. `frame` is an immutable
    frame-reference parameter, or the current resume function's frame. -/
structure Slot where
  localSlot : Nat
  frame : Nat
  field : Nat
  deriving Inhabited

/-- A synthetic refining-cast copy-out. Its RHS is a saved result or one
    field of that result; ordinary assignments are not copy-outs. -/
structure CopyOut where
  target : Nat
  result : Nat
  field : Option Nat := none
  deriving Inhabited

/-- Storage information collected from one final function elaboration. -/
structure Info where
  /-- Frame-reference arguments precede the hidden type witnesses. -/
  explicit : Nat := 0
  slots : List (Nat × Origin) := []
  copies : List CopyOut := []
  deriving Inhabited

/-- Private pre-lowering placeholder: a source call passes its own frame,
    which only exists as local 0 after the suspension pass shifts slots. -/
def currentSlot : Nat := 1000000017
def current : Expr := .heap (.get currentSlot) []

partial def resolveCurrent : Expr → Expr
  | .heap (.get 1000000017) [] => .local 0
  | .assign i e => .assign i (resolveCurrent e)
  | .seq a b => .seq (resolveCurrent a) (resolveCurrent b)
  | .prim p es => .prim p (es.map resolveCurrent)
  | .heap p es => .heap p (es.map resolveCurrent)
  | .call f es => .call f (es.map resolveCurrent)
  | .ite c t e => .ite (resolveCurrent c) (resolveCurrent t) (resolveCurrent e)
  | .forE i it f b => .forE i (resolveCurrent it) (resolveCurrent f) (resolveCurrent b)
  | .loop e => .loop (resolveCurrent e)
  | .ret e => .ret (resolveCurrent e)
  | .print e => .print (resolveCurrent e)
  | e => e

def CopyOut.matches (copy : CopyOut) (target : Nat) (rhs : Expr) : Bool :=
  copy.target == target && match copy.field, rhs with
    | none, .local r => copy.result == r
    | some k, .prim (.tupGet j) [.local r] => k == j && copy.result == r
    | _, _ => false

structure Rewritten where
  body : Expr
  slots : Array VTy

private structure St where
  slots : Array VTy

private abbrev M := StateT St (Except String)

private def snapshot (slot : Nat) : M Nat := do
  let st ← get
  let some ty := st.slots[slot]? | throw "source-frame alias has no slot type"
  let n := st.slots.size
  set { st with slots := st.slots.push ty }
  return n

/-- Redirect mutable aliases to their source storage before suspension ANF.
    Writes inside conditions go directly to the heap and participate in the
    condition's transaction; no stale local overlay is kept until success.

    A canonical refining call snapshots its receiver so that the Core
    checker's dispatch rule still sees a local. The snapshot has an ordinary
    slot's lifetime: a later argument can suspend, so the suspension lowering
    must preserve it and its existing `fixRefined` pass handles field access.
    Other arguments read live storage in their original order. Only recorded synthetic copy-outs may
    be omitted; return operands and user copies remain ordinary snapshots.

    For binders cannot alias borrowed storage. Source generator bindings are
    immutable and are not entered in `aliases` by the caller. -/
def rewrite (slots : Array VTy) (aliases : List Slot) (copies : List CopyOut)
    (body : Expr) : Except String Rewritten := do
  let alias (i : Nat) := aliases.find? (·.localSlot == i)
  let read (s : Slot) : Expr := .heap (.get s.field) [.local s.frame]
  let rec go (e : Expr) : M Expr := do
    match e with
    | .local i => return (alias i |>.map read).getD e
    | .assign i rhs =>
      match alias i with
      | none => return .assign i (← go rhs)
      | some s =>
        if copies.any (·.matches i rhs) then return .lit .void
        -- Heap.set returns its operand, just as local assignment does.
        return .heap (.set s.field) [.local s.frame, ← go rhs]
    | .ite (.heap (.isTag us) [.local y]) (.call f (.local y' :: es)) els =>
      if y == y' then
        if let some s := alias y then
          let z ← snapshot y
          return .seq (.assign z (read s))
            (.ite (.heap (.isTag us) [.local z]) (.call f (.local z :: (← es.mapM go))) (← go els))
      return .ite (← go (.heap (.isTag us) [.local y])) (← go (.call f (.local y' :: es))) (← go els)
    | .seq a b => return .seq (← go a) (← go b)
    | .prim op es => return .prim op (← es.mapM go)
    | .heap op es => return .heap op (← es.mapM go)
    | .call f es => return .call f (← es.mapM go)
    | .ite c t f => return .ite (← go c) (← go t) (← go f)
    | .forE i it f b =>
      if (alias i).isSome then throw "a for binder cannot alias source-frame storage"
      return .forE i (← go it) (← go f) (← go b)
    | .loop b => return .loop (← go b)
    | .ret v => return .ret (← go v)
    | .print v => return .print (← go v)
    | e => return e
  let (body, st) ← (go body).run { slots }
  return { body, slots := st.slots }

end OpenVerse.Front.FrameRefs
