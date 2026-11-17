/- Object aliases carried by typed immutable Core values. -/
import OpenVerse.Core.Typing

namespace OpenVerse.Front.MetadataValues
open OpenVerse

mutual
def hasObjectRef : Value → Bool
  | .ref _ => true
  | .arr values => hasObjectRefs values.toList
  | .tup values => hasObjectRefs values
  | .some value => hasObjectRef value
  | _ => false

def hasObjectRefs : List Value → Bool
  | [] => false
  | value :: rest => hasObjectRef value || hasObjectRefs rest
end

mutual
/-- A closed data type cannot contain an object alias. Opaque types and
    parameters remain unknown; reference arguments do not make a ref safe. -/
def objectFree : VTy → Bool
  | .int | .logic | .char | .float => true
  | .arr element | .opt element => objectFree element
  | .tup elements => objectFreeTypes elements
  | _ => false

def objectFreeTypes : List VTy → Bool
  | [] => true
  | ty :: rest => objectFree ty && objectFreeTypes rest
end

/-- Strict closed data references may retain ordinary heap identity, but can
    never reach a compiler-private cell or a metadata-bearing field. This is
    deliberately separate from `objectFree`, which excludes every alias. -/
private partial def dataEdges (count : Nat) : VTy → Bool × List Nat
  | .int | .logic | .char | .float => (true, [])
  | .arr ty | .opt ty => dataEdges count ty
  | .tup tys => tys.foldl (fun (safe, edges) ty =>
      let next := dataEdges count ty
      (safe && next.1, next.2 ++ edges)) (true, [])
  | .ref tags args =>
    let nested := args.foldl (fun (safe, edges) ty =>
      let next := dataEdges count ty
      (safe && next.1, next.2 ++ edges)) (true, [])
    (!tags.isEmpty && tags.all (· < count) && nested.1, tags ++ nested.2)
  | _ => (false, [])

/-- Greatest safe class graph: an ordinary reference cycle is safe unless
    some reachable class has a private tag, metadata field, or opaque field.
    Each reverse edge is visited only when its target first becomes unsafe. -/
def dataClassFlags (classes : Array (List VTy))
    (metadataFields : Array (List Nat)) (privateTags : List Nat) : Array Bool := Id.run do
  let count := classes.size
  let mut safe := Array.replicate count true
  for tag in privateTags do
    if tag < count then safe := safe.set! tag false
  let mut callers := Array.replicate count ([] : List Nat)
  for index in [:count] do
    if !(metadataFields[index]?.any List.isEmpty) then
      safe := safe.set! index false
    for ty in classes[index]! do
      let (closed, edges) := dataEdges count ty
      if !closed then safe := safe.set! index false
      for target in edges do
        if target < count then callers := callers.modify target (index :: ·)
  let mut queue := (List.range count).filter (fun index => !safe[index]!) |>.toArray
  let mut cursor := 0
  while cursor < queue.size do
    let target := queue[cursor]!
    cursor := cursor + 1
    for caller in callers[target]! do
      if safe[caller]! then
        safe := safe.set! caller false
        queue := queue.push caller
  return safe

/-- A closed type whose entire object graph has the strict data certificate.
    This does not assert that the value contains no references. -/
partial def dataOnly (flags : Array Bool) : VTy → Bool
  | .int | .logic | .char | .float => true
  | .arr ty | .opt ty => dataOnly flags ty
  | .tup tys => tys.all (dataOnly flags)
  | .ref tags args => !tags.isEmpty && tags.all (fun tag => flags[tag]?.getD false) &&
      args.all (dataOnly flags)
  | _ => false

mutual
/-- Prototype addresses are safe only when explicitly certified; private,
    unknown and out-of-range addresses remain unsafe through all wrappers. -/
def hasUnsafeObjectRef (safeProtos : Array Bool) : Value → Bool
  | .ref address => !(safeProtos[address]?.getD false)
  | .arr values => hasUnsafeObjectRefs safeProtos values.toList
  | .tup values => hasUnsafeObjectRefs safeProtos values
  | .some value => hasUnsafeObjectRef safeProtos value
  | _ => false

def hasUnsafeObjectRefs (safeProtos : Array Bool) : List Value → Bool
  | [] => false
  | value :: rest => hasUnsafeObjectRef safeProtos value || hasUnsafeObjectRefs safeProtos rest
end

@[simp] private theorem array_sizeOf (values : Array Value) :
    sizeOf values = 1 + sizeOf values.toList := by
  cases values
  rfl

mutual
theorem objectFree_hasTy (variance : Variances) (heap : HeapTy) (value : Value) (ty : VTy)
    (typed : hasTy variance heap value ty = true) (free : objectFree ty = true) :
    hasObjectRef value = false := by
  cases ty <;> cases value <;> simp_all [objectFree, hasTy, hasObjectRef]
  · apply objectFree_allTy <;> assumption
  · apply objectFree_allTys <;> assumption
  · apply objectFree_hasTy <;> assumption
termination_by sizeOf value + sizeOf ty
decreasing_by all_goals simp_all; omega

theorem objectFree_allTy (variance : Variances) (heap : HeapTy) (values : List Value) (ty : VTy)
    (typed : allTy variance heap values ty = true) (free : objectFree ty = true) :
    hasObjectRefs values = false := by
  cases values with
  | nil => rfl
  | cons value rest =>
    simp only [allTy, Bool.and_eq_true] at typed
    simp only [hasObjectRefs, Bool.or_eq_false_iff]
    exact ⟨objectFree_hasTy variance heap value ty typed.1 free,
      objectFree_allTy variance heap rest ty typed.2 free⟩
termination_by sizeOf values + sizeOf ty
decreasing_by all_goals simp_all; omega

theorem objectFree_allTys (variance : Variances) (heap : HeapTy) (values : List Value) (tys : List VTy)
    (typed : allTys variance heap values tys = true) (free : objectFreeTypes tys = true) :
    hasObjectRefs values = false := by
  cases values with
  | nil => rfl
  | cons value rest =>
    cases tys with
    | nil => simp [allTys] at typed
    | cons ty tys =>
      simp only [allTys, Bool.and_eq_true] at typed
      simp only [objectFreeTypes, Bool.and_eq_true] at free
      simp only [hasObjectRefs, Bool.or_eq_false_iff]
      exact ⟨objectFree_hasTy variance heap value ty typed.1 free.1,
        objectFree_allTys variance heap rest tys typed.2 free.2⟩
termination_by sizeOf values + sizeOf tys
decreasing_by all_goals simp_all; omega
end

end OpenVerse.Front.MetadataValues
