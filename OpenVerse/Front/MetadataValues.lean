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
