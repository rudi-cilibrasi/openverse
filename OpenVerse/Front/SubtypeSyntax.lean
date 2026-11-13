/- Syntax-only subtype evidence metadata, shared by pre-elaboration adapters
   and the typed evidence planner without a dependency cycle. -/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front.SubtypeEvidence

def family : String := "$subtypeEvidence"
def identityFamily : String := "$subtypeIdentity"
def composeFamily : String := "$subtypeCompose"
def rationalFamily : String := "$subtypeRational"
def eraseFamily : String := "$subtypeErase"
def discardFamily : String := "$subtypeDiscard"
def bottomFamily : String := "$subtypeBottom"
def arrayFamily : String := "$subtypeArray"
def optionFamily : String := "$subtypeOption"
def mapFamily : String := "$subtypeMap"
def tupleFamily (arity : Nat) : String := s!"$subtypeTuple{arity}"
def tupleArrayFamily (arity : Nat) : String := s!"$subtypeTupleArray{arity}"

/-- Readonly compiler proofs are separate from dummy type-value fields. -/
def fieldPrefix : String := "$subtype."
def fieldName (owner parameter : String) : String := s!"{fieldPrefix}{owner}.{parameter}"

/-- A full relation after adapter substitution, including compound lower
    types. Its field is both a declaration constraint and an actual proof. -/
def relationFields (p : Pos) (owner : String) (relations : List (STy × STy)) : List SField :=
  relations.zipIdx.map fun ((base, derived), i) =>
    { name := fieldName owner s!"$relation{i}", ty := .app family [base, derived],
      default := some (.app p (.ident p "$subtypeWitness") [.construct p family [base, derived] []] false) }

def declaredRelation? (owner name : String) (ty : STy) (mutable : Bool) : Option (STy × STy) := do
  if mutable || !name.startsWith (fieldName owner "$relation") then none else do
    let .app protocol [base, derived] := ty | none
    if protocol == family then some (base, derived) else none

end OpenVerse.Front.SubtypeEvidence
