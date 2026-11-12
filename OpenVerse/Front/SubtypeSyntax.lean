/- Syntax-only subtype evidence metadata, shared by pre-elaboration adapters
   and the typed evidence planner without a dependency cycle. -/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front.SubtypeEvidence

def family : String := "$subtypeEvidence"
def identityFamily : String := "$subtypeIdentity"
def composeFamily : String := "$subtypeCompose"

/-- Readonly compiler proofs are separate from dummy type-value fields. -/
def fieldPrefix : String := "$subtype."
def fieldName (owner parameter : String) : String := s!"{fieldPrefix}{owner}.{parameter}"

/-- A full relation after adapter substitution, including compound lower
    types. Its field is both a declaration constraint and an actual proof. -/
def relationFields (p : Pos) (owner : String) (relations : List (STy × STy)) :
    List (String × STy × Option SExpr × Bool) :=
  relations.zipIdx.map fun ((base, derived), i) =>
    (fieldName owner s!"$relation{i}", .app family [base, derived],
      some (.app p (.ident p "$subtypeWitness") [.construct p family [base, derived] []] false), false)

def declaredRelation? (owner name : String) (ty : STy) (mutable : Bool) : Option (STy × STy) := do
  if mutable || !name.startsWith (fieldName owner "$relation") then none else do
    let .app protocol [base, derived] := ty | none
    if protocol == family then some (base, derived) else none

end OpenVerse.Front.SubtypeEvidence
