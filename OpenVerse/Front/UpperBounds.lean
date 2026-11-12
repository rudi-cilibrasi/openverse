import OpenVerse.Front.Syntax

namespace OpenVerse.Front.UpperBounds

partial def hasBounds : STop → Bool
  | .fn _ _ _ parameters .. => parameters.any (·.upperBound.isSome)
  | .const _ _ _ (.structDef _ parameters _ _) => parameters.any (·.upperBound.isSome)
  | .classDef _ _ parameters _ _ _ _ _ methods =>
    parameters.any (·.upperBound.isSome) || methods.any hasBounds
  | _ => false

/-- Until the checked evidence ABI is ready, retained bounds must be refused
    before inlining can erase the generic declaration. The legacy name-only
    compiler API representation is checked at this boundary too. -/
def checkParams (params : List TParam) : Except String Unit := do
  for param in params do
    if param.upperBound.isSome || !["type", "comparable"].contains param.constraint then
      throw s!"{param.pos.show}: unknown constraint subtype({param.constraint}) (checked upper-bound evidence is not implemented yet, #502)"

end OpenVerse.Front.UpperBounds
