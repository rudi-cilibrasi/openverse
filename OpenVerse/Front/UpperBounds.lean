import OpenVerse.Front.Syntax

namespace OpenVerse.Front.UpperBounds

/-- Until the checked evidence ABI is ready, retained bounds must be refused
    before inlining can erase the generic declaration. The legacy name-only
    compiler API representation is checked at this boundary too. -/
def checkParams (params : List TParam) : Except String Unit := do
  for param in params do
    if param.upperBound.isSome || !["type", "comparable"].contains param.constraint then
      throw s!"{param.pos.show}: unknown constraint subtype({param.constraint}) (checked upper-bound evidence is not implemented yet, #502)"

end OpenVerse.Front.UpperBounds
