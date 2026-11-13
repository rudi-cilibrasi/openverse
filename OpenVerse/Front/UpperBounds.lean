/- Source rules of type parameters' upper bounds (#502), checked on the
   program as written: what a bound needs of the parameters. The checked
   evidence a bound gives is `SubtypeEvidence`'s; what the Book's rules are,
   and which of them openverse follows, `docs/research/upper-bound-evidence.md`. -/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front.UpperBounds

partial def hasBounds : STop → Bool
  | .fn _ _ _ parameters .. => parameters.any (·.upperBound.isSome)
  | .const _ _ _ _ (.structDef _ parameters _ _) => parameters.any (·.upperBound.isSome)
  | .classDef _ _ _ parameters _ _ _ _ methods =>
    parameters.any (·.upperBound.isSome) || methods.any hasBounds
  | _ => false

/-- The names a parameter's type gives a call's argument to infer: those it
    writes but as a parameter of a function type, which an argument's type
    does not determine (`F(G(:t):void where t:type)`, the Book's tests). -/
partial def determines : STy → List String
  | .name n => [n]
  | .arr t | .opt t => determines t
  | .tup ts | .app _ ts => ts.flatMap determines
  | .map k v => determines k ++ determines v
  | .fn _ _ r => determines r

/-- Each bounded type parameter of a function, and each that a bound names,
    is determined by a call's arguments: named in the type of one of its
    parameters, where an argument gives it, or in the bound of a type
    parameter that is (`Foo(X:t where t:subtype(u), u:type)`). Otherwise no
    call can give it, the Book's rule (its tests, `ParametricFunctions.versetest`
    336-374 and 586, error 3503). openverse keeps, for a type parameter
    without a bound, its reading that the expected result can give it
    (`docs/LANGUAGE.md`, "Readings"); a bound's evidence comes from an
    argument's type, not from the context a call's result goes to. -/
def checkDetermined (fname : String) (params : List SParam) (tparams : List TParam) : Except String Unit := do
  let names := tparams.map (·.name)
  let mut known := (params.flatMap fun q => determines q.ty).filter names.contains
  for _ in tparams do
    for tp in tparams do
      if known.contains tp.name then
        known := known ++ ((tp.upperBound.map determines).getD []).filter fun n => names.contains n && !known.contains n
  let inBounds := tparams.flatMap fun tp => (tp.upperBound.map STy.allNames).getD []
  for tp in tparams do
    unless known.contains tp.name || (tp.upperBound.isNone && !inBounds.contains tp.name) do
      throw s!"{tp.pos.show}: no parameter of {fname} determines its type parameter {tp.name}, so no call can give it one: name {tp.name} in a parameter's type, outside a function type's parameters (the Book's tests, ParametricFunctions.versetest, error 3503)"

end OpenVerse.Front.UpperBounds
