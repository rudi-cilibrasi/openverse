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
  | .fn _ _ r => determines r
  | t => t.children.flatMap determines

/-- Each bounded type parameter of a function, and each that a bound names,
    is determined by a call's arguments: named in the type of one of its
    parameters, where an argument gives it, or in the bound of a type
    parameter that is (`Foo(X:t where t:subtype(u), u:type)`). Otherwise no
    call can give it, the Book's rule (its tests, `ParametricFunctions.versetest`
    336-374 and 586, error 3503). One without a bound must be named in the
    function's signature, its parameters' types or its result's: the tests
    refuse `F(:u where t:type, u:type)` (`:374`), which nothing can give a
    `t`. (They refuse `F(() where t:type):?t` (`:338`) and
    `F(G(:t):void where t:type)` (`:348`) too, which openverse keeps, its
    reading that a call's expected result gives a type parameter
    (`docs/LANGUAGE.md`, "Readings"); VerseVM takes
    `MakeClosure(Callback:tuple(payload, context)->void, …)`, whose
    `payload` only a function type's parameter names,
    `Bugs/FORT-592189-MaybeCoerceToTypeCrash.versetest:44`.) -/
def checkDetermined (fname : String) (params : List SParam) (tparams : List TParam) (ret : STy) : Except String Unit := do
  let names := tparams.map (·.name)
  let mut known := (params.flatMap fun q => determines q.ty).filter names.contains
  for _ in tparams do
    for tp in tparams do
      if known.contains tp.name then
        known := known ++ ((tp.upperBound.map determines).getD []).filter fun n => names.contains n && !known.contains n
  let inBounds := tparams.flatMap fun tp => (tp.upperBound.map STy.allNames).getD []
  let named := params.flatMap (·.ty.allNames) ++ ret.allNames
  for tp in tparams do
    let free := tp.upperBound.isNone && !inBounds.contains tp.name
    if free && !named.contains tp.name then
      throw s!"{tp.pos.show}: the type parameter {tp.name} of {fname} is named nowhere in its signature, so nothing can give it one: name it in a parameter's type or the result's, or remove it (the Book's tests, ParametricFunctions.versetest:374, error 3503)"
    unless known.contains tp.name || free do
      throw s!"{tp.pos.show}: no parameter of {fname} determines its type parameter {tp.name}, so no call can give it one: name {tp.name} in a parameter's type, outside a function type's parameters (the Book's tests, ParametricFunctions.versetest, error 3503)"

/-- The type parameters a definition declares, its methods' too. -/
partial def tparamsOf : STop → List TParam
  | .fn _ _ _ tps .. => tps
  | .const _ _ _ _ (.structDef _ tps _ _) => tps
  | .classDef _ _ _ tps _ _ _ _ methods => tps ++ methods.flatMap tparamsOf
  | _ => []

/-- The metatypes openverse takes as a type parameter's bound: `subtype(c)`
    and `castable_subtype(c)`, which the Book's tests write
    (`Castable.versetest` 510-603). `concrete_subtype(c)` is refused: the
    instance it asks for is a class marked `<concrete>` (`TypeValues`), which
    a class below one is not, so it is no subtype relation a bound's checked
    evidence can carry. -/
def checkKinds (params : List TParam) : Except String Unit := do
  for tp in params do
    if tp.constraint == "concrete_subtype" && tp.upperBound.isSome then
      throw s!"{tp.pos.show}: {tp.name}:concrete_subtype(…) is not supported as a type parameter's bound: a concrete class's subclasses need not be concrete, so it is no subtype relation; write {tp.name}:subtype(…)"

/-- A program that writes a `castable_subtype(c)` bound has the interface
    `castableClassMarker`, above each `<castable>` class and interface (and
    so above the classes below them, as castability is inherited): the bound
    is `subtype(c)` and `subtype(castableClassMarker)` together, each with its
    own checked evidence (`resolveTParams`). Unchanged otherwise. -/
def markCastable (tops : List STop) : List STop :=
  if !(tops.flatMap tparamsOf).any (·.constraint == "castable_subtype") then tops else
  let p0 : Pos := { line := 0, col := 0 }
  let marker : STop := .classDef p0 castableClassMarker [] [] ["computes"] [] true [] []
  marker :: tops.map fun
    | .classDef p n nsp tps specs parents isI fs ms =>
      .classDef p n nsp tps specs (if specs.contains "castable" then parents ++ [.name castableClassMarker] else parents)
        isI fs ms
    | t => t

end OpenVerse.Front.UpperBounds
