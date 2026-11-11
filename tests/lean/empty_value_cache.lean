import OpenVerse.Core.Bounded
import OpenVerse.Core.Typing

open OpenVerse

-- Keep the producers separate so compiler common-subexpression elimination
-- cannot make freshly allocated wrappers appear shared.
@[noinline] def directArray (n : Nat) : Value :=
  Value.ofArray (Array.replicate n Value.void)

@[noinline] def capacityArray (capacity : Nat) : Value :=
  Value.ofArray (Array.emptyWithCapacity capacity)

@[noinline] def directTuple (n : Nat) : Value :=
  Value.ofTuple (List.replicate n Value.void)

@[noinline] def primitiveValue (op : Prim) (vs : List Value) : Value :=
  match op.apply vs with
  | .ok v => v
  | _ => .none

@[noinline] def stringValue (s : String) : Value := Value.ofString s

@[noinline] def forValue (bounded : Bool) (acc : List Value) : Value :=
  let p : Prog := { fns := [], main := 0 }
  let s : St := { fr := [], g := { out := [], heap := #[] } }
  if bounded then
    match evalForB p 2 2 0 (.lit .void) (.lit .void) s [] acc with
    | .res (.ok v, _) => v
    | _ => .none
  else
    match evalFor p 2 0 (.lit .void) (.lit .void) s [] acc with
    | some (.ok v, _) => v
    | _ => .none

unsafe def main : IO Unit := do
  let empty := Value.emptyArray
  for v in [directArray 0, capacityArray 16, primitiveValue .mkArr [],
      primitiveValue .range [.int 1, .int 0],
      primitiveValue .concat [directArray 0, directArray 0],
      primitiveValue .flatten [directArray 0],
      primitiveValue .flatten [Value.ofArray #[directArray 0, directArray 0]],
      primitiveValue .toStr [directArray 0], stringValue "",
      forValue false [], forValue true [], VTy.default (.arr .int)] do
    unless ptrEq empty v do
      throw (IO.userError "empty array producer did not share its wrapper")
  for v in [directTuple 0, primitiveValue .mkTup [], VTy.default (.tup [])] do
    unless ptrEq Value.void v do
      throw (IO.userError "empty tuple producer did not share void")
  unless empty ≠ Value.void && !(ptrEq empty Value.void) do
    throw (IO.userError "empty arrays and tuples must remain distinct")
  let pair := primitiveValue .mkArr [directArray 0, directArray 0]
  match pair with
  | .arr xs =>
    unless xs.size == 2 && xs.all (fun v => ptrEq empty v) do
      throw (IO.userError "sharing changed collection multiplicity")
  | _ => throw (IO.userError "array construction changed its constructor")
  unless directArray 2 = .arr #[.void, .void] &&
      directTuple 2 = .tup [.void, .void] &&
      primitiveValue .range [.int 1, .int 2] = .arr #[.int 1, .int 2] &&
      stringValue "a" = .arr #[.char 97] &&
      forValue false [.int 2, .int 1] = .arr #[.int 1, .int 2] &&
      forValue true [.int 2, .int 1] = .arr #[.int 1, .int 2] do
    throw (IO.userError "nonempty collection changed value")
  IO.println "empty collections: wrappers shared; constructors and multiplicity preserved"
