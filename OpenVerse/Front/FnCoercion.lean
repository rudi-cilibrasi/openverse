/-
  OpenVerse front end — the conversions of function values Epic's Verse
  compiler does not make (#724).

  A function value of one function type used as a value of another that
  its value does not already have needs a wrapper: a function that takes
  the other type's arguments, converts them, calls the value and converts
  its result. Epic's Verse compiler (UEFN 43.12,
  ++Fortnite+Release-43.12-CL-60598086) makes one for a function named as a
  value where a function type is expected, and for no other value: it
  refuses the others with error 3502, "Using a value of type A as a value
  of type B is not yet implemented" (tests/conformance/versevm/
  followup-book2, the Book of Verse's `bp_vm_only` tests). openverse needs
  no wrapper (a function value is an object of every function type it
  fits, `FnValues`), so it refuses them by these rules, unless
  `--function-coercions` (`TyEnv.functionCoercions`). The rules, and the
  evidence for each, are in docs/LANGUAGE.md, "Function values".
-/
import OpenVerse.Front.Types

namespace OpenVerse.Front
open OpenVerse

namespace FnCoercion

/-- The shape of a function type, of no other type. -/
def shape? : Ty → Option FnValues.Shape
  | .struct n _ => FnValues.parse n
  | _ => none

/-- A function type. -/
def isFn (t : Ty) : Bool := (shape? t).isSome

/-- A function of shape `a` is called through a function type of shape
    `b` as it is: the same effects and the same parameters, positional and
    named, and every named parameter `b` lets a caller omit one `a` has a
    default for (`F:type{_(?A:int):int} = if (true?) { F1 } else { F2 }`
    with `F2(?A:int = 2)`, the Book of Verse's `DefaultNamed.versetest:623`,
    valid on both VMs). A named parameter `a` has and `b` has not needs the
    wrapper that gives its default (`join-named-default-fn`). -/
def shapeAsIs (a b : FnValues.Shape) : Bool :=
  { a with optional := [] } == { b with optional := [] } && b.optional.all a.optional.contains

mutual
/-- A value of type `a` is one of type `b` as it is, no wrapper made: the
    same type, `void` and `true` for each other (Book of Verse tests,
    `Void.versetest` 161-173, admitted on both VMs), a reference to a class
    or interface above (`refUp`; `FunctionTypes.versetest` 198-203, the
    join of `tuple()->C2` and `tuple()->C3`), a function type that
    `needsWrapper` does not. Anything else changes the value: `int` to
    `rational` or to `void`, `int` or `float` to `comparable`, a class to
    `comparable`, `void` to `int` (UEFN 43.12: followup-coerce2's
    `join-int-rational`, `value-int-rational-result`, `value-void-result`;
    `book-join-fn-result`, `book-join-comparable-param`,
    `book-join-void-param`). -/
partial def asIs (env : TyEnv) (a b : Ty) : Bool :=
  a == b || (a.isUnit && b.isUnit) || (!a.isUnit && a.unitUp b) ||
    match shape? a, shape? b with
    | some _, some _ => !needsWrapper env a b
    | none, none => refUp env a b
    | _, _ => false

/-- A value of function type `a` used as one of function type `b` needs a
    wrapper: their effects or their parameters differ, beyond the defaults
    `shapeAsIs` allows (UEFN 43.12: `join-generic-effects-*`,
    `join-named-*`, `book-join-array-tuple-param`), or a parameter of `b`
    is no parameter of `a` as it is, or `a`'s result no result of `b`
    (`book-join-void-param`, `book-join-void-result`,
    `book-join-comparable-param`). Not for types that are not both
    function types. -/
partial def needsWrapper (env : TyEnv) (a b : Ty) : Bool :=
  match a, b with
  | .struct S as, .struct T bs =>
    match FnValues.parse S, FnValues.parse T with
    | some sa, some sb =>
      !shapeAsIs sa sb || as.length != bs.length ||
        !((as.take sa.arity).zip (bs.take sa.arity)).all (fun (x, y) => asIs env y x) ||
        !asIs env (as.getLastD .void) (bs.getLastD .void)
    | _, _ => false
  | _, _ => false
end

/-- A value of type `a` used as one of type `b` holds a function value that
    `needsWrapper`: `a` and `b` function types that do, or options, arrays,
    tuples or maps (their values) of such (UEFN 43.12: "Using a value of type
    ?((?A:int = ...)->int) as a value of type ?(tuple()->int)",
    `option-of-fn-default`). -/
partial def needsWrapperDeep (env : TyEnv) : Ty → Ty → Bool
  | a@(.struct _ _), b@(.struct _ _) => isFn a && isFn b && needsWrapper env a b
  | .opt a, .opt b | .arr a, .arr b => needsWrapperDeep env a b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).any fun (a, b) => needsWrapperDeep env a b
  | .map _ a, .map _ b | .map _ a, .weakMap _ b | .weakMap _ a, .weakMap _ b => needsWrapperDeep env a b
  | _, _ => false

/-- The type parameters a type mentions inside a function type (`t` in
    `t->void`, `[]type{_():t}`, `tuple(tuple()->t, int)`). -/
partial def paramsInFn : Ty → List String
  | t@(.struct n ts) => if (FnValues.parse n).isSome then t.params else ts.flatMap paramsInFn
  | .arr t | .opt t => paramsInFn t
  | .tup ts => ts.flatMap paramsInFn
  | .map k v | .weakMap k v => paramsInFn k ++ paramsInFn v
  | _ => []

/-- An instance of a type parameter that changes no function type it is
    inside: `any` and `comparable`, as a type parameter's values are in
    generic code (UEFN 43.12 shows the declaration's `t` as `any`,
    `interface-fn-param-generic`; the Book's `ParametricFunctions.versetest`
    546 takes a `comparable` "so a function coercion isn't required"). -/
def erasedInstance (t : Ty) : Bool := t == .any || t == .dyn

/-- Of the type parameters `vs`, those that `σ` instantiates to a type that
    changes a function type they are inside (`erasedInstance`): not to
    another type parameter, whose values generic code has as it has its own
    (`fn_values_open_*`), nor where `σ` does not say (`unknown`). -/
def changedBy (σ : List (String × Ty)) (vs : List String) (unknown : Bool := false) : List String :=
  vs.filter fun v => match σ.lookup v with
    | some (.param ..) => false
    | some t => !erasedInstance t
    | none => unknown

/-- The citation every refusal of this module ends with. -/
def cite : String :=
  "(Epic's Verse compiler, UEFN 43.12: error 3502; #724; --function-coercions keeps openverse's conversion)"

/-- A function type with its type parameters, as Epic's compiler writes a
    generic function's: `type{_(:t)<computes>:t} where t`. -/
def showGeneric (t : Ty) (tps : List String) : String :=
  if tps.isEmpty then t.show else s!"{t.show} where {", ".intercalate tps}"

end FnCoercion

end OpenVerse.Front
