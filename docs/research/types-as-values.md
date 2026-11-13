# Types as values

The Book of Verse's metatypes, `subtype(t)`, `castable_subtype(t)`,
`concrete_subtype(t)` and `type`, and its conversions written as calls,
`int(0)`: what each form is, which of them the front end alone can give a
meaning to, what openverse builds and how, and what needs Verse Core.
[LANGUAGE.md](../LANGUAGE.md#types-as-values) states the rules for users;
[DESIGN.md](../DESIGN.md#types-as-values-classes-the-front-end-writes) says
how they are built.

## Sources

- The [Book of Verse at `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs):
  chapter 11, "Metatypes" (`docs/11_types.md` lines 1399-1700).
- Its tests: `Cast.versetest` (57-150), `Subtype.versetest`,
  `Castable.versetest` (85-170), `MetatypeConcreteSubtype.versetest`,
  `Archetypes.versetest:110`, `TypeParam.versetest`, `TypeValue.versetest`,
  `ClassifiableSubset.versetest`, `WhereConstrainedInts.versetest` (219-222).

## Quotations

- Ch. 11, 1409-1412: "The `subtype(T)` type constructor represents runtime
  type values that are subtypes of `T`. Unlike `concrete_subtype` and
  `castable_subtype`, which are specialized for classes and interfaces,
  `subtype(T)` works with **any type** in Verse".
- 1466-1467: "`subtype(T) <: subtype(U)` if and only if `T <: U`".
- 1500-1501: "Both `subtype(T)` and `castable_subtype(T)` are subtypes of
  `type`".
- 1517-1519 (`concrete_subtype`): "A concrete class is one that can be
  instantiated directly—it has the `<concrete>` specifier and provides
  default values for all fields"; 1578-1581: "the actual type value
  assigned must be a concrete class"; 1605-1607: "you can instantiate it
  with the empty archetype `{}`, but you cannot provide field initializers".
- 1636-1643 (`castable_subtype`): "represents types that are subtypes of
  `t` and marked with the `<castable>` specifier. This constraint is
  required when you want to use types as first-class values … and then use
  those type values to perform casts. Note that the `<castable>` specifier
  is not required for basic dynamic casting".
- `Subtype.versetest:65`: "We can't yet compare the subtype values".
- `Cast.versetest:56`: "Test infallible casts. These should produce a
  compile error if the argument type is not a subtype of the cast type."

## Where the prose and the tests disagree

- **Casts through a type value.** The prose makes `castable_subtype` the
  metatype to cast through: "This constraint is required when you want to
  use types as first-class values … and then use those type values to
  perform casts" (ch. 11, `docs/11_types.md` 1636-1641). The tests cast
  through a value of `subtype(base)`, `base` not `<castable>`, and expect
  the cast to work (`Cast.versetest` 90-100: "ensure that casting class and
  interface types through type variables applies the values of the
  variable", `t := if (true?) then class2 else classB  # t has the type
  subtype(base)`, then `t[X]`). openverse follows the tests: a cast goes
  through any metatype's value.

## The map, by form

| form | cases when surveyed | front end alone? | built |
|---|---:|---|---|
| a conversion written as a call, `int(0)`, `float(0.0)`, `logic(false)`, `void(0)`, `s(s{})`, `(?int)(…)`, `([]int)(…)` (`Cast.versetest` 57-71, 59-62; `WhereConstrainedInts.versetest` 219-222) | 13 | yes: `X` checked at `t` and converted | yes |
| a class or an interface named as a value of `subtype(c)`, stored, passed, returned, upcast (`Subtype.versetest` 66-96, 140-190; ch. 11's examples) | about 45 | yes: a value of a class of its own, the metatypes interfaces | yes |
| a cast through a type value, `t[X]` with `t:subtype(c)`, and a join of two class values (`Cast.versetest` 98-149) | 8 | yes: the cast is a method of the value | yes |
| `concrete_subtype(c)`, construction through it, `T{}` (ch. 11's `spawner`; `MetatypeConcreteSubtype.versetest` 300-329) | about 12 | yes: the construction is a method of the value | yes, `T{}` with no field given; a value's own class with fields (`Type := concrete_class; Type{Value := 42}`, :153) not |
| `castable_subtype(c)` (`Castable.versetest` 91-170) | about 20 | yes: an interface of the castable classes' values | yes; as a type parameter's bound (`where t:castable_subtype(c)`, 519-563) not: a bound of #502's kind |
| `type`, the type of every type value (`f(c:subtype(C)):type = c`, `Subtype.versetest` 99-103) | 4 | yes, for class values | yes; of other types' values not |
| `subtype(int)`, `subtype([]C)`, a value `int` of `type` (`Subtype.versetest` 113-119, 140-142, `TypeParam.versetest` 3-16, `TypeValue.versetest`) | about 20 | in part: values of other types than classes carry nothing the program can use but `type` itself, so they need no witness; each needs a class of its own in this design | yes, of a built-in type, a struct, an enum, and arrays, options, maps and tuples of them; a type written as an expression other than a name (`Identity([]int)`, `Identity(c(int))`, `Identity(subtype(c))`) not: the parser reads no such expression |
| a type given as an argument and used as a type, `False(t:type):?t = false`, `FalseOption(t:type)`, `EmptyArray(t:type)` (`TypeParam.versetest` 57-60, `ParametricTypes.versetest` 613-624) | 6 | yes: a generic call with the type given | yes (`TypeArguments`); `Bar(t)` of a type parameter `t` not, as the BPVM's link error (`TypeParam.versetest` 41-52) |
| `concrete_subtype(comparable)`, `concrete_subtype(any)` (`MetatypeConcreteSubtype.versetest` 13-41) | 10 | yes: interfaces the `<unique>` and the `<concrete>` classes' values implement | yes; construction through them refused (3545, as the tests have it); `castable_subtype(any)` (`Castable.versetest` 609-618) not |
| `classifiable_subset(t)` (`ClassifiableSubset.versetest`) | 21 | no | no: a set of types, which the Book's chapters do not describe |
| a metatype as a type parameter's bound, `where t:subtype(class1)` (`ParametricFunctions.versetest` 46-57, 237-248) | 8 | front end, #502's checked upper-bound evidence | no (#502) |
| comparison of type values (`TestUtils.AreClassesEqual`) | — | — | not translatable (the test runner's); the Book: "We can't yet compare the subtype values" |

## Design (as built): a type value is a witness object

Since #520 openverse checks subtype evidence and passes hidden type
witnesses, and a function value is an object of a class whose method is the
function (#210). A type value of a class or an interface is the same kind of
object, made by the front end with no Verse Core added
(`Front/TypeValues.lean`, run after modules and access are resolved):

- **Values.** A class or interface `C` named as a value is `$type:C{}`, an
  object of a class of its own. Verse has no shadowing, so a name that is a
  class's in scope is the class.
- **Types.** For each class or interface `A` at or above one named in a
  metatype or as a value, the interfaces `subtype(A)`, `castable_subtype(A)`
  and `concrete_subtype(A)`, each below the same interface of each parent of
  `A` (so `subtype(A)` is below `subtype(B)` exactly when `A` is below `B`,
  ch. 11, 1466), `subtype(A)` below `type` at the top, `castable_subtype(A)`
  and `concrete_subtype(A)` below `subtype(A)`; `castable_subtype(A)` of a
  `<castable>` `A` also below the mark `$castable`.
- **Casts.** `subtype(A)` declares `$cast(A)(X:A)<decides>:A`; `$type:C`
  gives it, for each `A` above `C`, as `C[X]` (as a cast that always fails
  when no class is below `C`). `T[X]` with `T` of a metatype of `A` is
  `T.$cast(A)[A[X]]`: the object's class is tested by the class the value
  is, at the value's bound.
- **Constructions.** `concrete_subtype(A)` declares `$make(A)():A`;
  `$type:C` gives it as `C{}` when `C` is `<concrete>` (ch. 11, 1517-1519;
  `MetatypeConcreteSubtype.versetest:40`), and is then below
  `concrete_subtype(C)`. `T{}` is `T.$make(A)()`; `T{F := e}` is refused
  (ch. 11, 1605-1607).
- **`<castable>`.** `$type:C` is below `castable_subtype(C)` when `C` is
  `<castable>` (inherited); `castable_subtype(A)` exists for any `A`, as the
  tests type `Value: castable_subtype(class1) = class2` with only `class2`
  castable (`Castable.versetest` 95, 126).
- **Joins.** Two different type values join at the nearest metatype above
  both that is no `concrete_subtype` (a class value's type is its own class;
  a join keeps the bound only, `Archetypes.versetest:110`) and no
  `castable_subtype(A)` of an `A` that is not `<castable>`, before an
  expected type is met (`Castable.versetest` 145, 168); a container literal
  expected to be of `castable_subtype` or `concrete_subtype` checks its
  elements' join.
- **Not compared.** The classes `$type:C` are not `<unique>`, so `=` on type
  values is refused, as the Book's tests have it.

## What needs Verse Core, and a design

- **Type values of other types** (`int`, `[]C`, enums, structs) and `type`
  as their type: built, by this design. `subtype(t)` of a built-in type, a
  struct, an enum, or an array, option, map or tuple of them, is an
  interface below `type`, named by the type as written (`subtype([]c)`),
  with no method; a type's name used as a value is `$type:t{}`, an object
  of a class of its own below `subtype(t)`, which nothing reads but a
  conversion to `type`. `castable_subtype` and `concrete_subtype` of such a
  type stay refused, as the tests have them (3509). Function types
  (`subtype(type{f():void})`) and types written as expressions other than
  names (`Identity([]int)`) are not: the parser reads neither there.
- **A type given as an argument and used as a type** (`False(t:type):?t`):
  built, by the design that was left here. Verse Core's generic functions
  are checked once for every instance and take a witness value per type
  parameter (`LANGUAGE.md`, Parametric functions); a parameter `t:type` the
  code uses as a type is such a type parameter whose argument the caller
  writes. `TypeArguments.desugar`, before `TypeValues.desugar`, makes the
  function generic over `t` and the parameter, in its place,
  `$typeArgument:t:?t`, which nothing reads; a call's argument there, a type
  as written, becomes that parameter's value `(?int)(false)`, from which the
  call's type argument is inferred, with `int`'s witness: no Core change. A
  type parameter given there (`Foo(:t where t:type):void = Bar(t)`) is
  refused, the BPVM's link error 9001 (`TypeParam.versetest:43`), which the
  VerseVM twin (:49) accepts: openverse keeps the case it agrees with. A
  comparison's operand takes its type from the other's only as a hint, so
  `False(int) = False(logic)` compares a `?int` and a `?logic`, as any two
  comparable values (`TypeParam.versetest:59`).
- **`concrete_subtype(comparable)` and `concrete_subtype(any)`**: built, by
  this design. Each is an interface below `type` that the value of a
  `<concrete>` class implements, of `concrete_subtype(comparable)` only one
  that is also `<unique>` (comparable, by identity), so
  `c1:concrete_subtype(comparable) = c` holds and `= float` is refused. They
  declare no construction: `c1{}` is refused ("comparable cannot be
  instanced here because we don't know if it's a class type",
  `MetatypeConcreteSubtype.versetest:35`, 3545). `subtype(any)`,
  `subtype(comparable)` and `castable_subtype(any)` are not built: their
  values would be those of every type, or every comparable one, which this
  design would have to give every type value.
- **`classifiable_subset`**: not designed; the Book's chapters do not
  describe it.
