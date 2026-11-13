# `comparable` as a type

What the Book of Verse says a value of type `comparable` is, why openverse's
representation of values cannot give the Book's answers for it as `any` is
built, and what each way of building it would take. Nothing here is
implemented: `comparable` stays a constraint, `t:subtype(comparable)`, and
`comparable` as a type stays "unknown type 'comparable'"
([LANGUAGE.md](../LANGUAGE.md#parametric-functions)).

## Sources

- The [Book of Verse at `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs):
  chapter 11, "Type `any`" (`docs/11_types.md` lines 152-225) and
  "Comparable and Equality" (lines 918-1127); chapter 4, "Equality
  Operators" (`docs/04_operators.md` lines 323-376); chapter 9, enum
  "Comparison" (`docs/09_structs_enums.md` lines 557-581); chapter 1, arrays
  (`docs/01_expressions.md` line 1276); chapter 10, parametric interfaces
  (`docs/10_classes_interfaces.md` lines 1703-1737); chapter 14
  (`docs/14_concurrency.md` lines 1530-1535); chapter 17
  (`docs/17_persistable.md` line 178).
- The same snapshot's tests, by line: `Tests/Comparable.versetest`,
  `Tests/EnumCompare.versetest`, `Tests/Any.versetest`,
  `Tests/RollbackTortureTest.versetest`,
  `Tests/MetatypeConcreteSubtype.versetest`.
- The API signature of `=` quoted in [the digest](book-of-verse-digest.md)
  §5.4.
- Retrieved 2026-11-13. No Epic source was read and no Epic engine was run.

**Release status.** No "Unreleased Feature" marker on these sections;
development-branch evidence, as the Book's.

## Quotations

- Ch. 11, lines 920-931: "The `comparable` type represents a special subset
  of types that support equality comparison. … The basic scalar types are
  all comparable: `int`, `float`, `rational`, `logic`, `char`, and
  `char32`. Compound types are comparable if all their components are
  comparable."
- Lines 934-945: `operator'='(X:t, Y:t where t:subtype(comparable))<decides>:t`;
  "the return type is the least upper bound of their types". The API's
  signature (digest §5.4) is `operator'='(Lhs:t, Rhs:comparable where
  t:subtype(comparable))<…><decides>:t`: the right operand is a
  `comparable`.
- Lines 948-975: `not (0 = 0.0)  # Fails - there is no implicit conversion
  from int to float`; "Note that `0 = 0.0` is not rejected by the compiler.
  Both operands are subtypes of `comparable`, so the comparison
  type-checks; it simply never succeeds, because an `int` and a `float`
  are never the same value." `CompareToString(I:int, S:string)<computes><decides>:comparable
  = I = S`: "For an `int` and a `string` the only common type is
  `comparable`."
- Ch. 4, lines 369-376: "Comparisons between different types still compile,
  but they always fail: `not (0 = 0.0)`, `not ("5" = 5)`."
- Ch. 9, line 559: "Enum values from the same enum type can be compared,
  while values from different enum types are always unequal"
  (`CurrentState <> weapon_type.Sword  # succeeds - different enum types`).
- Ch. 11, lines 1043-1077: `F(X:int)` and `F(X:comparable)` are ambiguous
  overloads ("int is already comparable"), as are a `<unique>` class and
  `comparable`; `H(X:regular_class)` and `H(X:comparable)` are not.
- Lines 1080-1102, "Dynamic Comparable Values": "you may need to box
  comparable values into the `comparable` type explicitly. These boxed
  values maintain their equality semantics": `AsComparable(X:comparable):comparable
  = X`; `array{AsComparable(1)} = array{1}` and `= array{AsComparable(1)}`
  succeed, `array{AsComparable(1)} <> array{2}` succeeds;
  `comparable(15) = comparable(15)` and `comparable("Hello") = "Hello"`
  succeed. "This allows you to create collections that mix different
  comparable types by boxing them all to `comparable`."
- Lines 1106-1118: map keys must be comparable types.
- Ch. 1, line 1276: `Mixed := array{1, "two", 3.0}  # Element type is
  comparable, their common supertype`. Ch. 11, lines 181-196:
  `Arr:[]comparable = MixedArray` and `Mp:[int]comparable = MixedMap`
  compile; with a function value among them, "annotating it
  `[string]comparable` is a compile error". Ch. 14, lines 1532-1535: without
  a declared result "the inferred common supertype widens all the way to
  `comparable`".
- Ch. 11, lines 224-225: "You cannot use equality operators with `any`";
  "Because `any` is not comparable, it cannot be used as a map key type".
- Ch. 17, line 178: `comparable` is not persistable: an "Abstract interface
  type".
- Ch. 10, lines 1707-1714: `int_equivalence := class(equivalence(int,
  comparable))` with `Equal<override>(Left:int, Right:comparable)…:int =
  Left = Right`.

The tests add:

- `Comparable.versetest` lines 3-8 and 159-165: `Equal(X:t, Y:comparable
  where t:subtype(comparable))<decides>:t = X = Y`, and `<>`; lines 14-140:
  boxed and unboxed ints, chars, arrays, strings, options and maps compare
  equal exactly when their values are equal (`not Equal[array{1},
  array{AsComparable(2)}]`), arrays equal tuples (`Equal[array{1, 2, 3},
  (1, 2, 3)]`, lines 125-140); lines 147-157: `not Equal[letters.A, numbers.One]`, an enum
  value boxed is not another enum's first value; lines 179-192: the
  overloads above; lines 194-203: `F(X? or 1)` with `X:?comparable_class`
  (a `<unique>` class) joins at `comparable`, with a class that is not
  comparable it is an error.
- `EnumCompare.versetest` lines 6-18: `Equal(A:comparable, B:comparable)`,
  with `not Equal[42, e.E]`, `not Equal[e.E, array{1}]`, `not Equal['f',
  e.E]`.
- `Any.versetest` lines 66 and 74: `Map2:[comparable]comparable = Map1`,
  `comparable` as a map's key type.
- `RollbackTortureTest.versetest` line 25: `var A:[]comparable =
  MakeInt32Array(N)`, an `[]int` where a `[]comparable` is expected.

## What a value of type `comparable` is

The pinned rules, and the readings where the Book is silent:

1. **Conversion to it.** Every value of a comparable type is a
   `comparable`, implicitly where one is expected (`AsComparable(1)`,
   `var A:[]comparable = MakeInt32Array(N)`, containers elementwise) and
   explicitly, `comparable(15)`. A value of a type that is not comparable
   (`any`, a function, a class that is not `<unique>`) is not.
2. **Equality.** `=` and `<>` take a `comparable` on either side (the API's
   `Rhs:comparable`). A boxed value equals another value, boxed or not,
   exactly when both have the same type and equal values: an `int` never
   equals a `float`, a `string` or an enum value; two enums' values never
   equal each other (ch. 9, test lines 147-157). The array-tuple equality
   holds (test lines 125-140, unboxed; the Book does not
   say it holds through boxes, which is the reading here).
3. **Back from it.** The Book shows no cast or conversion from `comparable`
   to a type (ch. 17 calls it an "abstract interface type"). *Reading:* none
   is supported; `=` is the only operation, its result the left operand.
4. **Relation to `any`.** `comparable` is below `any` and above every
   comparable type. Two comparable types with no other common supertype
   join at `comparable`, not at `any` (ch. 1, ch. 11, ch. 14; test lines
   194-203), and a join that includes a type that is not comparable is
   `any`.
5. **Map keys.** `comparable` is comparable, so `[comparable]v` is a map
   type (`Any.versetest` 66): a key is found by the equality of rule 2.
6. **Overloads.** A parameter of type `comparable` overlaps every
   comparable type (ch. 11, test lines 179-192), so `F(:int)` and
   `F(:comparable)` cannot both be defined; it is disjoint from the types
   that are not comparable.

## Why `any`'s construction does not extend to it

- **`any` keeps no value.** In Verse Core an `any` is `void`: a value
  becomes one by being evaluated, and nothing can be done with it
  ([LANGUAGE.md](../LANGUAGE.md#any)). A `comparable` must keep its value
  for rule 2, so "an `any` restricted to comparable values, with equality"
  has nothing to compare.
- **No Verse Core type holds values of several Core types.** `VTy` has
  `int`, `logic`, `char`, `float`, arrays, tuples, options, type variables
  and references (`OpenVerse/Core/Typing.lean`); no type is inhabited by
  every value. A `[]comparable` holding an `int` and a string needs one.
  (A type variable is instantiated once per call, so it cannot be one.)
- **Core's equality is total but blind to Verse types.** The primitive `eq`
  takes two values of any types and compares them structurally
  (`PrimTy.eq {a b} : PrimTy .eq [a, b] a`; `Prims.lean`), so `int 0` and
  `float 0.0` differ, as rule 2 wants. But several Verse types share a Core
  representation (`Ty.toVTy`, `Front/Types.lean`): an enum value is its
  index (`int`), a `char32` an `int`, every enum's first value `int 0`, a
  struct the tuple of its fields, a `rational` a `tuple(int, int)`, a map
  the array of its pairs, a refinement its base. On values without their
  types, `Equal[letters.A, numbers.One]` would succeed, as would
  `comparable(0u0041) = comparable(65)`, `comparable(map{1 => 2}) =
  comparable(array{(1, 2)})` and a struct `s{X := 1}` against the tuple
  `(1)`; rule 2 says each fails.
- **Generic code does not know its type arguments at run time.** A generic
  function's hidden argument per type parameter is a value of that type,
  which initialises its slots (DESIGN.md, "Generic functions"); an enum's
  is an `int`, indistinguishable from an int's. Converting `X:t` to
  `comparable` in `Equal(X:t, Y:comparable where t:subtype(comparable))`,
  the test file's first definition, needs `t` itself at run time.

So equality across erased values needs the runtime type: the condition for
stopping at a design. The comparable bound's checked evidence (#520,
[upper-bound-evidence.md](upper-bound-evidence.md)) carries dictionaries for
bounds other than `comparable`; `t:subtype(comparable)` is still a flag on
the type parameter, and its evidence has no `Up` into a type that exists.

## Two designs

### A. A Core type of all values, with a type code beside each value

- **Core.** A `VTy.dyn` inhabited by every value (a typing rule: any value
  has type `dyn`; `eq` and `ne` already take operands of any two types),
  with no operation of its own, and a conversion into it that is the
  identity on values: a typing rule (an expression of any type has type
  `dyn`) or a primitive that returns its argument. The type-safety proofs
  (`Core/TypeSafety.lean` and the lemmas over `VTy`) and the checker
  (`Prog.checkTypes`, `Core/TypeCheck.lean`) gain the cases. OVBC carries no
  types ([FORMAT.md](../FORMAT.md)): the format and the C runtime change
  only if the conversion is a primitive (a new primitive number, a one-line
  identity in C).
- **Front end.** A `comparable` is the Core pair `(code, value)`: `code` a
  value that names the Verse type of `value` up to equality (an enum's name,
  `char32` apart from `int`, a struct's name, a map apart from an array;
  ints and their refinements alike, `<unique>` classes as one; array and
  tuple codes normalized so that rule 2's array-tuple equality holds).
  Converting is building the pair; `=` is Core's `eq` on pairs, so map keys
  of `comparable` work as other keys. Containers convert elementwise (a
  `for` over an `[]int`, as the subtype evidence's container `Up`s do).
- **Generic code.** A type parameter declared `subtype(comparable)` that
  is converted to `comparable` needs its code: one more hidden argument, a
  value of the code type, added only to the generic functions that convert
  (and those that call them with their own type parameter), so the bytecode
  of every program that compiles today stays as it is.
- **Joins.** Keep joining at `any`, and type a join at `comparable` only
  where the expected type asks for it (`Arr:[]comparable = array{1, "a"}`),
  so no inferred type of an existing program changes; the Book's inferred
  `[]comparable` without an annotation is a later step, as it changes the
  type of programs that compile.
- **Size.** Core typing and its proofs and the checker, and possibly one
  primitive in OVBC and C: a Core change, an owner decision before any
  code; then a front-end feature of about the size of the subtype evidence's
  container conversions.

### B. Boxes as objects, with no Core change

- A hidden interface `$comparable` with a method `$Eq(Other:$comparable)<decides>`,
  and a hidden class per equality domain (`$comparable:int`,
  `$comparable:letters`, …) holding the value, whose `$Eq` casts `Other` to
  its own class and compares the values. Conversion constructs a box; `=`
  between boxes dispatches.
- Generic code converts through a dictionary: the #520 evidence protocol
  with a `$subtypeEvidence(comparable, t)` whose `Up` boxes, passed for each
  comparable type parameter that is converted, as A's code is.
- Equality of containers of boxes (`array{AsComparable(1)} = array{1}`)
  needs a generated equality per container type, as Core's `eq` compares
  references by identity; converting an `[]int` to a `[]comparable`
  allocates a box per element.
- Map keys of `comparable` cannot be found by Core's map operations, which
  compare keys with `eq` (two boxes of `1` are two references): refused,
  or every map operation on such keys rewritten as a search with `$Eq`.
- **Size.** A large front-end feature (boxes, dispatch, dictionaries,
  container equality and conversions, maps), several times the type
  aliases', and slower values than A's pairs.

**Recommendation.** A, if the owner accepts a Core type `dyn`: it is small
in Core (one type, the identity conversion, the existing total `eq`), keeps
map keys and container equality as they are, and puts the type knowledge
where rule 2 needs it, in a code beside the value. B avoids the Core change
at the cost of a front end several times larger and of map keys.

## The survey's cases

123 cases (all refused, `unknown type 'comparable'`): `Comparable.versetest`
42, `MetatypeConcreteSubtype.versetest` 15 (which also need
`concrete_subtype`), `EnumCompare.versetest` 12, `RollbackTortureTest.versetest`
10, `SOL-5496-CaseCodeBlocksWithoutScopes` 7, `Operators/CompareString` 6,
`SOL-6739-ParametricTypeMeetAndJoin` 6, `Map` 5, `ParametricTypes` 4,
`Operators/BinaryAddArray` 4, `Attributes/unique` 4, `Any` 2, and seven files
with one each. Most need rule 2 across types, and the generic `Equal` of
`Comparable.versetest` needs the runtime type of a type parameter.
