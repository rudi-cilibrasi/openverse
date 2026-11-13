# Empty values, `tuple()` and `=` between different types

The owner decided that openverse follows the Book of Verse on the equality
of empty values, and then that it goes by the Book "for everything for
now". This note pins what the Book says (quoted from the checkout at
[`beaa719`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0),
the revision [the test survey](book-test-conformance.md) uses: chapters by
file and line, tests by file and line), what openverse does now and where
(part 1), and a design for what the front end cannot reach (part 2). No
Epic source code was read.

## 1. What the Book says

### 1.1 One empty value

Chapter 2 (`docs/02_primitives.md`), "void, true, tuple() and false"
(lines 1232 to 1407):

- 1234: "Verse has a single "there is nothing interesting here" value. It
  can be written `false` or `()`, and the types `void`, `true` and
  `tuple()` all describe it." Its example (1251 to 1257): `Nothing:void =
  false`, `Unit:tuple() = false`, `Flag:true = false`, "All the same
  value", `Unit = ()`, `Unit = false`.
- 1261: "`true` is a subtype of `logic`, so the unit value flows into logic
  positions": `Flag:true = false; AsLogic:logic = Flag`.
- 1276: "The empty value also stands in for empty containers. `false` is
  accepted wherever an empty array or map is expected": `Empty:[]int =
  false`, `Empty.Length = 0  # 0 - false is the empty array`, `Empty =
  false`.
- 1294: "`void`/`true` interchange through optionals, arrays and maps":
  `MaybeVoid:?void = option{0}`, `MaybeTrue:?true = MaybeVoid`.
- 1211: "`void` is a function that accepts any value and evaluates to
  `false`"; 1371: "Any value converts to `void`, and that extends through
  containers in ordinary parameter positions"; 1369, "Conversion is
  one-way".
- 829 (and chapter 1, `docs/01_expressions.md` 247): `"" = array{}  #
  Succeeds - empty string equals empty array`.
- Chapter 3 (`docs/03_containers.md` 17): "you use the special constant
  `false`. This is how Verse spells the empty optional".

The tests (`Tests/`) say the same of `=`, in both orders, as values held
in variables of each type: `Operators/CompareArray.versetest` 52 to 58
("Test comparing array{} to other forms of false: false, (), (?t)(false),
map{}, \"\""), `CompareBool` 12 to 18, `CompareMap` 173 to 179,
`CompareOption` 15 to 22, `CompareString` 122, 139 and 184 to 190 (`()=""`,
`""=()`), `Void.versetest` 199 to 206 (an empty `[]int` `= ()`) and 280 to
303 (`X:void = 1` then `X = false`, `false = X`, `X = ()`, `() = X`, `X =
array{}`, `array{} = X`, `X = ""`, `"" = X`). A non-empty value is none of
them: `X:[]int=array{0}; Y:logic=false; X<>Y` (CompareArray 60) and the
like, `X:logic=true; Y:void={}; X<>Y` (CompareBool 20 to 25).

So the empty value is one value of the types `logic` (its false), `void`,
`tuple()`, every option type (its `false`), every array type, `string`
and every map type. `=` between two of these values holds exactly when
both are that value.

### 1.2 Conversions the Book states

Into a type, the empty value is accepted where the Book says so: `false`
at `void`, `tuple()`, `true`, an option, an array; `()` at `tuple()`; a
`void` value at `true` (`Tests/Bugs/FORT-1054384-Void-Any-Meet.versetest`
25: `F1(X:void)<computes>:true = X`); the unit value at `logic` (1261, and
`Void.versetest` 220: `X:logic = if (false?) then true else ()` then `X =
()`); every value at `void`. **Maps:** the prose says `false` is accepted
where an empty map is expected (1276), but the tests refuse it:
`Tests/Map.versetest` 342 to 343, "Test `false` assignment and query throw
expected errors", `assert_semantic_error(3509){ C:=class {var IntMap:[string]int = false }}`,
where `Tests/Array.versetest` 102 to 105 accepts `var IntArray:[]int =
false`. The tests are the compiler's executable expectation, so openverse
takes `false` as an empty array but not as an empty map (it compares equal
to one).

The other direction is not stated: no text or test converts a value of an
array, map or option type to `logic`, or an array to an option. The Book
types statically (`assert_semantic_error(3509)` throughout the tests), and
`[]int` is not a subtype of `logic`; the equality of 1.1 is of values, not
a conversion. openverse converts no such value.

### 1.3 `void`, `tuple()`, `true` and `false` as types

- `void` takes any value and makes it the empty value (1211, 1371);
  `Tests/IndistinctOverloads.versetest` 117 to 134: "`void` is treated as
  equivalent to top - it is a functor accepting `any`", so `F(:int)` and
  `F(:void)` are not distinct overloads.
- `tuple()` is the type of the empty value alone: `Tests/Tuple.versetest`
  10 and 89 to 91 (`X:tuple() = ()`, `MyTuple:tuple() = false`, `MyTuple =
  ()`, `MyTuple = false`); `Void.versetest` 223 to 225 refuses
  `X:tuple() = if (false?) then (1, 2) else false` (3509). As an overload
  it is distinct from `int` (`Tests/ExtensionFields.versetest` 45 to 53:
  `(X:tuple()).Extension()` beside `(A:int).Extension()` and
  `(AB:tuple(int,int)).Extension()`, called as `().Extension() = 42`), and
  not from an array: IndistinctOverloads 93 to 97, "Empty `tuple`s and
  arrays are not distinct".
- `true` describes the same value (1235) and is a subtype of `logic`
  (1261); `?void` and `?true`, `[]void` and `[]true` interchange (1294,
  `Void.versetest` 46 to 80).
- `false` is a value (1235). `Tests/IndistinctOverloads.versetest` 3 to 7:
  "`option` and `logic` are not distinct" (both hold it).

Which may be overloaded beside which: `void` beside nothing; `tuple()`
beside `int`, `float`, `char`, a class, a struct, a non-empty tuple, not
beside a type that holds the empty value (`logic`, an option, an array, a
string, a map). The Book's tests show option/logic, array/map and
`tuple()`/array; openverse applies the reason they give, the common empty
value, to every such pair.

### 1.4 `=` and `<>` between values of different types

Chapter 4 (`docs/04_operators.md`) 359 to 376 lists the comparable types and
says: "Comparisons between different types still compile, but they always
fail": `not (0 = 0.0)`, `not ("5" = 5)`. The tests:
`Operators/CompareTypeChecking.versetest` 23 to 53 (`a:int`, `b:float` or
`b:logic`: `a = b` and `a <> b` are `assert_valid`; the orderings are
3509), `CompareArray` 19 to 21 (`F(A:[]int, B:[]float)` compares,
"Arrays of disjoint comparable types are comparable"), `CompareString` 14
to 40 (`""<>array{0}` and the like), 120 to 151 (a tuple of chars equals
the string of them, `('a','b')="ab"`, and a tuple of ints does not,
`(97, 98)<>"ab"`), `CompareStruct` 40 to 45 (`p(int){X:=0}` is not
`p(float){X:=0.0}`; "structs with the same value but different
representation compare as equal": `p([]int){X:=array{1,2}} =
p(tuple(int,int)){X:=(1,2)}`).

So `=` is equality of values: two values of different types are equal
only when they are one value, which happens for the empty value, a tuple
and the array of its elements, an int and the rational it is, and
containers or structs of such; otherwise the comparison compiles and
fails. Before this change openverse refused it where two scalar types met
(the reading "`=` between different types", now withdrawn).

### 1.5 What the Book does not settle

- Whether `true` is `option{()}` (as in the Verse Calculus, where `logic`
  is `?tuple()`): no text or test compares a logic with a non-empty option.
  openverse: they are different values.
- The value of `X?` for a logic `X`: the operators chapter says "`IsReady?`
  is equivalent to comparing against true" (chapter 4, 396), but the tests
  give `true?` the empty value: `Operators/BoolQuery.versetest` 3
  (`true?=false`), 4 (`not true??`), `LogicalAnd.versetest` 30
  (`(true? and true?) = false`), `Precedence.versetest` 121 (`x := true? or
  true; x = false`). openverse's `true?` is `true` (part 2, 3.1).

## 2. Part 1: what openverse does

### 2.1 The rule

**`=` and `<>` compare values: between two different types, Verse Core's
equality decides where it is Verse's, and otherwise two values are equal
only as the one empty value: types with nothing in common are never
equal, types with only the empty value in common are equal exactly when
both operands are empty, and types with other values in common that Verse
Core holds differently are refused.**

It is one function, `TyEnv.cmpPlan` (`OpenVerse/Front/Elab/Context.lean`),
which `elabCmp` (`Elab/Expr.lean`) asks for every `=` and `<>` of two
different types, single or in a chain:

- `TyEnv.common a b`: what values of `a` and `b` have in common, nothing,
  the empty value only (`Ty.emptyValue?`, `Front/Types.lean`, says which
  types hold it and how Verse Core holds it there: `false`, `()`, `none`,
  `array{}`), or other values (part by part in options, arrays, maps,
  tuples and the fields of one struct at two instances; a tuple and an
  array; an int and a rational; a refinement and its base).
- `TyEnv.coreExact a b`: Verse Core's structural equality is Verse's for
  these types (the same type, part by part; or what they have in common
  Verse Core holds alike and it equates nothing else: `[]int` and
  `string`, whose one common value is `array{}` at both).
- The plan: `core` (Verse Core's `eq`, the code is as before), `never`
  (`neverTest`: `=` fails and `<>` holds after both operands are
  evaluated, as `0 = 1` does: an `int` and a `char32` or an enum, two
  structs of one layout, a rational and a tuple, which Verse Core holds
  alike), `empty` (`emptyTest`: `y` empty and `x` empty for `=`; for `<>`,
  `x` not empty when `y` is), `refuse`.

Around it: an empty `array{}` or `map{}`, which has no type of its own, is
the empty value of the other operand's type (two of them, of `()`'s); a
tuple compared with an array is converted to it, a container of ints to
one of rationals, and a struct at other type arguments field by field
where Verse Core would not compare it as Verse does (`p(tuple(int, int))`
to `p([]int)`), when they convert; two type parameters, or one and a
type several types share in Verse Core, are still refused (generic code,
part 2).

`A:[]int = S:string` is accepted: both hold the empty value, Verse Core
holds it alike (`array{}`) and finds no non-empty values equal, so `core`
decides, and the comparison holds exactly when both are empty, as the
Book says. `array{1} = array{1.0}`, `0 = 0.0` and `0u41 = 65` compile and
fail.

### 2.2 The pair matrix

Every ordered pair of `false`, a `logic` holding false, `()`, a `void`
value, a `tuple()` value, an empty `?int`, `array{}` (typed by the other
operand), an empty `[]int`, `""`, a `string` holding `""`, `map{}` and an
empty `[int]int`, under `=` and `<>`, as a statement (the value of a
`<decides>` function's body) and as an `if` condition, and through
parameters of each type passed the empty value: 772 programs, each run by
the Lean interpreter and by `cverse` (which agree on every one, before and
now). The Book's answer is `y` for every `=` and `n` for every `<>`.

Before (main `d2e26f1`; also `8f7719e`, identical): 200 agree, 388
contradict the Book, 184 are refused. Statement and condition gave the
same verdict on every pair, as did a parameter and a variable. `y` holds,
`n` fails, `r` refused (`array{}` and `map{}` without an array or map
beside them: "the type of an empty array{} must be given"; `[]int` against
`string`: "compares values of different types"); `X <> Y` was the negation
of `X = Y` on every pair that compiled.

| `X = Y`, X down | `false` | `logic` | `()` | `void` | `tuple()` | `?int` | `array{}` | `[]int` | `""` | `string` | `map{}` | `[int]int` |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `false` | y | y | n | n | n | n | r | n | n | n | r | n |
| `logic` | y | y | n | n | n | n | r | n | n | n | r | n |
| `()` | y | n | y | y | y | n | r | n | n | n | r | n |
| `void` | y | n | y | y | y | n | r | n | n | n | r | n |
| `tuple()` | y | n | y | y | y | n | r | n | n | n | r | n |
| `?int` | y | n | n | n | n | y | r | n | n | n | r | n |
| `array{}` | r | r | r | r | r | r | r | r | r | r | r | r |
| `[]int` | y | n | n | n | n | n | y | y | r | r | r | y |
| `""` | y | n | n | n | n | n | y | r | y | y | r | y |
| `string` | y | n | n | n | n | n | y | r | y | y | r | y |
| `map{}` | r | r | r | r | r | r | r | r | r | r | r | r |
| `[int]int` | n | n | n | n | n | n | r | y | y | y | y | y |

Through parameters, before:

| `X = Y`, X down | `logic` | `void` | `tuple()` | `?int` | `[]int` | `string` | `[int]int` |
|---|---|---|---|---|---|---|---|
| `logic` | y | n | n | n | n | n | n |
| `void` | n | y | y | n | n | n | n |
| `tuple()` | n | y | y | n | n | n | n |
| `?int` | n | n | n | y | n | n | n |
| `[]int` | n | n | n | n | y | r | y |
| `string` | n | n | n | n | r | y | y |
| `[int]int` | n | n | n | n | y | y | y |

**Now: all 772 agree with the Book** (`y` for every `=`, `n` for every
`<>`), in Lean and in C. The matrix is openverse's own test
`tests/verse/empty_values.verse` (its expected output written from the
rule, not from a run), with non-empty values against each empty one, the
value of `=` (the left operand) and chains.

### 2.3 What changed in programs that compiled

The oracle (`openverse emit` of every program of `tests/verse`,
`tests/bench`, `tests/conformance`, `tests/upper-bounds` and the frozen
corpus, its bytecode's hash and messages; `openverse check` of
`tests/errors`) against main `d2e26f1`: 5,456 programs in common (4,521
emitted, 935 checked), **5,447 identical**, 9 different, every one listed:

- `tests/verse/empty_literal_compared.verse`, bytecode and output: it
  compares `""` with `()`, a `void`, `false`, a `logic` and an option, all
  empty, and printed `not same`, `differ`, `void ne`, `unit ne`, `rev ne`;
  the Book's answer, which it prints now, is `same`, `not differ`, `void
  eq`, `rev eq`.
- `tests/errors/call_pack_empty_overlap.verse` and
  `overload_shapes_tuple_empty.verse`: still refused, the message names the
  parameter's type `tuple()` where it said `void`.
- New tests: `tests/verse/empty_values.verse`, `different_types.verse` and
  `tuple_type.verse` (main refuses each), `tests/errors/eq_core_values.verse`
  (main refuses it with another message), `overload_map_logic.verse` and
  `tuple_type_value.verse` (main accepts both, which the Book refuses), and
  `eq_nested_empty.verse`.

Test programs changed with the rules, each because its old answer was not
the Book's: the error tests `char32_vs_int`, `float_eq_int`,
`float_eq_nested`, `eq_core_option`, `eq_core_struct`, `eq_core_tuple`,
`rational_nested_eq` and `rational_vs_tuple` expected a refusal of a
comparison the Book compiles; each is now a line of
`tests/verse/different_types.verse` with the Book's answer (all fail but
`array{1} = array{R}` with `R = 2 / 2`, an int and the rational it is).
`tests/verse/call_argument_callee_order.verse` has a `tuple()` function
whose body ended with `set H.F = One`, a function value, which the Book
refuses as a `tuple()` result; it ends with `()` now (main compiles the new
text to the same bytecode as openverse now does). The overload model
(`scripts/models/overload_shapes.py`) says a map and an option overlap.
Lean and C agree on every program, before and now, and on the 772 of the
matrix.

### 2.4 The Book's tests

Against the baseline of main `d2e26f1` (7,180 agree, 2,210 refuse, 308
accept, 85 differ), regenerated from a fresh run: **7,254 agree, 2,164
refuse, 307 accept, 58 differ**, no internal error; 74 cases agree more, none
less ([the survey](book-test-conformance.md#after-the-empty-value)).

- "Empty values are one value" (32): **28 agree**. The 4 left are the value
  of `true?` (`BoolQuery.versetest` 3, 4, `LogicalAnd.versetest` 29,
  `Precedence.versetest` 121): openverse's `true?` is `true`, the tests'
  is the empty value (1.5; part 2).
- "Comparisons of different types" (51 refused): 35 agree; the 16 left
  compare a tuple of a type parameter with a string in generic code
  (`CompareString.versetest` 168 to 182 and `:decls`, part 2).
- Also agreeing: `tuple()` beside `int` (`ExtensionFields.versetest` 48, 70,
  `:decls`), `CompareStruct.versetest:43` (a struct at two instances; it
  compiled and failed), `Void.versetest:223` (`X:tuple() = (1, 2)`, accepted
  before), six empty `array{}` and `map{}` compared with typed values.
- Worse: none agrees less. Two cases moved from a refusal to a different
  result: `FlowControl/for.versetest` 317, 344, `array{} = for(…) {I}`,
  refused before for the untyped `array{}`, now differ by the documented
  rollback of a `for` iteration, whose cause they join.
- Kept agreeing by not following the prose: `Map.versetest:343` (`false` as
  a map, 1.2) and `FORT-582630-BranchResult.versetest:3` (`true` as a type,
  2.5).

### 2.5 `tuple()`

`tuple()` resolves to its own type, `Ty.tup []` (`resolveTy`,
`Elab/Context.lean`), Verse Core's `()` as `void`'s is: no Core type and no
representation change. `Ty.isUnit` names the two types of the empty value
alone. `false`, `()` and a `void` value convert to `tuple()`, a `tuple()`
value converts to `void`, to an array (a tuple is the array of its
elements) and to `logic` as `false` (the Book's `true <: logic`); nothing
else converts to it (`X:tuple() = 1` is refused, as `Void.versetest` 223
refuses `(1, 2)`). Overload domains (`TyEnv.disjointStep`,
`Front/Types.lean`) follow one rule for the empty value: two types that
both hold it overlap (`Ty.emptyValue?`). So `tuple()` is distinct from
`int`, and now also a map overlaps an option and a `logic`, as an array
did (the overload model's `[logic]int`/`?int` row,
`scripts/models/overload_shapes.py`, changed with it).

`true` as a type name is the same type in the Book; openverse does not
take it yet: `Tests/Bugs/FORT-582630-BranchResult.versetest` 3 refuses
`Result:true = branch: Immediate()` (3509), which openverse would accept,
since its `branch:` gives `void`, where the Book's gives its body's type
(`Result:any = branch:` is valid). With `true` the survey gains 4 cases
(`Void.versetest` 177, 253, 267 and its definitions) and loses that one;
the type of `branch:` is concurrency's to settle first.

## 3. Part 2: what the front end cannot reach

### 3.1 What still differs

Where the static types are not both known, or the empty values sit inside
something else, Verse Core's structural equality on today's
representations decides, or the front end refuses:

| Program | openverse | Book |
|---|---|---|
| `array{false} = array{()}` | refused: `[]logic` and `[]void` have values in common that Verse Core holds differently | holds |
| `option{false} = option{()}` | refused (`tests/errors/eq_nested_empty.verse`) | holds |
| `(false, 1) = ((), 1)` | refused | holds |
| `p(t:type) := struct{X:t}`, `p(logic){X := false} = p(void){X := ()}` | refused | holds |
| `p([]int){X := array{1, 2}} = p(tuple(int, int)){X := (1, 2)}` (`CompareStruct` 43) | refused (before: compiled and failed) | holds |
| `IsEmpty(X:t where t:subtype(comparable))<decides>:void = X = false`, `IsEmpty[A]` with `A:[]int = array{}` | fails (Verse Core's `eq` of `array{}` and `false`) | holds |
| `Same(X:t, Y:u where t:subtype(comparable), u:subtype(comparable))<decides>:void = X = Y` | refused: two type parameters | compiles; holds for `false` and `array{}` |
| `DoesTupleEqualString(A:tuple(t,t,t), B:string …) = A = B` (`CompareString` 167 to 182) | refused | compares as values |
| `true? = false` (`BoolQuery` 3, `LogicalAnd` 30, `Precedence` 121; `not true??`, `BoolQuery` 4) | fails: `true?` is `true` | holds: `true?` is the empty value |
| `comparable` and `any` values | `comparable` is not a type yet ([comparable-type.md](comparable-type.md)); `any` has no `=` (as the Book: ch. 11) | `comparable(false) = comparable(array{})` would hold |

Map keys and `case` are not affected today: a map's keys and a `case`'s
patterns are taken at one type (the key type, the scrutinee's), where each
value has one representation. They would be with `comparable` keys or
scrutinees.

The `never` and `empty` plans of 2.1 that are not about empty values
(`0u41 = 65`, `[]int` against `[]char32`) stay in the front end under both
designs below: they come from different types that Verse Core holds alike,
which only runtime types (the `comparable` design) could take into Core.

### 3.2 Design A: one representation

Every empty value is one Verse Core value `ε` (`Value.void`, `.tup []`):
`false` at `logic`, the empty option, and the empty array, string and map
become `ε`; arrays are `ε` or a non-empty `.arr`, options `ε` or `.some v`,
logics `ε` or `.logic true`. Options still nest (`option{false}` is
`.some ε`, `false` at `??int` is `ε`), so a `?[]int` still tells `false`
from `option{array{}}`, as the Book's nested options require (chapter 8,
`Outer:??int = false`, `not Outer??`).

What changes:

- `Value.lean`: the invariant (no `.arr #[]`, no `.none`, no `.logic
  false`), kept by `ofArray`/`ofArrayCached` (which already share one empty
  array) and by every operation that builds an array; `decEq` unchanged.
- `Prims.lean`: every array operation must take `ε` as the empty array
  (`len`, `index`, `concat`, `arrSet`, `flatten`, `toStr`, the slices),
  `query` fails on `ε`, `mkSome` unchanged.
- `Typing.lean`: `hasTy ε τ` for `τ` = `logic`, `?t`, `[]t`, `tuple()`;
  `VTy.default`; `litTy` of `ε` (no type of its own, as `none` and the
  empty array have now).
- Proofs: `TypeCheck.lean` (`litTy_sound`, `litTys_sound`,
  `tcPrim_sound_of`, `tc_sound_aux`, `checkDefault_sound`,
  `checkHeapOK_sound`, about 6), `TypeSafety.lean` (the inversion lemmas
  `hasTy_logic`, `hasTy_arr`, `hasTy_opt`, `hasTy_tup`, `hasTy_sub`,
  `hasTy_subst`, `allTys_sub`, `hasTy_mono`, `toStr_typed`, every array
  case of `prim_typed`, `DefaultE.eval_ok`, `stepE_rule`'s `for` cases,
  about 14), `Derived.lean` (`optionE_*`, `logicE_*`, `evalFor_allFail`,
  `chooseFirst_none`, about 10), `Value.lean` (4), `Adequacy.lean` (2
  case splits), `Interp.lean` and `Bounded.lean` (the `for` over `ε`).
  `Prog.checkTypes` follows `tc`.
- OVBC: the encoder writes `ε` as `VOID`; `NONE`, `LOGIC 0` and `STR ""`
  would no longer be written (the loader may keep reading them, mapping to
  `ε`, so `load.c` and its QuickProof stay; if the kinds are removed
  instead, `Specs.v`'s bound `n_op x <= 6` and `Lit.v` are re-proved).
- C runtime: the four tags of an empty value (`LOGIC`/`NONE`/`ARR`/`TUP`
  with bits 0) become `TUP`, 0; every primitive on arrays (`prims.c`),
  `query`, the `for` loop (`interp.c`) and `toStr` take it.

What it simplifies: Verse Core's `eq` is Verse's for every empty value,
nested or generic, so `cmpPlan`'s `empty` plan for different
representations, and the refusals of 3.1's first four rows, go; `Ty.
emptyValue?` becomes one value. What stays: `never` and the `empty` plan
of types Verse Core holds alike (3.1, last paragraph), and the tuple
against array of `CompareStruct` 43.

Cost: about 36 theorems, every array primitive in Lean and C, the
encoder, the C literal evaluation, and the risk of an `.arr #[]` built
somewhere the invariant was not kept (a fuzzer of every primitive on
empty inputs, Lean against C, would be needed).

### 3.3 Design B: an equality that relates them

Verse Core's `eq` and `ne` compare by `Value.veq`: structural equality in
which any two of `.logic false`, `.tup []`, `.none` and `.arr #[]` are
equal, at every depth. Representations, typing, OVBC and the loader do
not change.

- `Value.lean`: `Value.isEmpty` (the four), `Value.veq` (if both are
  empty, true; else structural, with `veq` on the parts; as `decEq` is
  written, mutual with its list and array versions), and the lemmas
  `veq_refl`, `veq_symm`, `veq_trans` (an equivalence, so a map's lookup
  by `eq` is well defined), `veq_of_eq`, and `veq_int : veq v (.int j) =
  decide (v = .int j)` (a non-empty scalar is related only to itself).
- `Prims.lean`: `.eq` is `cmpRes (veq a b) a`, `.ne` is `cmpRes (!veq a
  b) a`; `PrimTy.eq`/`ne`, `tcPrim` and `prim_typed` (which only use the
  left operand's type) do not change.
- `Derived.lean`: `Eval.eq_slot`'s statement says `veq`; `altFrom_sel` and
  `altE_sel` rewrite with `veq_int`. These 3 are the only theorems that
  read `eq`'s result (the inventory: `TypeSafety.lean` 0,
  `TypeCheck.lean` 0).
- C runtime: `shallow_eq` (`runtime/src/value.c`) returns equal when both
  values are empty (tag `LOGIC`, `NONE`, `ARR` or `TUP` and the object
  empty: bits 0, which every empty array and tuple has, heap cell 0), before
  its tag test; `vx_equal` then descends as before. No proof covers
  `value.c` (the QuickProof laws are `arith`, `store` and the loader).
- Hashing: none exists (maps are scanned with `eq`, `mapLookup`); a later
  hash must give the four the same hash.
- The front end: `TyEnv.coreExact` takes Verse Core's new equality (an
  `empty` common value is then exact when no non-empty values could be
  equal), so `cmpPlan`'s `empty` plan remains only for types Verse Core
  holds alike (`[]int` against `[]char32`), and the refusals of 3.1's
  first four rows and the generic `IsEmpty` row become Verse's answer. The
  bytes of programs comparing two empty-capable types change (the
  `emptyTest` code becomes a plain `eq`); each is listed by the oracle.

A tuple and an array (`CompareStruct` 43) could be related the same way
(`veq (.tup xs) (.arr ys)` part by part), but Verse Core also holds
structs, rationals and class values as tuples, so `coreExact` would have
to treat a tuple and an array as overlapping everywhere; that is a second
step, not part of B.

### 3.4 Recommendation

**Design B.** It gives the Book's answer for every empty value Verse Core
compares, nested and generic, with one definition, two primitive cases,
three theorems and five lemmas in Lean, one test in C, and no change to
OVBC, the loader or its proof; Design A gives the same answers at about
ten times the proof work and touches every array primitive in both
implementations, for no difference a program can see. Sizes: B, 3 Lean
files (`Value.lean`, `Prims.lean`, `Derived.lean`) and `value.c`, plus the
front end (`Context.lean`) and tests: about 5 new lemmas and 3 changed
theorems. A, about 12 Lean files, 4 C files and `Encode.lean`: about 36
changed theorems.

Step order for B, each keeping `scripts/check.sh` green:

1. `Value.isEmpty`, `Value.veq` and its lemmas, unused.
2. `.eq`/`.ne` by `veq` in `Prims.lean` and `shallow_eq` in C together
   (Lean and C must agree on every test); `Derived.lean`'s three theorems.
   Tests: nested empty values (`option{false} = option{()}` through a
   generic function, which the front end does not refuse), Lean against C.
   `docs/CLAIMS.md` regenerated.
3. The front end: `coreExact` with Verse Core's new equality; the
   refusals of 3.1 become comparisons; the oracle lists the programs whose
   code shrinks.
4. `LANGUAGE.md`, `DESIGN.md`, `FORMAT.md` (the meaning of `eq`).

Separately, in the front end: the value of `X?` on a logic (the Book's
tests: the empty value, so `X:logic = true?` would be `false`), and `true`
as a type name once `branch:` has its body's type.
