# Destructured tuple parameters and named elements in them

The rules OpenVerse takes for parameters that destructure a tuple, the design
question for named parameters inside such a group, and the map for both.

## Sources

- The [Book of Verse at `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/06_functions.md),
  chapter 6, "Tuple as Arguments" (`docs/06_functions.md` lines 287-425) and
  "Flattening and Unflattening" (lines 427-472).
- The same snapshot's tests: [`NestedTupleParameters.versetest`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/NestedTupleParameters.versetest),
  [`NestedNamedTupleParameters.versetest`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/NestedNamedTupleParameters.versetest)
  and [`DefaultNamed.versetest`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/DefaultNamed.versetest).
- Retrieved 2026-11-12. No Epic source was read and no Epic engine was run.

**Release status.** These sections carry no "Unreleased Feature" marker (the
chapter's "Nested Functions" does). The Book's landing page says it documents
"the head of the main development branch of Verse", so this is
development-branch evidence; no released UEFN version is verified.

## Quotations

- Lines 315-317: "Functions can destructure tuple parameters directly in the
  parameter list, allowing you to extract tuple elements inline without
  manual indexing". Its example, `Func(A:int, (B:int, C:int), D:int)`, is
  called three ways: `Func(1, (2, 3), 4)` ("Direct tuple literal"),
  `Func(1, X, 4)` with `X := (2, 3)` ("Tuple variable") and `Func(Y)` with
  `Y := (1, (2, 3), 4)` ("Entire argument list as tuple"), each `= 10`.
- Lines 333-335: "The parameter `(B:int, C:int)` destructures the tuple,
  giving direct access to `B` and `C` instead of requiring `Tuple(0)` and
  `Tuple(1)` indexing."
- Line 337: "Tuples can be destructured to arbitrary depth".
- Lines 348-349 and 362: "You can mix destructured tuple parameters with
  regular tuple parameters that are not destructured", and of
  `F(A:int, (B:int, C:int), D:int)` and `G(A:int, T:tuple(int, int), D:int)`:
  "Both work identically".
- Lines 367-369: "Choose destructured form when you need direct access to
  individual elements, and non-destructured when you need to pass the tuple
  as a whole to other functions."
- Lines 468-472: "Because of automatic flattening and unflattening, you cannot
  define overloads that would be ambiguous. If you define
  `F(P:tuple(int, int))`, you cannot also define `F(X:int, Y:int)`".
- Lines 371-373: "Tuple parameters can contain named/optional parameters,
  allowing for flexible APIs that combine structural decomposition with
  optional values". Lines 386-387: "A tuple can contain multiple named
  parameters, and they can be specified in any order".
- Lines 400-402 and 423-425: "When a tuple parameter contains **only** named
  parameters (no positional parameters), you must provide an empty tuple `()`
  even when using all defaults", with `Configure(5)` marked "ERROR - tuple
  parameter required", and "This is a known limitation in the current
  implementation. When the tuple contains at least one positional
  parameter, this restriction does not apply."
- Lines 289-291: "you cannot mix a pre-constructed tuple variable with
  additional named arguments".

The tests add:

- `NestedTupleParameters` lines 76-99: four functions mixing groups, nested
  groups and tuple parameters, each called with literals, tuple variables
  and the whole argument list as one tuple (`I(T4) = 45`). Lines 21-43: a
  `<suspends>` function with groups, spawned. Lines 45-49: a refinement
  inside a group is refused.
- `NestedNamedTupleParameters` lines 20-23: `SumFour(A:int, (X:int, (Y:int,
  (Z:int))))`, called `SumFour(1, (2, (3, (4))))`. A group of one parameter
  takes one value: `(4)` is 4.
- Named elements, same file: `SumThree(U:int, (?X:int=1, ?Y:int=1))` gives
  `SumThree(1, ()) = 3` and `SumThree(1, (?X:=2, ?Y:=3)) = 6`.
  `SumFourNamed(A:int, (X:int, (Y:int, (?Z:int=0))))` gives
  `SumFourNamed((1, (2, (3)))) = 6`, the last group fed one value.
  `SumFourArray(A:int, (U:[]int, ?X:int=1, ?Y:int=1))` takes
  `(1, array{100, 2})` or `(1, (X, ?Y:=1, ?X:=1))`.
- Two known bugs, asserted as errors (lines 157-172): JIRA SOL-6937,
  "Undesirable language behaviour where a tuple of named-args requires an
  empty tuple to be passed in" (`SumThree(1)`), and JIRA SOL-6939,
  "SemanticAnalyzer fails to Constrain single named args to tuples params in
  same way unnamed args do to unnamed tuples" (`SumThree(1, (?X:=2))`).
- `DefaultNamed` lines 489-501: a tuple value with named elements,
  `(0, ?A := 1, ?B := 2)`, is refused when indexed or passed on
  (`assert_semantic_error(3640, 3640, 3509)`). Lines 537-546 comment out
  passing one to `Apply(F(:t):u, X:t)` as a VM bug.

## Rules OpenVerse takes for destructuring (implemented)

1. A parenthesized group of two or more parameters is one parameter of their
   tuple type. Groups nest, giving nested tuple types. A group of one
   parameter is that parameter, as `(4)` is 4 and a tuple of one element
   cannot be made. An empty group is refused: write a `tuple()` parameter.
2. The body sees each name of a group bound to its element, from the start.
   Verse has no shadowing, so the body cannot declare it again.
3. Everything else sees a tuple parameter there, as the Book's "Both work
   identically" says: calls (a tuple literal, a tuple variable, the whole
   argument list as one tuple), overload distinctness, function values (its
   type is the one with a tuple parameter there), `spawn`, methods,
   constructors and generic functions.
4. A later parameter's default may use a destructured name, as it may use an
   earlier parameter (Book lines 105-110). That a destructured name counts as
   an earlier parameter here is a reading; the Book shows no such default.

The parser makes a group a parameter `$tuple{i}` of its tuple type. It
starts the body (or a constructor's items, as a `let:`) with the bindings
`B := $tuple1(0)`, nested as `D := $tuple1(1)(1)`. It rewrites later defaults
the same way. Nothing after the parser knows about groups.

## Named parameters inside a group: the design question

The question was whether a group with named elements, "positional parts,
then names, some omittable", is the notion function shapes already have
(#503: `FnValues.Shape`, sorted names and omittable ones, `Shape.within`),
one level down.

**As a description it is the same.** `(Value:int, ?Factor:int = 1, ?Offset:int
= 0)` has one positional part and two omittable names, matched by name, and
`Shape.within`'s rule says which supplied arguments fit it. One structure
(positional count, sorted names, the omittable ones) should describe both.

**As a mechanism it is not, and it needs a new type.**
- A function shape is an interface. Its omittable parameters cost nothing at
  run time, because the call dispatches to the function and the function's
  own defaults fill in what the call left out.
- A group is data that a caller builds and the callee takes apart. If a
  caller writes `(5, ?Factor := 2)`, the callee must learn that `Offset` was
  left out, so that it can run `Offset`'s default. Telling "supplied" from
  "left out" needs a representation with optional elements (`option{2}` and
  `false`). The caller must also build that value by name, from a tuple
  literal written in any order, from a bare value (`Scale(10, 5)`) or from a
  tuple variable.
- So a tuple type with named, omittable elements has to enter the type
  language. Coercion has to convert into it by name, and every path of the
  call machinery has to supply it: ordinary, method, generic, overloaded,
  choice-inlined and spawned calls, constructors, and calls through values.
- Within the existing call machinery the alternative is to match a group's
  argument as a nested argument list on each of those paths. That costs as
  much and still leaves function values and overloads without a type for the
  group.

As instructed, OpenVerse stops here. A group with a named parameter is
refused: "a named parameter inside a tuple parameter (?Z) is not supported
yet".

**What it would take**, for the owner to decide:
1. Factor the parameter part of `FnValues.Shape` (positional, names, omittable,
   `within`, `select`) into one structure, used by function shapes and by the
   new tuple type.
2. A named tuple type: `STy.tup` with `STy.namedParam` elements, as function
   types write them, and a `Ty` form. In Verse Core it is a tuple: positional
   elements, then names in order, an omittable one as an option.
3. `coerce` into it from a tuple literal with named elements, a tuple value or
   a bare value (one positional element). Required names must be given, and
   unknown ones are refused. Subtyping goes by name, as `Shape.within` does.
4. The callee's prelude runs an omitted element's default when the option is
   `false`: in declaration order, in the function's scope, after every
   explicit argument. That is later than a top-level default the caller fills
   in, a difference from the Book's single "defaults left to right" order
   that would have to be accepted or engineered away.
5. Parse tuple literals with named elements wherever a named tuple type is
   expected. Keep the pinned errors: `Configure(5)` (SOL-6937) and
   `SumThree(1, (?X:=2))` (SOL-6939).
6. Unsettled, to be decided rather than guessed: how such a function's type
   is written as a value, and how its group counts for overload
   distinctness.

## Map

"Before" is main `6ffd968`; "expected" is derived from the pinned sources; "now"
agrees in the Lean interpreter and the C runtime.

| Program | Before | Expected | Now |
| --- | --- | --- | --- |
| `Func(A:int, (B:int, C:int), D:int)` called with a literal, a variable, the whole list | exit 4: "expected an identifier, found '('" | `10 10 10` | `10 10 10` |
| `H(A:int, (B:int, (C:int, D:int)), E:int)`, three call forms | exit 4, as above | `15 15 15` | `15 15 15` |
| `I(…)` with two nested groups, five call forms (tests 76-99) | exit 4, as above | `45` each | `45` each |
| `SumFour(A:int, (X:int, (Y:int, (Z:int))))` | exit 4, as above | `10 10` | `10 10` |
| A spawned `<suspends>` function with groups | exit 4, as above | `10` | `10` |
| A group and a tuple parameter of the same types, overloaded | exit 4, as above | refused: indistinct | refused: "defined twice with parameters a call cannot tell apart" |
| A default using a destructured name, `((A:int, B:int), ?C:int = A * 10 + B)` | exit 4, as above | `12 7` | `12 7` |
| A function with a group as a value, `type{_(:int, :tuple(int, int), :int):int}` | exit 4, as above | `10` | `10` |
| A method, a constructor, a generic function with groups | exit 4, as above | as written | as written |
| `SumValues(A:int, (X:int, (Y:int, ?Z:int = 0)))`; `SumValues(1, (2, (3, ?Z := 4)))`, `SumValues((1, (2, 3)))` | exit 4, as above | `10 6` | refused: named parameter inside a tuple parameter |
| `Scale(Base:int, (Value:int, ?Factor:int = 1, ?Offset:int = 0))`, three calls | exit 4, as above | `15 21 21` | refused, as above |
| `Configure(Base:int, (?Width:int = 10, ?Height:int = 20))`; `Configure(5, ())` | exit 4, as above | `35` | refused, as above |
| `Configure(5)` | exit 4, as above | refused (the known limitation) | refused, as above |
| `X := (0, ?A := 1, ?B := 2)` | exit 4: "unexpected '?'" | unsettled | refused: "a tuple with a named element (?Name := …) is not supported: the pinned Book of Verse does not settle such values, …" |
| `Calculate(Args, ?C := 5)`, `Args:tuple(int, int)` | `8` | refused by the Book (lines 289-291) | `8`, unchanged: an OpenVerse extension the overloading audit records |
