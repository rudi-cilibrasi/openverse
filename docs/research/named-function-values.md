# Function values with named parameters (#503)

Issue [#503](https://github.com/rudi-cilibrasi/openverse/issues/503), found by
the [overloading audit](overloading-conformance.md) (#493). This note pins the
rules OpenVerse implements for function values of functions with named
parameters, and the map from each acceptance item to a minimal program.

## Sources

- The [Book of Verse at `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/06_functions.md),
  chapter 6 (`docs/06_functions.md`), cited below by line.
- The same snapshot's [`Tests/DefaultNamed.versetest`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/DefaultNamed.versetest),
  a copy of the compiler development suite (see the [overloading audit's
  source notes](overloading-conformance.md#sources-and-release-evidence)).
- Retrieved 2026-11-12. No Epic source code was read, and no Epic engine was run.

## Release status

The Book's landing page (`docs/index.md`, lines 18-21):

> The documentation pertains to the head of the main development branch of
> Verse, some features may be discussed before they are officially released
> and are thus subject to change.

Chapter 6 marks its "Nested Functions" section with `!!! warning "Unreleased
Feature"` (lines 1076-1078). Its "Named Parameters" section (lines 28-285) and
its "Types" section carry no such marker. This is **development-branch
evidence**: no released UEFN version is verified to accept these values.

The tests disagree between the two VMs they name in one place: joining two
branches of different named types at `type{_():int}`. The `bp_vm_only` blocks
expect `assert_ir_error(3502, 3502)` and the `verse_vm_only` blocks expect
`assert_valid` (`DefaultNamed.versetest` lines 627-685 and 739-771).

## Quotations

Declaration and calls (chapter 6):

- Lines 38-39: "Named parameters are declared with a `?` prefix and called with
  the name and a `:=` followed by a value".
- Line 70: "After the first named parameter, all subsequent parameters must
  also be named".
- Lines 84-86: "When calling functions with named parameters, you must use the
  `?Name:=Value` syntax. All parameters without default must be specified.
  Positional arguments come first".
- Lines 227-228: "Named parameters are matched by name, not position, so
  reordering does not create distinctness."

Defaults:

- Lines 105-110: "Verse evaluates default values in the function's defining
  scope; they can reference: Module-level definitions; Class or interface
  members; Earlier parameters".
- Line 135: "Default values work with overridden members in class
  hierarchies". Its example's comment, line 143: "The default is read from the
  current instance".
- Lines 476-481, "Evaluation Order": "1. *Positional arguments*: Left to right
  in the call 2. *Named arguments*: Left to right as encountered in the call
  3. *Default values*: Filled in for omitted parameters, left to right in
  parameter order".

Function types:

- Lines 153-155: "Named and default parameters interact with the type system.
  A function with default parameters is a subtype of the same function without
  those parameters". The example (lines 160-173) assigns
  `Process(?Required:int, ?Optional:int = 0)` to `type{_(?Required:int):int}`
  (`F1(?Required := 5) = 5`) and to
  `type{_(?Required:int, ?Optional:int):int}`, and
  `DefaultAll(?A:int = 1, ?B:int = 2)` to `type{_():int}` (`F3() = 3`).
- Line 176: "Function types preserve named parameter names". Lines 190-191:
  `type{_(?Value:float, ?Factor:float):float}` cannot hold
  `Calculate(?Amount:float, ?Rate:float)` ("Invalid: different names").
- Line 194: "Function types do not include default values". Lines 199-201:
  `F1(?X:int=1):int = X` and `F2:type{_(?X:int=99):int} = F1`, commented
  "F1 and F2 are of the same type".
- Lines 1541 and 1555, "Capture": "You cannot take a reference to an overloaded
  function name", "because the compiler cannot determine which overload you
  mean without seeing the call site with arguments".

`DefaultNamed.versetest` makes the type rules concrete:

- Lines 513-519: an unannotated value keeps the function's own named type.
  With `F1(A:int, ?B:int = 0, ?C:int)`, `F := FirstClass.F1` gives
  `F(1, ?C := 2) = 1 + 0 - 2` and `F(1, ?C := 2, ?B := 3) = 1 + 3 - 2`.
- Lines 556-570: `F2(?A:int = 2)` is a `type{_():int}` (`F() = 2`) and a
  `type{_(?A:int):int}`. `F4(A:int, ?B:int = 4)` is a `type{_(:int):int}`
  (`F(5) = 4 + 5`) and a `type{_(:int, ?B:int):int}`.
- Lines 572-612, all `assert_semantic_error(3509)`: a type naming a parameter
  the function lacks (`?B` for `F2`, whether `?B:int` or `?B:int = 0`). A type
  writing `?A:int = 0` when the function requires `?A` (`F1(?A:int)`). A named
  type parameter where the function's is positional.
- Lines 529-535: `type{_(?A:int = 'a'):int}` is an error. A type's default is
  type-checked though it is not part of the type.
- Lines 717-737, `JoinTest`: `F2(F(?A:int = 0):int):int = F() + F(?A := 2)`,
  called with `F6(?A:int = 6)`, gives `6 + 2`. A call through a value of a
  type that writes `?A:int = 0` may omit `A`, and the **value's own** default
  runs, not the type's `0`.
- Lines 802-804: `F(A:[]int, ?B:int = 2)` is a `type{_(:[]int):[]int}`.

## Rules OpenVerse takes

1. **Syntax.** In a function type, `?N:t` is a named parameter and
   `?N:t = e` one that callers of the type may omit. Named parameters come
   after the positional ones. A name may appear once. A positional
   parameter's name (`X:t`) is still not part of the type.
2. **Identity.** Named parameters are part of a function type and match by
   name: `type{_(?A:int, ?B:int):int}` and `type{_(?B:int, ?A:int):int}` are
   one type. Their default expressions are not part of the type.
3. **Subtyping.** A value of function type `s` is a value of type `t` when
   they have the same positional parameters and `t`'s names are among `s`'s.
   Each name of `s` that `t` lacks must be one `s` lets callers omit, and each
   name `t` lets callers omit must be omittable in `s` too. Its effects must
   be among `t`'s, and the parameter and result types are the same. A
   function or method named where a function type is expected fits it on the
   same terms; its own type marks the named parameters with defaults as
   omittable. As before (#214), such a name also fits a closed function type
   by variance: parameter types above the type's and a result below. A value
   of a function type does not convert to another by variance.
4. **Calls.** A call through a value gives the positional arguments, then
   named ones in any order. It must give every name the type requires, and
   may give only names the type has. Explicit arguments run in written order.
   Each omitted default then runs once, at the call, in declaration order and
   in the function's own scope. For a bound method that is its receiver's
   current state and its dynamic class's override.
5. **Bound methods.** The receiver is evaluated once, when the value is made,
   as for methods without named parameters. A method's own type is that of
   the receiver's static class: an override that adds a default makes the
   parameter omittable from a receiver of its class.
6. **Unannotated values.** `F := G` has `G`'s own type, its parameters with
   defaults optional in it.
7. **Capture.** Overloaded functions and methods still cannot be values,
   named parameters or not.

## Readings OpenVerse takes

- **The type's default expression** is not part of the type and never runs,
  but it is checked: at the parameter's type, with literals and top-level
  names only, wherever the type is written (a local, a parameter, a field, a
  module definition), and in a context that cannot fail. The pinned sources
  show only literals (`?X:int=99`, `?A:int = 0`) and refuse a literal of
  another type (`type{_(?A:int = 'a'):int}`, and the same in a signature
  parameter, tests lines 529-535). They say nothing about what else a
  type's default may name. **Open reading:** whether it may also use the
  names in scope where the type is written: locals, earlier parameters,
  members, a generic function's type parameters (`?A:t = …`). OpenVerse
  refuses those with a message that names the rule. Allowing them would
  mean checking each default at its place, with that place's scope, instead
  of at the top level.
- **Joining branches of different named types** at an expected function type
  is accepted (`if (true?) then F2 else F4` at `type{_():int}` gives `2`).
  Each branch is checked against the expected type, as the `verse_vm_only`
  tests expect. The `bp_vm_only` tests refuse it.
- **A function whose named parameter has the function's own name**
  (`F(?F:int)`) cannot be a value. Its value class's method must take that
  parameter by its name, which hides the function in the method's body, and
  the elaborator has no name for a top-level function that a local cannot
  shadow. Making one, a `$`-named forwarding function for each shape the
  value class implements, would add a special case for a rare program, so
  the refusal stays. The Book does not address it.
- **A parameter written as a signature**, `F(:t)<effects>:u` or
  `?F(?A:int = 0):int = G` (chapter 6's "Examples", lines 1013-1023; the
  tests' `Apply(F(:t):u, …)`, `JoinTest`, `FuncFuncDef(?NamedFunc():string =
  HelloFunc)`), is a parameter of that function type, parsed by the same
  signature parser as `type{_…}`.
- Named parameters inside a tuple parameter, and tuples with named elements,
  are not supported; see [tuple-parameters.md](tuple-parameters.md).

## Map

One minimal program per acceptance item. "Before" is `d642ffc`, the main
this work started from; the expected output was derived by hand from the
rules above before running; "now" is the same in the Lean interpreter and
the C runtime. The last column names the test that covers the same rule in
the repository.

| Acceptance item | Minimal program | Before | Expected | Now | Test |
| --- | --- | --- | --- | --- | --- |
| Issue example | `DefaultAll(?X:int=7)<computes>:int=X` as `type{_()<computes>:int}`, called | exit 4: "has named parameters" | `7` | `7` | [named_capture](../../tests/conformance/overloading/named_capture.verse) |
| Retain required names, omit optional (Book example 08) | `Process` as `type{_(?Required:int):int}` and as `type{_(?Required:int, ?Optional:int):int}`; `DefaultAll` as `type{_():int}` | exit 4: a parse error in the type | `5`, `8`, `3` | `5`, `8`, `3` | [book](../../tests/verse/fn_values_named_book.verse) |
| Names are identity (example 09) | `Calculate(?Amount, ?Rate)` as `type{_(?Value:float, ?Factor:float):float}` | exit 4: parse error | refused | refused: expected `type{_(?Factor:float, ?Value:float):float}` | [renamed](../../tests/errors/fn_value_named_renamed.verse) |
| No defaults in types (example 10) | `F1(?X:int=1)` as `type{_(?X:int=99):int}`; `F2()`, `F2(?X := 5)` | exit 4: parse error | `1 5` | `1 5` | [book](../../tests/verse/fn_values_named_book.verse) |
| Overloaded capture stays refused | `F(X:int)` and `F(X:string)` as a value | exit 4 | refused | refused: "an overloaded function cannot be used as a value" | [overloaded](../../tests/errors/fn_value_named_overloaded.verse) |
| Positional and named (example 03) | `Log(Message, ?Level=1, ?Color="white")` at three types | exit 4: parse error | `[Level 1] Hi (red)`, `[Level 1] Starting (white)`, `[Level 3] Error (red)` | as expected | [book](../../tests/verse/fn_values_named_book.verse) |
| Written order | `F(T(1), ?D := T(4), ?B := T(2), ?C := T(3))`, `T` printing | exit 4: parse error | `eval 1`, `eval 4`, `eval 2`, `eval 3`, `1, 2, 3, 4` | as expected | [order](../../tests/verse/fn_values_named_order.verse) |
| Defaults once, at the call, in order and scope | `Make(C, ?A = C.Next(), ?B = A * 10 + C.Next())` at `type{_(:counter):int}` twice, then at a type giving `?A` | exit 4: parse error | `made`, `default 1`, `default 2`, `12`, `default 3`, `default 4`, `34`, `default 5`, `75` | as expected | [order](../../tests/verse/fn_values_named_order.verse) |
| Receiver once, defaults read live state | `MakeGame().CurrentSpeed` (printing `receiver`) called twice; `G.CurrentSpeed` bound, then `set G.DefaultSpeed = 3.0` | exit 4: "a method with named parameters is not a value" | `receiver`, `bound`, `1.0`, `1.0`, `3.0` | as expected | [methods](../../tests/verse/fn_values_named_methods.verse) |
| Inherited and overridden defaults (example 07) | through a `base_game`: `fast_game` overrides the member the default reads, `slow_game` the method's default | exit 4 | `2.0 1.0` | `2.0 1.0` | [methods](../../tests/verse/fn_values_named_methods.verse) |
| Generic | `Pick(X:t, ?Y:t = X)` as `type{_(:int):int}` and `type{_(:string, ?Y:string):string}` | exit 4: parse error | `3 b` | `3 b` | [generic](../../tests/verse/fn_values_named_generic.verse) |
| Escaping | returned from `Make()`, in a field, in an array | exit 4: parse error | `11 3 3` | `11 3 3` | [escape](../../tests/verse/fn_values_named_escape.verse) |
| Failure and rollback | `<decides>` with a write before the failing check | exit 4: parse error | `ok 3 1`, `fail 1`, `ok 9 2` | as expected | [effects](../../tests/verse/fn_values_named_effects.verse) |
| Suspension | `Wait(?Ticks:int = 2)<suspends>` as `type{_()<suspends>:int}` | exit 4: "has named parameters" | `2` | `2` | [effects](../../tests/verse/fn_values_named_effects.verse) |
| Cleanup | a `<suspends>` value's call cancelled by `race`; its default logs, its `defer` prints | exit 4: "has named parameters" | `default`, `cleanup 1`, `after 1` | as expected | [cleanup](../../tests/verse/fn_values_named_cleanup.verse) |
| Required name left out of the type | `Need(?A:int)` as `type{_():int}` | exit 4: "has named parameters" | refused | refused: expected `type{_():int}`, found `type{_(?A:int):int}` | [required](../../tests/errors/fn_value_named_required.verse) |
| Name the function lacks | `F2(?A:int = 2)` as `type{_(?B:int):int}` | exit 4: parse error | refused | refused | [unknown](../../tests/errors/fn_value_named_unknown.verse) |
| Call omits a required name | `F()` for `F:type{_(?A:int):int}` | exit 4: parse error | refused | refused: "needs the argument ?A" | [call_missing](../../tests/errors/fn_value_named_call_missing.verse) |
| Omittable in the type, required by the function | `F1(?A:int)` as `type{_(?A:int = 0):int}` | exit 4: parse error | refused | refused | [optional](../../tests/errors/fn_value_named_optional.verse) |
| Unannotated value (tests 513-519) | `F := F1`; `F(1, ?C := 2)`, `F(1, ?C := 2, ?B := 3)` | exit 4: "has named parameters" | `-1 2` | `-1 2` | [book](../../tests/verse/fn_values_named_book.verse) |
| Names in any order | `Stitch(?First, ?Second)` as `type{_(?Second:string, ?First:string):string}` | exit 4: parse error | `ab` | `ab` | [book](../../tests/verse/fn_values_named_book.verse) |
| Value to value | `G:type{_(?A:int = 0):int} = F6`, then `type{_():int}` and `type{_(?A:int):int}` from `G` | exit 4: parse error | `6 2 6 3` | `6 2 6 3` | [book](../../tests/verse/fn_values_named_book.verse) |
| Through a parameter whose type omits (JoinTest) | `F2(F:type{_(?A:int = 0):int}) = F() + F(?A := 2)` with `F6` | exit 4: parse error | `8` | `8` | [book](../../tests/verse/fn_values_named_book.verse) |
| Bound method at named types, live default | `B.Add(X, ?Extra = Base)` at two types, `set B.Base = 20` | exit 4 | `3 21` | `3 21` | [methods](../../tests/verse/fn_values_named_methods.verse) |
| A type's default of another type (tests 529-535) | `type{_(?A:int = 'a'):int}` | exit 4: parse error | refused (the pinned tests) | refused: expected `int`, found `char` | [type](../../tests/errors/fn_type_default_type.verse), [signature](../../tests/errors/fn_type_default_signature.verse) |
| A parameter written as a signature (ch. 6 example 48) | `Map(Items:[]t, F(:t)<transacts>:u …)`, `Filter`, `Fold` | exit 4: parse error | `5 3 15` | `5 3 15` | [signature](../../tests/verse/fn_values_param_signature.verse) |

## Tuple arguments with named elements

Moved to [tuple-parameters.md](tuple-parameters.md), with the pinned rules.
Destructured tuple parameters are implemented. Named parameters inside them
are refused, with the design question answered there; tuples with named
elements are refused because the Book does not settle them.
