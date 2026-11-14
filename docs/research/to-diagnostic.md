# `ToDiagnostic`: what the Book asks, and what openverse would need

`ToDiagnostic` is the cause of 93 refusals of the Book of Verse's tests
(`Tests/Intrinsics/ToDiagnostic.versetest`), the largest library cause left
([the map of forms](book-test-conformance.md#forms-of-expressions-statements-and-the-library-a-map)).
This note pins what the Book says, sorts the cases by what each needs, and
says what is built: an `any` that keeps what it needs to print itself, in
the programs that call `ToDiagnostic` only, and the printers of every type
but floats, which need a shortest round-trip float printer, Verse Core's
and the C runtime's (left). Revision
[`beaa719`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0);
no Epic source code was read.

## What the Book says

- **The API reference**: `ToDiagnostic<public><native>(Value:any)<predicts><reads>:diagnostic`,
  "Accepts any value at all. For objects whose class implements the internal
  diagnosable interface it delegates to that class's own GetDiagnostic … and
  everything else goes through the runtime's generic value printer";
  `diagnostic<public><native> := class<epic_internal><computes>(diagnosable)`
  with `String<native><epic_internal>:string`, "An opaque string wrapper that
  is deliberately write-only from Verse … cannot read the text back out or
  compare two of them"; `diagnosable<epic_internal><native> := interface<computes>`
  with `GetDiagnostic()<reads>:diagnostic`.
- **The prose**, ch. 2 (`02_primitives.md:867-884`): the format "may vary
  between VM implementations".
- **The tests** read `ToDiagnostic(V).String` (Epic's own code may: the field
  is `<epic_internal>`), and pin the format: `false`, `true`; ints in
  decimal; rationals reduced, `1/2`, `-2/3`; floats in the shortest form that
  reads back, `1.0`, `1.2345678901234567`, `1e+100`, `1.234e+101`,
  `1.7976931348623157e+308`, `5e-324`, `Inf`, `NaN`; chars `'a'`, `'\\t'`,
  `0o00`, `0o7f`, char32 `0u9`, `0u1f600`; strings quoted and escaped, an
  invalid UTF-8 byte as `{0oXX}`, a valid sequence that is no printable
  character as `{0uXXXX}`; `option{1}` and `false` for an empty one; an
  array of one element `array{1}`, of several `(1, 2)`; tuples `(1, 2, 3)`;
  maps `map{0.0 => 1, 1.0 => 1}`; an object `(/Verse.org/VerseTests:)my_class{X := 10}`,
  an enum's value `(/Verse.org/VerseTests:)e.A`, a struct
  `(/Verse.org/VerseTests:)s{X := 10, Y := 11.1}`, a function
  `(/Verse.org/VerseTests:)GlobalFunction(:float)`; a `diagnosable` object
  its `GetDiagnostic`'s text.

## The cases, by what each needs

Every case passes its value through a parameter `Value:any`
(`TestDiagnosticString(Value:any, ExpectedString:string)`, `:5`; the
classes' `:149`): a `ToDiagnostic` over the types known where it is called
reaches none of them. Of the 93:

| Needs | Cases |
|---|---|
| an `any` that keeps its value, and a printer of each type, only | 60: booleans (2), ints in 64 bits (10), rationals (10), chars, char32s and strings (24), options without floats (4), arrays and tuples without floats (6), a map of tuples (1), `diagnosable` objects (2), a diagnostic's diagnostic (`:235`) |
| and the shortest round-trip float printer | 18: floats (9), and floats inside an option, an array, maps, an object and structs (9) |
| and the test runner's package path, `(/Verse.org/VerseTests:)` | 13 (4 with floats): objects (4), enums' values (2), structs (3), functions (4: `GlobalFunction`, a method, twice by VM, and `ToDiagnostic` itself, `(/Verse.org/Verse:)`) |
| ints past 64 bits (`verse_vm_only`) | 6 (`:35-40`): different results under the Blueprint VM's ints openverse has |

(The 18 assertions on type values, `:215-232`, are not translatable: their
function selects a string by VM inside its body.)

## As built

**An `any` that prints itself, where `ToDiagnostic` is called.** A program
whose source names `ToDiagnostic` (the parser's marker `$uses:diagnostic`)
and defines none of `ToDiagnostic`, `diagnostic` and `diagnosable` gets the
helpers of `Front/Diagnostic.lean`, Verse source: the interface
`$anything` with `$Diagnose()<reads>:string`; `$anyEmpty`, below it, the
empty value's class; `diagnosable := interface<computes>` with
`GetDiagnostic()<reads>:diagnostic`; `diagnostic := class<computes>(diagnosable)`
with `String<public>:string` and a `GetDiagnostic` that gives itself;
`ToDiagnostic(Value:any)<reads>:diagnostic`; and the printers of strings,
chars, char32s and rationals. Then, and only then (`TyEnv.anyWraps`, the
helpers' interface being in the program), an `any` is `$anything`'s
reference in Verse Core, and a value of type `t` converted to `any` is an
object of `$any_t`, a class below `$anything` with one field holding the
value, whose `$Diagnose` calls `$diag_t`, the printer of `t`
(`Context.wrapAny`, `Diagnostic.wrapperDecls`). The classes and printers
are asked for by the conversion (`Requests.anys`) and added in the next
round of elaboration. Verse Core, its proofs, OVBC, `openverse.h`,
`load.c` and the runtime are unchanged.

**What `any` is there, and what differs.** Everything a program can do
with an `any` in openverse is unchanged: it is converted to (every
conversion, `convert`'s `_, any`, which the joins at `any`, `[]any`, `?any`,
maps' and tuples' elements, function values' adapters and `any(X)` all
reach), passed, stored, returned and discarded, and it still has no
equality, no `ToString`, no cast back (`c[X]` of an `any` is refused, as
before) and no conversion to `comparable`. A generic function at `t :=
any` takes the object as it is (its hidden witness of `t` a slot of type
`any`, which starts as a `$anyEmpty`). What differs, in such a program
only:
- a conversion to `any` allocates an object (the wrapper); a value already
  an `any` is not wrapped again;
- the conversion is refused, where it is written, for a type no printer
  prints yet: a float, or a value holding one (an option, an array, a
  map, a tuple, a struct's or an object's field); a `comparable` (a box,
  whose type no Verse code reads); a value of a type parameter, in
  generic code (its type is known only to the caller; a generic function
  instantiated at `any` is no such case); a weak map; a type as a value;
- an object's `var` fields are printed when `ToDiagnostic` runs, as the
  API's `<reads>` says, not when the conversion did.

Every program that does not call `ToDiagnostic` keeps its bytes: over the
suites and the corpus `corpus2` (5,944 programs), none changed.

**The alternative** (a typed `ToDiagnostic` overload set for statically
known types, and a refusal through `any`) would agree on no case: every
case passes its value through `Value:any`.

## The format, per type

Each from the tests, `Tests/Intrinsics/ToDiagnostic.versetest`, by line;
the prose gives none (ch. 2, `02_primitives.md:882-884`: "The exact format
it produces may vary between VM implementations").

| Type | openverse | The Book's tests |
|---|---|---|
| `logic` | `false`, `true` | `TestDiagnosticString[false, "false"]` (`:13`), `[true, "true"]` (`:14`) |
| `int` | decimal, `-` | `[4294967296, "4294967296"]` (`:29`), `[-Value, "-{ExpectedString}"]` (`:20`) |
| `rational` | reduced, `N/D`, an integral one as its int | `[2/4, "1/2"]` (`:61`), `[-2/-4, "1/2"]` (`:62`), `[0/2, "0"]` (`:59`), `[-1/SeedPrime, "-1/{ExpectedSeedString}"]` (`:54`), `[SeedPrime/1, "{ExpectedSeedString}"]` (`:46`) |
| `float` | refused (left) | `[1.5, "1.5"]` (`:79`), `[1e100, "1e+100"]` (`:83`), `[12.34e100, "1.234e+101"]` (`:84`), `[NaN, "NaN"]` (`:76`), `[Inf, "Inf"]` (`:87`), `[FloatConstants.SmallestSubnormal, "5e-324"]` (`:86`) |
| `char` | printable ASCII quoted, escapes as a string's, else `0oXX` | `[0o00, "0o00"]` (`:91`), `['a', "'a'"]` (`:92`), `['\t', "'\\t'"]` (`:93`), `['\#', "'\\\#'"]` (`:94`), `[0o7f, "0o7f"]` (`:95`) |
| `char32` | `0u` and lowercase hex | `[0u20, "0u20"]` (`:98`), `[0u1f600, "0u1f600"]` (`:100`) |
| `string` | quoted; `\t`, `\n`, `\r`, and `" # & ' < > \ { } ~` escaped; a valid UTF-8 sequence of 2 to 4 bytes `{0uX}`; a byte of no valid sequence (overlong, surrogate, past `10ffff`, cut short) or a control character `{0oXX}` | `["\t\n\r\"\#\&\'\<\>\\\{\}\~", …]` (`:105`), `["{0o08}{0o09}{0o0a}{0o0b}", "\"\{0o08\}\\t\\n\{0o0b\}\""]` (`:106`), `["Smiley face: 😀, …", "…\{0u1f600\}…"]` (`:107`), `["{0odf}{0o00}", "\"\{0odf\}\{0o00\}\""]` (`:110`), `["{0of4}{0o8f}{0obf}{0obf}", "\"\{0u10ffff\}\""]` (`:116`) |
| `?t` | `option{X}`, empty `false` | `[option{false?}, "false"]` (`:123`), `[option{1}, "option\{1\}"]` (`:124`) |
| `[]t` | one element `array{X}`, else `(X, Y)`; none `()` (not pinned) | `[array{1}, "array\{1\}"]` (`:131`), `[array{1,2}, "(1, 2)"]` (`:132`), `[array{array{1,2},array{3,4}}, "((1, 2), (3, 4))"]` (`:135`) |
| tuples | `(X, Y)` | `[(1,2,3), "(1, 2, 3)"]` (`:137`), `[((1,2),(3,4)), "((1, 2), (3, 4))"]` (`:138`) |
| `[k]v` | `map{K => V, …}`, in its order; empty `map{}` (not pinned) | `[map{(0,0)=>0,(1,1)=>1,(2,2)=>2}, "map\{(0, 0) =\> 0, …\}"]` (`:145`) |
| enums | `e.A` | `[e.A, "(/Verse.org/VerseTests:)e.A"]` (`:180`) |
| structs, objects | the name without type arguments, the fields in declaration order, `X := V`; an object's own class (by casts from the most derived class), a module member qualified `(M:)c` (not pinned) | `[s{X:=10,Y:=11.1}, "(/Verse.org/VerseTests:)s\{X := 10, Y := 11.1\}"]` (`:187`), `[my_class{X:=10}, "(/Verse.org/VerseTests:)my_class\{X := 10\}", …]` (`:159`), `[my_parametric_class(int){X:=0}, "(/Verse.org/VerseTests:)my_parametric_class\{X := 0\}", …]` (`:166`) |
| `diagnosable` objects | their `GetDiagnostic()`'s `String` | `[class_with_diagnostic_string{DiagnosticString:="Object1"}, "Object1"]` (`:173`); a diagnostic's diagnostic is itself: `[ToDiagnostic("test"), "\"test\""]` (`:235`) |
| functions | the name and the parameter types at the value's type, `F(:float)`; a method `(c:)M(:int)` (not pinned: the VMs differ); the language's own `(/Verse.org/Verse:)` | `[GlobalFunction, "(/Verse.org/VerseTests:)GlobalFunction(:float)"]` (`:199`), `[ToDiagnostic, "(/Verse.org/Verse:)ToDiagnostic(:any)"]` (`:200`), `bp_vm_only` `"Object3.(/Verse.org/VerseTests/class_with_method:)Method(:int)"` and `verse_vm_only` `"(/Verse.org/VerseTests/class_with_method:)Method(:int)"` (`:201-202`) |
| `void`, `tuple()` | `false` (not pinned) | |
| types as values | refused (left) | `:215-232`, not translatable (their function picks a string by VM in its body) |

openverse's top level has no path, so a definition there is printed with
no qualifier; the tests print the test runner's package,
`(/Verse.org/VerseTests:)`: the harness takes a case whose expected string
names it as not translatable (`booktests.py`, as for that path written as
a qualifier).

## The cases

Of the 93 refused before, with the harness's change: **62 agree** (the
booleans 2, the ints 11, the rationals 10, chars, char32s and strings 24,
options 4, arrays and tuples 6, the map of tuples 1, `diagnosable` objects
2, a diagnostic's diagnostic 1, `ToDiagnostic` as a value 1); **14 stay
refused**, the floats (9 alone, `:75-87`; 5 inside an option, an array and
maps, `:125`, `:134`, `:142-144`), each refused as above; **5 differ**,
`verse_vm_only` ints past 64 bits (`:36-40`, cause int-precision: their own
operands overflow, openverse's int reading, as the 82 int-precision cases
before them); **12 are not translatable** now (the runner's package path in
the expected string: `:159`, `:160`, `:166`, `:167`, `:180`, `:181`, `:187`,
`:188`, `:199`, `:201`, `:202`; and the runner's struct `tuple_struct`,
`:190`).

## Left

- **The float printer**, Verse Core's: the shortest decimal that reads
  back to the same double needs exact arithmetic on the double's bits,
  which Verse code over 64-bit ints cannot do for every double. Lean has
  it already, `VFloat.render`, kept for the compiler's messages. A new
  primitive `ftoShortest` (`Core/Prims.lean`), with its seam in
  `Core/Seams.lean` beside `fixed6`'s (`ToString`), its code in OVBC's
  primitive table (the loader's bound on primitive codes), and a C
  implementation (a correctly rounded `%.17g` narrowed to the shortest
  precision that reads back, as `fuzz-floats.sh` would check against
  Python's `repr`). Theorems touched: the primitives' typing and
  evaluation lemmas (`Prim` cases of `TypeSafety.lean`, `Typing.lean`,
  `Adequacy.lean`), none of the language's: the primitive gives a string.
  Then `printer`'s `float` case calls it, and the 14 cases agree (the
  front end only; `Inf`, `NaN`, `-0.0` as the tests have them).
- **Unbounded ints** (`:36-40`): openverse's ints are the Blueprint VM's.
- **A `comparable`'s or a type parameter's value as an `any`**: a printer
  needs the type, which the box (Verse Core's `dyn`) or the caller has; a
  Verse Core primitive that prints a `dyn`, or a printing dictionary per
  type parameter in programs that call `ToDiagnostic`.
- **Types as values** (`int`, `my_class`, `?int`: `:215-232`, not
  translatable).
- `+` of diagnostics and strings (the API reference: "`+` is overloaded for
  `diagnostic`/`diagnostic`, `diagnostic`/`string` and `string`/`diagnostic`"):
  no test.
