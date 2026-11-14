# `ToDiagnostic`: what the Book asks, and what openverse would need

`ToDiagnostic` is the cause of 93 refusals of the Book of Verse's tests
(`Tests/Intrinsics/ToDiagnostic.versetest`), the largest library cause left
([the map of forms](book-test-conformance.md#forms-of-expressions-statements-and-the-library-a-map)).
This note pins what the Book says, sorts the cases by what each needs, and
designs the change. It is left: the cases need an `any` that keeps its
value, which every program's `any` would change, and a shortest
round-trip float printer, which is Verse Core's and the C runtime's. Revision
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

## A design

1. **An `any` that keeps its value, in the front end.** Today an `any` is
   `void` in Verse Core: a value becomes one by being evaluated
   (LANGUAGE.md, "any"). Instead, a value of type `T` converted to `any`
   becomes an object of a class the front end writes for `T`,
   `$any(T)`, below an interface `$anything` with one method
   `Diagnose()<reads>:string`, which prints the value at `T` — as function
   values become objects of hidden classes ("Function values: hidden
   interfaces and classes", DESIGN.md). Verse Core, its proofs, OVBC and the
   runtime are unchanged: `any` becomes a reference type. Every conversion
   to `any` (`convert`'s `_, .any` case, joins at `any`, `[]any`, `?any`,
   maps' values, function types' parameters through their adapters) builds
   one, so it changes the code of every program that converts a value to
   `any` (an allocation per conversion): it would be taken only by programs
   that call `ToDiagnostic`, which none of openverse's do, or by all of
   them as the owner decides. `<reads>`: an object's fields are printed when
   `ToDiagnostic` runs, not when the conversion did.
2. **The printers**, Verse code the front end writes per type (as the
   rationals' helpers are), with `ToString` of ints, chars and strings
   escaped by the tests' rules; an object's class name and its fields in
   declaration order; a `diagnosable` object's `GetDiagnostic`.
3. **The float printer** is Verse Core's: the shortest decimal that reads
   back to the same double needs exact arithmetic on the double's bits, which
   Verse code over 64-bit ints cannot do for every double. Lean has it
   already, `VFloat.render`, kept for the compiler's messages. A new
   primitive `ftoShortest` (`Core/Prims.lean`), with its seam in
   `Core/Seams.lean` beside `fixed6`'s (`ToString`), its code in OVBC's
   primitive table (the loader's bound on primitive codes), and a C
   implementation (a correctly rounded `%.17g` narrowed to the shortest
   precision that reads back, as `fuzz-floats.sh` would check against
   Python's `repr`). Theorems touched: the primitives' typing and
   evaluation lemmas (`Prim` cases of `TypeSafety.lean`, `Typing.lean`,
   `Adequacy.lean`), none of the language's: the primitive gives a string.
4. **The package path**: openverse's top level has no path; the 13 cases
   expect the test runner's. A harness translation of the expected strings
   would be the honest stand-in (the path is the runner's, not the
   language's), or the cases not translatable.

With 1 and 2, 60 cases could agree; with 3, 14 more; the rest need the
runner's path (9 more) or unbounded ints (6).
