# Book of Verse test conformance

This survey runs openverse on every test case of the Book of Verse's own test
suite and records, case by case, whether openverse agrees. It was taken at
`0e69cfb862d8e6888a944049cf79bedd8404aa31` (main, 2026-11-13); its counts
are those of openverse with the parser forms of [After the parser
forms](#after-the-parser-forms) and the rule checks of [After the rule
checks](#after-the-rule-checks), on main `f80fcb2`, and with the type aliases
of [After the type aliases](#after-the-type-aliases), the library
functions of [After the library functions](#after-the-library-functions)
the extension methods of [After extension
methods](#after-extension-methods), the empty value and comparisons of
[After the empty value](#after-the-empty-value), the qualified names and
the Book's shadowing rule of [After qualified names](#after-qualified-names),
the readings of [After the readings audit](#after-the-readings-audit),
the access specifiers of [After access specifiers](#after-access-specifiers),
`comparable` as a type of [After `comparable`](#after-comparable), the
load-bearing readings of [After the load-bearing
readings](#after-the-load-bearing-readings), the attributes, types as
values and syntax forms of [After attributes, types as values and the
syntax forms](#after-attributes-types-as-values-and-the-syntax-forms), the
Book's primitives of [After the Book's
primitives](#after-the-books-primitives), the source upper bounds of
[After source upper bounds](#after-source-upper-bounds), what a `for`
undoes of [After what a `for` undoes](#after-what-a-for-undoes), the
fields with accessors, type arguments and metatypes of [After fields with
accessors, type arguments and
metatypes](#after-fields-with-accessors-type-arguments-and-metatypes),
the weak maps and module-scoped `var`s of [After weak maps and
module-scoped vars](#after-weak-maps-and-module-scoped-vars), the
fixes of [After the found bugs](#after-the-found-bugs), the classes
and subtyping of [After classes and subtyping](#after-classes-and-subtyping),
the forms of [After the forms of expressions, statements and the
library](#after-the-forms-of-expressions-statements-and-the-library) and the
variance of [After variance](#after-variance), the held rules of [After the
held rules](#after-the-held-rules), and `ToDiagnostic`, `true` and the
rest of [After `ToDiagnostic`, `true` and the full type-parameter
rule](#after-todiagnostic-true-and-the-full-type-parameter-rule),
against the Book at
[`beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests),
the revision the other research notes pin. The Book's
[`DEVELOPMENT.md`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/DEVELOPMENT.md)
calls `Tests/` "a verbatim copy of the compiler's own test suite", run with
Epic's `VerseTestScriptCmd`. These are development expectations of the head
of Verse's main branch, not a certification of a released UEFN compiler. No
Epic compiler or engine was run, and no Epic source code was read: the
harness reads the test files of the public Book repository, and this note
quotes them by file and line only.

The harness is [`tests/conformance/book/booktests.py`](../../tests/conformance/book/booktests.py)
(run it with [`scripts/book-conformance.sh`](../../scripts/book-conformance.sh)),
its causes are [`causes.py`](../../tests/conformance/book/causes.py), and the
per-case verdicts are [`baseline.tsv`](../../tests/conformance/book/baseline.tsv).

## Summary

- **13,504 cases** from the 629 test files that hold one (of 636; seven are
  entirely commented out): 13,197 test cases and 307 cases for the shared
  definitions of a file.
- **3,952 are not translatable** (29%; 3,940 on main `dca5ad1`, before [After `ToDiagnostic`, `true` and the full type-parameter rule](#after-todiagnostic-true-and-the-full-type-parameter-rule), whose expected strings name the test runner's package; 3,721 on main `7f12181`: [After the remaining causes](#after-the-remaining-causes) found 193 more of the test runner's names, [After weak maps and module-scoped vars](#after-weak-maps-and-module-scoped-vars) 2 more of the runner's and the engine's, [After the forms of expressions, statements and the library](#after-the-forms-of-expressions-statements-and-the-library) 24 more, the runner's modules and package path): virtual packages and modules
  (1,264); the compiler's test runner, its natives and classes (1,207), its
  coroutine controls `CoroUtils` (552) and its other modules (187); engine
  APIs (persistence, JSON, natives; 345); compiler tooling such as bytecode
  and digests (128); VM-conditional code inside a definition (37) and one
  file that defines `Main` itself (1).
- Of the **9,552 translatable cases**, openverse **agrees on 8,692 (91%)**,
  refuses 703 valid programs, **accepts 65 refused ones**, gives a
  **different result in 92** (87 of them `verse_vm_only` cases of unbounded
  ints) and hits **no internal error** ([After `ToDiagnostic`, `true` and
  the full type-parameter rule](#after-todiagnostic-true-and-the-full-type-parameter-rule);
  on main `dca5ad1`, before it: 8,599 agreed, 809 refused, 69 accepted, 87
  differed, after [After the held rules](#after-the-held-rules), merged with
  [After variance](#after-variance);
  on main `84285c1`, before them: 8,544 agreed, 856 refused, 77 accepted, 87
  differed, with [After the forms of expressions,
  statements and the library](#after-the-forms-of-expressions-statements-and-the-library);
  on main `215af57`, before that: 8,452 agreed, 964 refused, 84 accepted, 88
  differed, with [After classes and
  subtyping](#after-classes-and-subtyping); on main `fdb1127`, before that:
  8,290 agreed, 1,123 refused, 87 accepted, 88 differed, with [After the
  remaining causes](#after-the-remaining-causes), [After weak maps and
  module-scoped vars](#after-weak-maps-and-module-scoped-vars) and [After
  the found bugs](#after-the-found-bugs); the first two alone:
  8,267 and 8,236 agreed; before them, on main `7f12181`, of
  9,783: 8,214 agreed, 1,346 refused, 135 accepted, 88 differed). (When the survey was
  taken, at `0e69cfb`: 6,409 agreed, 2,817 refused, 482 accepted, 86
  differed and 4 internal errors; before the parser forms, at main
  `99ed203`: 6,417 agreed, 2,809 refused, 482 accepted, 86 differed; with
  the parser forms alone: 6,828 agreed, 2,360 refused, 521 accepted, 85
  differed, 4 internal errors; with the rule checks, at main `1300096`:
  7,057 agreed, 2,360 refused, 296 accepted, 85 differed, none internal;
  each of the next two steps measured alone from there: the type aliases
  7,072 agreed, 2,333 refused, 308 accepted, the library functions 7,128
  agreed, 2,277 refused, 296 accepted, both with 85 different; with both,
  7,143 agreed, 2,250 refused, 308 accepted, the base of the extension
  methods; with them, 7,180 agreed, 2,210 refused, 308 accepted and 85
  differed, the base of the empty value; with that, at main `d058cfd`: 7,254
  agreed, 2,164 refused, 307 accepted, 58 differed, the base of the
  qualified names; with them, at main `7bf6dbd`: 7,374 agreed, 2,069
  refused, 282 accepted, 58 differed, the base of [the readings
  audit](#after-the-readings-audit); with that, at main `ce5e444`: 7,390
  agreed, 2,066 refused, 277 accepted, 50 differed, the base of [access
  specifiers](#after-access-specifiers); with them, at main `9263665`:
  7,535 agreed, 2,028 refused, 170 accepted, 50 differed, the base of
  [`comparable`](#after-comparable); with it, at main `77bc509`: 7,670
  agreed, 1,893 refused, 170 accepted, 50 differed, the base of [the
  load-bearing readings](#after-the-load-bearing-readings); with them, at
  main `34e76e1`: 7,732 agreed, 1,869 refused, 136 accepted, 46 differed,
  the base of [attributes, types as values and the syntax
  forms](#after-attributes-types-as-values-and-the-syntax-forms); with
  them: 8,004 agreed, 1,598 refused, 135 accepted, 46 differed, the base of
  [the Book's primitives](#after-the-books-primitives); with them, at main
  `84ee83c`: 8,114 agreed, 1,439 refused, 135 accepted, 95 differed, the
  base of [source upper bounds](#after-source-upper-bounds) and of [what a
  `for` undoes](#after-what-a-for-undoes); with each alone, 8,131 agreed,
  1,422 refused, 135 accepted, 95 differed, and 8,121, 1,439, 135, 88.)
- An agreement on an expected error is weak evidence: 2,999 expected errors
  agree, but only 1,552 of them are refused by a check of a language rule
  (and 39 more, whose codes are all warnings, get openverse's warning);
  1,060 are refused by the parser (the lexer's and parser's own checks
  included) and 348 for a missing feature (counts of the run of [After
  variance](#after-variance)).
- **Internal errors**: none ([Internal errors](#internal-errors)). The three
  programs that failed `Prog.checkTypes` (`X:int = return`, `() = ""`, a
  `void` parameter compared with `""`) are refused or compile, and Lean's
  out-of-memory panic (exit 1, where C gives `limit: memory` and exit 3) is
  documented as the reference interpreter's memory limit
  ([`FORMAT.md`](../FORMAT.md)).
- **Dangerous**: the rule checks of [After the rule
  checks](#after-the-rule-checks) refuse duplicate class, struct, enum and
  interface definitions (the first was kept silently), a class and a
  function of one name, constants that depend on themselves, the names the
  tests reserve and `_`, float literals that round to infinity, misplaced
  specifiers and what they require, redundant effects, `defer:` as a value,
  `for` of literal clauses only, `not` of what cannot fail, unreachable
  `case` arms and stray `#>`, and strip comments inside string literals, as
  the Book's chapter 1 requires. Still accepted or different: `true?`
  is `true`, which the tests make the empty value (4 cases; `false`, `()`,
  `""`, `array{}`, `map{}` and an empty option are one value now, [After
  the empty value](#after-the-empty-value)). Access specifiers are
  enforced, and their 107 accepted refusals agree ([After access
  specifiers](#after-access-specifiers)). A member of a module or class that
  took the name of an enclosing definition, which chapter 10 refuses, is
  refused now ([After qualified names](#after-qualified-names)). [The
  readings audit](#after-the-readings-audit) took the readings the tests
  contradict (the order of `set X += e`, the key order of
  `ConcatenateMaps`, constants named before their definition, a failing
  range bound, a map's `set`, the left of `or`); the format of `ToString`
  of a float (the C runtime) is designed there and left; of the
  load-bearing readings, warnings, `return`/`break` out of a failure
  context and commas in blocks are taken ([After the load-bearing
  readings](#after-the-load-bearing-readings)) and the rollback of a `for`
  iteration is left; comparison chains are where the Book disagrees with
  itself; the BPVM `int` reading gives the 26 VerseVM-only overflow
  differences.
- **Most refusals were syntax**: path literals (213, nearly all parse-only
  tests), empty class and function bodies (160), unnamed parameters (123),
  block and dot forms (163); the parser now takes these (450 cases more
  agree, see [After the parser forms](#after-the-parser-forms)). The
  library functions the tests call (the character conversions, `Clamp`,
  `Sgn`, math functions as values) followed ([After the library
  functions](#after-the-library-functions), 71 more), and so did type
  aliases ([After the type aliases](#after-the-type-aliases), 27 more, 12
  fewer), and extension methods ([After extension
  methods](#after-extension-methods), 37 more, none fewer), and qualified
  names ([After qualified names](#after-qualified-names), 102 more, and 18
  with the Book's shadowing rule), and access specifiers ([After access
  specifiers](#after-access-specifiers), 145 more, none fewer). Left: attributes (134), Tim Sweeney's
  parser tests and other syntax (192); bitwise functions (159; built since:
  [After the Book's primitives](#after-the-books-primitives)), free `ToChar` and `ToChar32` the API reference does not
  declare (145), `ToDiagnostic` (93). The largest semantic gaps are types as
  values (196), `comparable` as a type (125; built since: [After
  `comparable`](#after-comparable)) and VerseVM-only union types (136).

## How the harness reads a test file

A `.versetest` file is one Verse module. Its top-level items are of three
kinds, and the harness splits a file into them by indentation and brackets,
with comments and string contents masked:

- **Definitions** (`F0(X:any):any=X`, `c := class{X:any={}}`, `using{…}`),
  shared by the file's runtime assertions.
- **Assertions**, the test cases: `assert{…}` or `assert:` and an indented
  block, `assert_runtime_error(NAME)`, `assert_valid`,
  `assert_semantic_error(CODE, …)`, `assert_syntax_error(CODE)`,
  `assert_valid_syntax`, `assert_roundtrip`, `assert_link_error`,
  `assert_ir_error`, `assert_link_valid`, and tooling forms
  (`assert_bytecode`, `assert_digest_generated`, …). A body is braced, an
  indented block, or `. expression`; syntax tests give it as a string literal
  (`assert_syntax_error(3100){"0x1_"}`), which the harness unescapes.
  `assert_semantic_error<depends_on_library>(…)` carries a specifier the
  harness records and otherwise ignores.
- **Wrappers** that select a VM or mark a known failure: `bp_vm_only{…}`
  (the older BPVM), `verse_vm_only{…}` (VerseVM), `verse_vm_todo{…}`
  (expected on BPVM, a known VerseVM failure), `auto_qualify_todo{…}` (skipped
  in the auto-qualification mode). Their contents are spliced in with the tag.

A case is identified by `FILE:LINE`, the line of its assertion keyword in
the pinned file (`#2` is added when two start on one line). A file with no
assertion is one case, `FILE:1`, expected to compile. Seven files have
everything commented out and give no case. Every file's shared definitions
also give a case `FILE:decls`, expected to compile, since the test runner
compiles them with every runtime assertion; these 307 are counted
separately below.

### What each case becomes

| Form | Program | Expectation |
|---|---|---|
| `assert`, `assert_runtime_error`, `assert_success_or_runtime_error` | the file's `using`s and the shared definitions the body needs, then `Main()<decides>:void = BODY` (braced bodies stay braced, indented ones indented) | `assert`: `Main` succeeds (exit 0); `assert_runtime_error`: a runtime error (exit 2) or resource limit (exit 3); `…_or_runtime_error`: exit 0 or 2 |
| `assert_valid`, `assert_link_valid` | the snippet alone, `;`-separated top-level definitions on lines of their own, and `Main():void = {}` unless it defines `Main` | accepted |
| `assert_semantic_error`, `assert_link_error`, `assert_ir_error` | as `assert_valid` | refused (exit 4); the error codes are recorded, not compared; when they are all warnings (2000-2999), a program that compiles with a warning (`FILE:LINE:COL: warning: …`) agrees too |
| `assert_syntax_error` | the snippet exactly as written, parsed with openverse's parser; when that parses, the snippet and `Main():void = {}` compiled | refused |
| `assert_valid_syntax`, `assert_roundtrip` | the snippet exactly as written, and the snippet as the indented body of `BookSyntax():void =`, each parsed only (a roundtrip test's printed form is not checked) | parsed in either wrapping |
| a file without assertions; `FILE:decls` | the file's definitions and `Main():void = {}` | accepted |

The choices behind this, and what each one could distort:

- **Snippets compile on their own.** `assert_valid` and the error forms do
  not see the file's definitions: 317 `assert_valid` snippets define a name
  that the same file defines at top level (`Tests/DefaultNamed.versetest`
  defines `Subtype := module:` at line 551 and the snippets at lines 572-612
  define their own), which would be duplicates in one scope, and the
  runner expects them valid.
- **Runtime assertions get the definitions they need**, by name and
  transitively (with every member of a module a `using` makes visible, and
  every overload of a name), not all the file's definitions. A definition
  openverse cannot compile then fails only the cases that use it; the
  `:decls` case reports it once. 3,108 of the 4,621 translated runtime
  cases use shared definitions. An operator definition (`prefix'-'`) is
  taken with a definition its signature names, or, when it names only
  built-in types, wherever its symbol occurs. The Epic runner runs a
  file's assertions in one program; an assertion that changes module
  state for a later one is not modelled.
- **An assertion body is a `<decides>` `Main`.** The body must be a failure
  context (`assert{F1(false)=false}`), so `Main()<decides>` is the direct
  translation and a failed assertion is exit 1. It also makes the body a
  failure context for `spawn` and `Signal`, which the Book's tests allow
  and openverse accepts (since [After awaiters inside
  `Signal`](#after-awaiters-inside-signal); before, openverse refused
  `spawn` there, 28 cases).
- **VM tags.** A case sees the untagged definitions and those of its own VM
  (`verse_vm_todo` counts as BPVM). openverse is one implementation: its
  verdict is compared with the case's own expectation, and the tag is
  reported, so a `bp_vm_only` and a `verse_vm_only` twin can disagree with
  each other and openverse agrees with at most one.
- **Error codes are not compared.** openverse has no Epic error numbers. A
  refusal for an unrelated reason (a feature openverse does not parse)
  agrees with an expected error; the split of those agreements is in
  [Totals](#totals).
- **Fuel and time.** Both implementations get `--fuel 10000000` (a tenth of
  openverse's default, so a test that loops ends in seconds) and 60 seconds;
  the slowest single run took 3.8 seconds, and two fresh runs give
  identical results.
- **One stand-in.** The test runner's `DebugPrint`, which the tests call from
  `<computes>` functions on their failure paths only, is replaced by
  `DebugPrint(Message:any)<computes>:void = {}` where a program uses it and
  does not define it (278 cases).

### Not translatable

A case is not translatable when it needs something openverse has no
counterpart for, found before running anything:

| Reason | Cases |
|---|---:|
| the runner's virtual packages and modules (`vpackage`, `vmodule`) | 1264 |
| the test runner's natives and classes | 1207 |
| the test runner's `CoroUtils` | 552 |
| the test runner's free functions `ToChar(N)` and `ToChar32(N)` | 145 |
| the test runner's names found with the map of the remaining causes (`MakeNull`, `native_property_rollback_test`, …) | 48 |
| the test runner's modules, `import(/Verse.org/Tests/VerseTestScriptCmd/…)` | 13 |
| the test runner's package path, `(/Verse.org/VerseTests/…:)`, `(VerseTests:)` | 11 |
| engine API `FromJson` | 153 |
| the test runner's `TestUtils` | 113 |
| `<native>` definitions | 93 |
| engine API `Persistence` | 63 |
| the test runner's `FloatConstants` | 69 |
| compiler tooling: `assert_digest_generated` | 53 |
| `bp_vm_only`/`verse_vm_only` inside a definition | 37 |
| engine API `ToJson` | 32 |
| compiler tooling: `assert_auto_qualification` | 29 |
| compiler tooling: `assert_bytecode` | 25 |
| compiler tooling: `incremental_compilation` | 12 |
| compiler tooling: `assert_fingerprint_determinism` | 4 |
| compiler tooling: `assert_persistence_snapshot` | 4 |
| the test runner's `ProfUtils` | 4 |
| engine API `GetUObjectPathName` | 2 |
| compiler tooling: `assert_used_assets` | 1 |
| engine API `IsUObject` | 1 |
| the test runner's `FunctionUtils` | 1 |
| the file defines `Main` | 1 |
| engine API `persistent_key` | 1 |

The test-runner names were found as openverse's "unknown …" refusals whose
name no line of the test file defines and the Book's Runtime API reference
does not mention, each then checked by hand: `serializable_class`,
`SerializeAndDeserialize`, `native_deeply_mutable`, `test_vni`,
`MakeObjectWith…`, `TestNamedParams`, … (the list is `TEST_NAMES` in the
harness). Engine APIs are those the API reference places in persistence,
JSON, Unreal objects and AutoRTFM. A Book API openverse lacks
(`BitAnd`, `ToDiagnostic`, `weak_map`, …) is not on this list: those
cases are refusals.

## Totals

### Overall

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| all test cases (assertions and files without one) | 13197 | 8512 | 65 | 673 | 92 | 3855 | 0 |
| shared definitions of a file (`:decls`) | 307 | 180 | 0 | 30 | 0 | 97 | 0 |
| **total** | 13504 | 8692 | 65 | 703 | 92 | 3952 | 0 |

### By form

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| `assert` | 6671 | 3790 | 0 | 443 | 92 | 2346 | 0 |
| `assert_semantic_error` | 3460 | 2686 | 31 | 0 | 0 | 743 | 0 |
| `assert_valid` | 1637 | 958 | 0 | 160 | 0 | 519 | 0 |
| `assert_valid_syntax` | 439 | 386 | 0 | 53 | 0 | 0 | 0 |
| `decls` | 307 | 180 | 0 | 30 | 0 | 97 | 0 |
| `assert_roundtrip` | 304 | 293 | 0 | 9 | 0 | 2 | 0 |
| `assert_syntax_error` | 303 | 303 | 0 | 0 | 0 | 0 | 0 |
| `assert_runtime_error` | 140 | 51 | 0 | 4 | 0 | 85 | 0 |
| `assert_link_error` | 55 | 10 | 24 | 0 | 0 | 21 | 0 |
| `assert_digest_generated` | 53 | 0 | 0 | 0 | 0 | 53 | 0 |
| `assert_auto_qualification` | 29 | 0 | 0 | 0 | 0 | 29 | 0 |
| `assert_bytecode` | 25 | 0 | 0 | 0 | 0 | 25 | 0 |
| `assert_ir_error` | 24 | 12 | 10 | 0 | 0 | 2 | 0 |
| `assert_link_valid` | 22 | 19 | 0 | 0 | 0 | 3 | 0 |
| `file` | 13 | 4 | 0 | 3 | 0 | 6 | 0 |
| `incremental_compilation` | 12 | 0 | 0 | 0 | 0 | 12 | 0 |
| `assert_fingerprint_determinism` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `assert_persistence_snapshot` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `assert_used_assets` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `assert_success_or_runtime_error` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |

### By VM tag

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| no VM restriction | 12208 | 8301 | 29 | 408 | 4 | 3466 | 0 |
| `verse_vm_only` | 702 | 215 | 4 | 289 | 88 | 106 | 0 |
| `bp_vm_only` | 366 | 81 | 32 | 0 | 0 | 253 | 0 |
| `verse_vm_todo` (BPVM only; a known VerseVM failure) | 219 | 95 | 0 | 6 | 0 | 118 | 0 |
| `auto_qualify_todo` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |

### By directory

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| (top level) | 5575 | 3717 | 27 | 540 | 3 | 1288 | 0 |
| Operators/ | 1203 | 1103 | 0 | 0 | 27 | 73 | 0 |
| Bugs/ | 1185 | 782 | 33 | 95 | 0 | 275 | 0 |
| Literals/ | 1020 | 835 | 0 | 6 | 0 | 179 | 0 |
| Serialization/ | 991 | 0 | 0 | 0 | 0 | 991 | 0 |
| Attributes/ | 795 | 535 | 4 | 10 | 0 | 246 | 0 |
| FlowControl/ | 484 | 432 | 0 | 7 | 0 | 45 | 0 |
| Intrinsics/ | 437 | 377 | 0 | 17 | 6 | 37 | 0 |
| Math/ | 321 | 261 | 0 | 0 | 56 | 4 | 0 |
| Classes/ | 317 | 230 | 0 | 8 | 0 | 79 | 0 |
| Versions/ | 289 | 6 | 0 | 0 | 0 | 283 | 0 |
| Roundtrip/ | 255 | 245 | 0 | 8 | 0 | 2 | 0 |
| Coroutines/ | 229 | 23 | 0 | 2 | 0 | 204 | 0 |
| Modules/ | 219 | 73 | 1 | 8 | 0 | 137 | 0 |
| Features/ | 67 | 21 | 0 | 1 | 0 | 45 | 0 |
| Interfaces/ | 41 | 34 | 0 | 0 | 0 | 7 | 0 |
| Bytecode/ | 27 | 2 | 0 | 0 | 0 | 25 | 0 |
| Exercises/ | 17 | 17 | 0 | 0 | 0 | 0 | 0 |
| Incremental/ | 16 | 0 | 0 | 0 | 0 | 16 | 0 |
| DebugStackTrace/ | 8 | 0 | 0 | 0 | 0 | 8 | 0 |
| CanCallerAccessEpicInternal/ | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| AssetUsage/ | 1 | 0 | 0 | 0 | 0 | 1 | 0 |

Of the 3,006 expected errors openverse agrees with, 39 are warnings
openverse gives (their codes are all warnings, [After the load-bearing
readings](#after-the-load-bearing-readings)); for the others the refusal came from
the parser in 1,060 (most semantic-error snippets among them use a form
openverse does not parse, such as `@attribute`; the lexer's and parser's
own checks, of comments, float literals, specifiers and an extension
method's receiver, count here), from a diagnostic that says openverse
lacks a feature or a name in 345, and from a rule check in 1,562. Only these 1,562 show
openverse checking the rule the test is about, and even they are not
compared by code. Of the 300 agreeing syntax errors, 8 parse once wrapped
in a function body, so openverse refuses
them only because its top level takes definitions alone.

The full per-file table is in [Appendix B](#appendix-b-totals-per-file).

## Internal errors

Four cases at the survey's revision and with the parser forms, none since
the rule checks ([After the rule checks](#after-the-rule-checks)). Each was a bug whatever the Book says.

| Case | Program | At the survey | Now |
|---|---|---|---|
| `Tests/FlowControl/Return.versetest:11` (expects error 3548) | `X:int = return` and `Main():void = {}` | `internal error: … Prog.checkTypes (in X)` | refused: `return` is in no function's body in a constant's value, nor in a field's default, where it returned from the function that constructed the object (`checkReturns`); agrees |
| `Tests/Operators/CompareString.versetest:122` (expects success) | `Main()<decides>:void = { () = "" }` | `internal error: … Prog.checkTypes (in Main)` | compiles: the right operand of `=` or `<>`, of another Verse Core type than the left and with no type of its own (`""`), goes through a temporary of its type, as the left one already did (#580); the comparison holds, as `"" = ()` does, both the empty value ([After the empty value](#after-the-empty-value)); agrees |
| `Tests/Void.versetest:300` (expects success) | `F(X:void)<decides>:void = { X = "" }` | as above (in F) | as above |
| `Tests/Bugs/FORT-555213-DontSignedInt32OverflowInArrayBytes.versetest:16` (expects success or a runtime error) | doubling an array 28 times under the 4 GB address-space cap | Lean `INTERNAL PANIC: out of memory`, exit 1; C `limit: memory`, exit 3 | the reference interpreter has no memory limit of its own and the Lean runtime's out-of-memory panic cannot be caught: [`FORMAT.md`](../FORMAT.md) documents it as its memory limit, and the harness reads it as exit 3, a resource limit (which an `assert_success_or_runtime_error` allows, as `assert_runtime_error` does); agrees |

The comparisons' neighbourhood (`()`, a `void` value, `false`, a `logic`,
an empty option, `""`, `array{}`, `map{}`, a string and an array variable,
on either side of `=` and `<>`, as a statement and as a condition: 400
programs) had 20 internal errors, all with `""` on the right of a value of
another type; none is left. Apart from the out-of-memory case, Lean and C
agreed byte for byte (output, status and diagnostics) on every program both
ran, and no accepted program raised a `type`, `slot`, `call` or `control`
error.

## Dangerous: accepted where the tests refuse, or different output

These are the cases where an openverse user would get a program the Book's
compiler refuses, or a different result. Every one is listed in
[Appendix A](#appendix-a-every-accepted-refusal-and-different-output).

### Different output

88 cases (95 before [what a `for` undoes](#after-what-a-for-undoes), 46 before [the Book's primitives](#after-the-books-primitives), 50 before [the load-bearing readings](#after-the-load-bearing-readings), 58 before [the readings audit](#after-the-readings-audit), 85 before [the empty value](#after-the-empty-value); 85 with the parser forms too: two comments inside strings agree now, and two internal errors compare now as below) run in openverse and give another result than the assertion
expects (in every one the assertion fails or a runtime error is raised; no
case prints differently, since the tests check values, not output).

| Cause | Cases | Example | openverse | The test | Marked | openverse documents it | Size |
|---|---:|---|---|---|---|---|---|
| empty values are one value | 30 → 32 → 4 ([After the empty value](#after-the-empty-value): 28 agree) | `Tests/Operators/BoolQuery.versetest:3`: `assert{true?=false}` | `true?` is `true`, so the comparison fails | succeeds: `true?` and `(true? and true?)` are the empty value | none; the operators chapter: "`IsReady?` is equivalent to comparing against true" | yes: Readings, "`X?` of a logic" | front-end: the value of `X?` of a logic ([empty-values.md](empty-values.md), 3.1) |
| `int` precision | 26 → 82 (the bitwise functions' 56 `verse_vm_only` cases, [After the Book's primitives](#after-the-books-primitives)) | `Tests/Operators/BinarySubInt.versetest:40`: `assert{0 - -9223372036854775808 = 9223372036854775807+1}` | `error: overflow` | succeeds | all `verse_vm_only`; their `bp_vm_only` twins expect the runtime error and agree | yes: the BPVM reading of the `int` range ([Readings](../LANGUAGE.md#readings-openverse-takes)) | Core and runtime (unbounded integers); keep as a reading |
| rollback of a `for` iteration | 8 → 10 (`for.versetest` 317, 344, refused for `array{} = for(…)` before) → 7 (317 and `SoftwareTransactionalMemory.versetest` 74, 81 agree: a failing range bound gives no iterations, [the readings audit](#after-the-readings-audit)) → 0 ([what a `for` undoes](#after-what-a-for-undoes): all agree) | `Tests/Range.versetest:140`: `for (J:(set X = array{666}); I := GetLower()..GetUpper())` with an empty range, then `X = array{42}` | keeps what a source or a range bound did before a later clause failed (`X` stays `array{666}`; in `Tests/FlowControl/for.versetest:362` `Y.Inc()` in an inner range bound is kept for the rejected `I = 2`) | undone with the iteration | none | in part: Readings, "Code before a choice" (#208, #283) | front-end feature: one transaction per iteration, sources included |
| `ToString` of a float | 7 → 0 ([After the Book's primitives](#after-the-books-primitives): all agree) | `Tests/Intrinsics/FloatToString.versetest:18`: `TestSignedFloatToString[1.0, "1.000000"]` | `1.0` | `1.000000`: six decimals, every digit of a large value | none; the Book's prose example is `98.5`, so prose and tests disagree | yes: Readings, `ToString` of a float | a message-sized change in both formatters; an owner decision |
| commas and semicolons in blocks | 4 → 0 (commas in a block make a tuple, [the load-bearing readings](#after-the-load-bearing-readings)) | `Tests/Option.versetest:44`: `assert{option{1,2}?=(1,2)}` | `option{1,2}` holds `2`; `for(…){C,I}` yields `I` | commas in braces make a tuple (the Book's ch. 1, "Semicolons vs Commas": `Comma := { A, B, C }` is a tuple) | none | no | parser form, and an owner decision: today commas separate statements |
| order of `set X op= e` | 4 → 1 (the readings audit: `e` first; `ArrayAppend.versetest:12`, VerseVM-only, writes through a reference taken before `e`) | `Tests/ArrayAppend.versetest:140`: `set S.X += if (set S.X = array{0}; 0=0) { array{42} } else { array{42} }`, then `S.X = array{0, 42}` | reads the old value first, giving `array{1, 2, 3, 42}` | evaluates `e` first | 2 `verse_vm_only` | yes: the Mutation row of [Supported](../LANGUAGE.md#supported) | front-end (evaluation order); an owner decision |
| comments inside strings | 2 → 0 (the lexer removes a block comment from a string) | `Tests/Literals/String.versetest:234`: `assert{"abc<#def#>ghi" = "abcghi"}` | the string keeps `<#def#>` | the comment is removed | none; the Book's ch. 1 example and [the digest](book-of-verse-digest.md) §1.1 say the same | no | lexer, small |
| key order of `ConcatenateMaps` | 2 → 0 (the readings audit) | `Tests/Intrinsics/ConcatenateMaps.versetest:21`: `ConcatenateMaps(map{"0"=>0,"1"=>1},map{"1"=>0,"0"=>1}) = map{"1"=>0,"0"=>1}` | a key keeps its first position | the later map's order | none | yes: the Maps row of [Supported](../LANGUAGE.md#supported) | front-end/library, small; an owner decision |
| comparison chains | 1 | `Tests/Operators/Associativity.versetest:9`: `assert{not 1 <> 2 <> 1}` | every adjacent pair is checked, so `1 <> 2 <> 1` succeeds | `(1 <> 2) <> 1` compares the left result `1` with `1` and fails | none | yes: Readings, associativity of comparisons | parser/front-end, small; an owner decision |
| a parametric struct compared across instances | 1 → 0 (agrees: [After the empty value](#after-the-empty-value)) | `Tests/Operators/CompareStruct.versetest:43`: `parametric_comparable_struct([]int){X:=array{1,2}} = parametric_comparable_struct(tuple(int,int)){X:=(1,2)}` | compiles; fails | succeeds (an array equals a tuple of its elements) | none | in part: an array compares with a tuple ([Supported](../LANGUAGE.md#supported), Types) | front-end, small |

### Accepted where the tests expect an error

521 cases with the parser forms, 277 now (the count before the arrow is
with the parser forms alone, after it the one now; the openverse column is
the former, and what the rule checks, the type aliases and qualified names
changed is in [After the rule checks](#after-the-rule-checks), [After the
type aliases](#after-the-type-aliases) and [After qualified
names](#after-qualified-names)). The causes, by the error code the test
expects:

| Cause | Cases (parser forms → now) | Example | openverse | The test | Marked | openverse documents it | Size |
|---|---:|---|---|---|---|---|---|
| access specifiers | 95 → 107 (12 `<public>` type aliases of internal types, which agreed when no alias parsed) → 0 ([After access specifiers](#after-access-specifiers)) | `Tests/ArchetypeAccessSpecifiers.versetest:43`: `my_struct<public> := struct<protected>{x<public>:int}` | accepted | errors 3593, 3594, 3543, 3650, 3642: a `<private>`, `<protected>` or `<internal>` member used outside its scope, a specifier where none is allowed or two of them, access narrowed by an override | none | yes: Readings, "accepted and not enforced" | front-end: visibility per specifier, extending module visibility |
| reserved names | 83 → 2 → 0 (`Union.versetest` 23, 290: a top-level constant states its type, the readings audit) | `Tests/NamesReservedForFuture.versetest:137`: `_:int = 42` | accepted | error 3514: 65 names reserved for the future (`as`, `bag`, `element`, `find`, `first`, `repeat`, …), `_`, and the built-in names `subtype`, `castable_subtype`, `Self` and `local` as definitions; 3547: `while := 42` and two others | none; the Book (ch. 1): "The single underscore `_` is reserved"; the digest notes the Book gives no list | no | a message |
| unreachable code | 39 → 30 → 0 (warnings, and `return`/`break` out of a failure context refused, [the load-bearing readings](#after-the-load-bearing-readings)) | `Tests/FlowControl/Reachability.versetest:12`: `F():int={if(return 0=1) {0} else {1}; 1+2}` | accepted | errors 2000, 2002, 2302, 3535, 3616: code after `return`, `break` or a `case` that always returns, unreachable or repeated `case` arms | none | no | front-end: a reachability pass |
| failure where it is not allowed | 35 → 30 → 29 (`LogicalOr.versetest:143`: the left of `or` must be able to fail, the readings audit) | `Tests/Effects.versetest:537`: `c:=class{X:int=option{0}?}` | accepted | error 3512: a failable field default, a failable default of a named parameter (16 in `DefaultNamed.versetest`), a `loop` as an `if` condition; 3513: `not` of an expression that cannot fail | 3 `bp_vm_only`, 1 `verse_vm_only` | in part: a default "is evaluated at the call, its effects counting as the caller's" ([Supported](../LANGUAGE.md#supported), Functions) | a message |
| misplaced specifiers | 32 → 0 | `Tests/Attributes/FinalSuperAttribute.versetest:56`: `i<final_super>:int = 42` | accepted | error 3596: `<abstract>` on a method, `<concrete>` or `<final>` on an interface, `<castable>` or `<final_super>` on a name; 3680: a class below a `<final_super_base>` class must be `<final_super>` | none | no (openverse refuses `<final_super>` classes, #11) | a message |
| other type rules | 31 → 28 → 24 (`SOL-4199-BreakFromIf.versetest` 4, 15, 51, 60: a `break` out of a failure context, [the load-bearing readings](#after-the-load-bearing-readings)) | `Tests/Bugs/2023-01-18-FunctionParameterWithoutDomain.versetest:12`: `F(X:int=0):void={}` | accepted | a default on a positional parameter (3625); a named argument before a positional one (`DefaultNamed.versetest:122`); `var` in a struct (`Classes/Struct.versetest:31`, 3607); `set S.M = 1` on a field that is no `var` (`Mutability.versetest:426`); `X:tuple() = if (false?) then (1, 2) else false` (`Void.versetest:223`, refused now that `tuple()` is a type of its own); joins of classes through a shared interface (`SOL-5838`); polymorphic and mutual recursion of parametric classes, which the test comments call "not yet supported" (`ParametricTypes.versetest:263-269`); `using` of a path to a class | 1 `bp_vm_only` | no | messages, one each |
| limits of Epic's compiler | 26 → 23 | `Tests/Map.versetest:45`: `V12:[[]int]void = map{}` | accepted | error 3502: arrays and maps as map keys, joins of function types with different effects (7 `bp_vm_only` IR errors whose `verse_vm_only` twins expect valid), a refinement bound out of range | the Book (ch. 3): arrays as keys are rejected with "Use of `[]int` as a map key is not yet implemented"; 7 `bp_vm_only` | no | none needed: openverse is more general here |
| duplicate definitions | 24 → 1 | `Tests/Bugs/2020-04-22-ThreeDuplicateDefinitions.versetest:17`: `C := class {}` three times | accepted, **the first kept silently** (two classes `C` with fields `X` and `Y`: `C{}.X` runs); also two structs or enums of one name, a class and a function of one name; a module function shadowed by a method (`ShadowDefinition.versetest`, 15), refused now with the Book's shadowing rule; left: `enum{public}` (`QualifiedIdentifier.versetest:315`) | error 3532 | none | no; constants and functions defined twice are refused | a message |
| `<concrete>` classes | 22 → 7 | `Tests/Attributes/concrete.versetest:21`: `class1 := class<concrete>:` with `Property:int` | accepted | error 3519: a concrete class needs a default for every field, also for interface fields | none | no | a message |
| name limits of the BPVM | 19 → 19 | `Tests/Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest:92`: `Function():int` and `FUNCTION():int` in one module | accepted | link errors 9200, 9000, 9002, 3655: names equal but for case, identifiers too long for Unreal names | all `bp_vm_only` | no | none needed (an engine limit) |
| control forms | 17 → 7 | `Tests/FlowControl/for.versetest:193`: `NotAnIterable:[]int= for(1) { 1 }` | accepted | `for` over what is no iterable or a range of an array (3524), `for(){}` (3544), a `loop` with no `break` (3579), `return` in a field default (3548) or a `for` body (3534), a non-suspending arm of `race` (3538), `using{/localhost}` | none | no | messages |
| `<final>` members | 13 → 1 | `Tests/Attributes/final.versetest:64`: `c := class{X<final>:int=0}` and `c{X:=1}` | accepted | errors 3568, 3673, 3674, 3591: a `<final>` field set in an archetype or without a value, `<final>` on a module function, a final method that does not satisfy an interface | none | no | messages |
| qualifiers | 13 → 6 | `Tests/Bugs/SOL-3564-CallingSuperClassMethodFromOverriddenMethod.versetest:7`: `F<override>():void= (a:)F()` in `b := class(a)` | accepted | `(a:)F()` in an override where `(super:)` is meant (2003, 2004: the tests' warnings), `(super:)` of a method no class above has, or in a class block (3612); a qualified call through a class that inherits or overrides the method (3506) and a qualified `using` (3506, 3612) are refused now | none | no | messages |
| float literal out of range | 12 → 0 | `Tests/Literals/Float.versetest:248`: `F():float=+2.0e+308` | accepted (infinity) | error 3554 | none | no: literals are "the nearest double" | a message |
| redundant effects | 9 → 0 | `Tests/Effects.versetest:229`: `F()<transacts><reads>:void={}` | accepted | error 3565: an effect implied by another, on functions and on classes, interfaces and structs | none | no ([effect conformance](effect-conformance.md) refuses contradictory ones) | a message |
| effects of initializers | 8 → 8 | `Tests/GlobalVariables.versetest:86`: `c0 := class<allocates>{block{var X:int = 0}}` and `C0:c0 = c0{}` | accepted | 3582: a module constant whose initializer writes; link error 9003 (4 `verse_vm_only`) | 4 `verse_vm_only` | in part (#511) | a message |
| `<castable>` and parametric types | 7 → 0 | `Tests/Castable.versetest:54`: `class1(t:type) := class<castable> {}` | accepted | error 3678 | none | no | a message |
| interface inheritance | 7 → 7 | `Tests/Interface.versetest:92`: `C := class(T, T) {}` | accepted | 3592: an interface inherited twice directly; 3523: `<override>` in an interface | none | no | a message |
| comment lexing | 6 → 0 | `Tests/TimSyntax.versetest:45`: `#>` | accepted (a `#` comment) | a syntax error: `#>` with no `<#`, an unclosed `<#` after `<#>` | none | no | a message in the lexer |
| `<persistable>` structs | 6 → 1 | `Tests/persistable.versetest:43`: `struct1 := struct<persistable>:` with `X:any` | accepted | error 3662: a field type that cannot persist | none | no (persistable classes are refused) | a message |
| `defer` as a block's value | 5 → 0 | `Tests/FlowControl/defer.versetest:928`: a `defer:` ending a function body | accepted | error 3567 | none | no | a message |
| constructor-like functions | 5 → 0 | `Tests/Bugs/SOL-2577-ConstructorOverloadAmbiguity.versetest:3`: `c := class{}` and `c(I:int):c=c{}` | accepted | 3588/3532: a function named like a class, a local shadowing an overloaded function | none | no | a message |
| cyclic initializers | 4 → 2 → 0 (`DefaultValueAssignment.versetest` 102, 128: a constant names only those defined before it in its scope, the readings audit) | `Tests/CyclicReferences.versetest:11`: `X:int = X` | accepted; a `Main` that prints `X` stops with `limit: recursion depth` (exit 3) | error 3502; also `i:int = j` with `j:int = i`, and a module constant using one defined after it | none | no | a message: a dependency order over constants |
| other syntax | 3 → 3 | `Tests/Classes/ClassBlockClause.versetest:19`: `c:=class{x:int block{}}` | accepted | a syntax error (also `ReserveDotSpace.versetest:5, 6`) | none | no | parser messages |

39 of these agreed when the survey was taken only because openverse could
not parse a form the program also uses (an empty class body, `F(:t)`,
`if:` without `then`, an `option:` block, an archetype block, a class field
ending in `;`), and the parser forms of [After the parser
forms](#after-the-parser-forms) let it reach the rule it does not check:
access specifiers (8, `DigestVisibility.versetest`), `<concrete>` classes
(6), `break` or `return` in a failure context (5,
`SOL-4199-BreakFromIf.versetest`, a documented reading), qualifiers (5,
`SOL-3564-…`), type parameters the tests call uninferable (4, error 3503),
`<final>` fields overridden (2), `<unique>` on a struct (2), a `void`
parameter given an `int` (2, error 3509), `bp_vm_only` IR limits (3) and
two others (`Classes/Constructor.versetest:528`,
`ParametricFunctions.versetest:431`). openverse accepts each of them
written without the form as well. The rule checks refuse 9 of them:
`<concrete>` classes (`concrete.versetest:43, 48, 116, 203`, and `:124`,
`<abstract>` with `<concrete>`), `<unique>` on a struct (`unique.versetest:17,
20`) and the overridden `<final>` fields (`final.versetest:38, 48`); 30 are
left (`concrete.versetest:38` is a class below a `<concrete>` one, see
[After the rule checks](#after-the-rule-checks)).

## Refused where the tests expect a valid program

2,069 cases (1,999 test cases and 70 `:decls`). The cause is that of
openverse's first refusal: a case can hit several, so a count is the number
of cases a fix would get past their first obstacle, an upper bound on the
cases it would turn into agreements.

| Cause | Cases | Example | openverse | Marked | openverse documents it | Size |
|---|---:|---|---|---|---|---|
| types as values | 196 | `Tests/Cast.versetest:69`: `assert{void(0)}` | `unknown function 'void'` | 10 `verse_vm_only` | in part: `t:subtype(…)` bounds of type parameters are supported, source upper bounds refused (#502) | front-end feature, and Core for `type` values: `subtype(t)`, `castable_subtype(t)`, `concrete_subtype(t)`, conversions `int(0)`, classes as values |
| other syntax | 192 → 174 (the 19 `scoped{…}` cases agree: [After access specifiers](#after-access-specifiers)) | `Tests/TimSyntax.versetest:224`: `"1,2"` (valid syntax) | parse errors of many kinds: Tim Sweeney's parser tests (51), `of` and `at` calls (15), `<scoped{…}>` specifiers and `scoped{…}` definitions (19), `profile` blocks (8), comments inside a definition (`Roundtrip/Comments.versetest`, 8), pointers `^` (5), module items at uneven columns (4), commas between expressions at statement level (also `Obj.Get, Obj.Set` as a function's value: 33 `ParametricFunctions.versetest` cases its modules' qualified classes led to), … ([After the parser forms](#after-the-parser-forms)) | 4 `verse_vm_only` | no | parser forms and features, many small ones |
| bitwise functions | 159 → 0 ([After the Book's primitives](#after-the-books-primitives): 103 agree, 56 `verse_vm_only` differ) | `Tests/Math/Bitwise.versetest:36`: `assert{BitNot(0) = -1}` | `unknown function 'BitNot'` | 62 `verse_vm_only` (unbounded ints), 13 `bp_vm_only` (runtime errors for shifts) | no; the Book's ch. 4, "Bitwise Operations" | Core and runtime: six `int` primitives, their Lean seams and C |
| character conversions | 145 | `Tests/Literals/Char.versetest:86`: `RequireChar8Equal[HexLiteral, ToChar(Utf8CodeUnit)]` | `unknown function 'ToChar'`: free functions `ToChar(N)` and `ToChar32(N)`, called with parentheses as total functions, which neither the API reference nor Epic's pages declare (the methods `N.ToChar[]`, `N.ToChar32[]` are `<decides>`); most likely the test runner's | none | yes: [char32](../LANGUAGE.md#char32) has the methods | none known |
| other type rules | 134 → 131 (a `set` through a map's key as an `if`'s condition, `Mutability.versetest:248`, `FORT-623803-STMRollbackAfterReturn.versetest` 22 and `:decls`, agree: the readings audit) | `Tests/Bugs/2021-09-03-OptionalTupleAssertionFailure.versetest:3`: `X:?tuple(int,int)=option{1,2}` | `expected ?tuple(int, int), found ?int` (see commas, above); also the `message` type, an overloaded function as a value, `Concatenate()` with no arguments, map keys of a sibling class, types of one name told apart by their parameters (`SOL-7503`, 4), … | 8 `verse_vm_only` | no | each small |
| qualified names | 162 → 26 | `Tests/ShadowDefinition.versetest:113`: `(c52:)F(X:int)` beside an inherited `F` | `a second method F beside the one c52 inherits` | none | yes: [Qualified names](../LANGUAGE.md#qualified-names) | done ([After qualified names](#after-qualified-names)); left: two members of one name in a class (12), the test runner's package path (5), other features' forms (9) |
| union types | 136 | `Tests/Union.versetest:21`: `u:=union{U:u}` | parse error | all `verse_vm_only`; not in the Book's chapters | no | front-end and Core; low priority |
| attributes | 134 | `Tests/Attributes/Attributes.versetest:16`: an `@attribute` before a definition (valid syntax) | `unexpected character '@'` | 1 `verse_vm_only` | no; the Book's ch. 12 and 18 | parser form for built-in attributes; custom attributes (`class(attribute)`) a front-end feature |
| `comparable` as a type | 126 → 26 ([After `comparable`](#after-comparable)) | `Tests/Comparable.versetest:3`: `Equal(X:t, Y:comparable)` | `unknown type 'comparable'` | 1 `verse_vm_only` | yes: [comparable](../LANGUAGE.md#comparable); left: `concrete_subtype`, field overrides, class variance, `weak_map` | done |
| `ToDiagnostic` | 93 | `Tests/Intrinsics/ToDiagnostic.versetest:22` | `unknown function 'ToDiagnostic'` | 7 `verse_vm_only` | no | front-end and runtime: a `diagnostic` printer of every value |
| class and function specifiers | 86 → 84 | `Tests/Effects.versetest:304`: `c:=class<abstract>{F()<converges>:void}` | `<converges> is unsupported` (#494); `<castable>`, `<final_super>` (#11), `<persistable>`, `<native_callable>` | 71 `verse_vm_todo` (`GetCastableFinalSuperClass.versetest`) | yes: [effect contracts](../LANGUAGE.md#effect-contracts), #11 | front-end features, one each |
| extension methods | 53 → 0 | `Tests/ExtensionFields.versetest:6`: `(I:int).Method()<computes>:int=I` | `expected an identifier, found '('` | none | yes: [Extension methods](../LANGUAGE.md#extension-methods) | done ([After extension methods](#after-extension-methods)) |
| comparisons of different types | 51 → 16 → 0 ([After the empty value](#after-the-empty-value), [After `comparable`](#after-comparable)) | `Tests/Operators/CompareString.versetest:168`: `DoesTupleEqualString(A:tuple(t,t,t), B:string …)=A=B` | `'=' compares values of different types, tuple(t, t, t) and string, whose values in common Verse Core cannot compare` | none | yes: [Equality and the empty value](../LANGUAGE.md#equality-and-the-empty-value) | generic code: a type parameter's instance at run time ([empty-values.md](empty-values.md), part 2) |
| live variables | 50 | `Tests/upon.versetest:7`: `upon(1){2}` | parse error | all `verse_vm_only`; the Book's ch. 15 is marked "Unreleased Feature" | no | front-end, Core and runtime |
| nested functions and lambdas | 44 | `Tests/NestedFunctions.versetest:41`: `G():int = X` inside `F` | `a definition in a module must start at the module body's column` | 25 `verse_vm_only`; the Book's ch. 6 marks nested functions "Unreleased Feature" | yes: [Not supported in v1](../LANGUAGE.md#not-supported-in-v1), [closure design](closure-design.md), #492 | front-end and Core (closures) |
| type aliases | 40 → 1 | `Tests/Effects.versetest:305`: `t:=type{F()<converges>:void}` | `expected ':', found '('`: a function type written with a name for `_`, and `<converges>` | none | yes: [Type aliases](../LANGUAGE.md#type-aliases) | done ([After the type aliases](#after-the-type-aliases)) |
| variance of parametric classes | 38 | `Tests/ParametricTypes.versetest:72`: a covariant `bivariant_class(sub_class)` passed as `bivariant_class(super_class)` | `expected bivariant_class(super_class), found bivariant_class(sub_class)` | none | no | front-end: variance from the positions of a parameter |
| `set` forms | 34 | `Tests/LiveVariables.versetest:122` | `expected '=' or a compound assignment in set`; `set` through a tuple element | 26 `verse_vm_only` | yes: the Mutation row | front-end |
| localization | 34 | `Tests/Bugs/SOL-3887-MessageArray.versetest:decls`: `SOL3887Message<localizes>(S:string) : message = "--{S}--"` | `unsupported function specifier <localizes>` (#494) | none | yes: [effect contracts](../LANGUAGE.md#effect-contracts) | front-end and runtime (`message` values) |
| overrides of fields | 33 | `Tests/Attributes/override.versetest:33` | `A<override> must give a new default`; a field narrowed by an override (`Data<override>:int` over `any`) | none | no | front-end |
| `spawn` in a failure context | 29 | `Tests/Bugs/FORT-582630-BranchResult.versetest:16` | `spawn cannot be in a failure context` (#156) | 1 `verse_vm_todo` | yes (#156) | exposed by the harness's `<decides>` wrapping; front-end |
| empty containers | 28 → 20 (an empty `array{}` or `map{}` compared is the other operand's empty value) | `Tests/Operators/CompareString.versetest:29`: `assert{array{}=""}` | `the type of an empty array{} must be given` | none | yes: call packing needs "an inferable element type" | front-end: an element type from context, or a bottom element |
| class effect specifiers | 23 → 28 (5 module-scoped `var` cases of `weak_map.versetest`, which the parser refused, reach their key classes' `<allocates><computes>` now: [After weak maps and module-scoped vars](#after-weak-maps-and-module-scoped-vars)) | `Tests/Attributes/allocates.versetest:6`: `c := class<computes><allocates> { Value:int = 0 }` | `<computes> excludes the heap effects … that class/interface also has` | none | yes: construction effects (#508) | a message |
| other library functions | 23 | `Tests/GetCastableFinalSuperClass.versetest:60` | `unknown function 'GetCastableFinalSuperClass'` (15), `FitsInPlayerMap` (3, persistence), `signalable(t)` and `awaitable(t)` (3), `GetSecondsSinceEpoch` (2, a clock) | none | [the library note](book-library-functions.md) | features: #11, persistence, the concurrency interfaces, a time source |
| `weak_map` | 22 → 0 ([After weak maps and module-scoped vars](#after-weak-maps-and-module-scoped-vars): 18 agree, 1 not translatable, 4 under other causes) | `Tests/weak_map.versetest:32` | `unknown function 'weak_map'` | 1 `verse_vm_only` | yes: [Weak maps](../LANGUAGE.md#weak-maps), [Module-scoped variables](../LANGUAGE.md#module-scoped-variables), #491 | done: front-end only ([weak-map.md](weak-map.md)) |
| module constants of mutable classes | 21 → 4 (17 call the test runner's `MakeNull`, not translatable now) | `Tests/Bugs/FORT-721882-CallingFunctionWithNullObject.versetest:14` | `the constant NullTestObject would hold an object with var fields …: make it a function` | 17 `verse_vm_todo` | yes, in the message | front-end and Core (module state) |
| joins | 28 | `Tests/Bugs/2021-04-26-DisjointTypesAllowedInComparisonAndPointerDeref.versetest:4`: `0=(false? or 0)` | `the branches have different types: logic and int` (also `?int` and `?float`) | none | in part: unrelated types join at `any` ([any](../LANGUAGE.md#any)), not inside options or `or` | front-end |
| `true` and `false` as types | 20 | `Tests/Subtype.versetest:113`: `m0:subtype(true)` | `unknown type 'true'` | none | no; the Book's ch. 2 | front-end |
| block forms | 17 | `Tests/Operators/At.versetest:40`: `F at array:` and an indented block | `at` and `of` calls with a block (12), `profile:` (`unknown struct 'profile'`, 2), … | none | yes: [Supported](../LANGUAGE.md#supported), Blocks | parser forms (`of`, `at`) and features |
| `var` specifiers and accessors | 16 → 0 (12 agree, [After access specifiers](#after-access-specifiers); getter and setter accessors, 3, are counted under attributes, a misindented case under other syntax) | `Tests/Attributes/AccessLevelInheritance.versetest:444`: `var<private> Field<public>:int = 42` | `expected an identifier, found '<'` | none | no | parser and front-end |
| unnamed parameters | 14 → 10 | `Tests/FlowControl/Return.versetest:34`: `f(x:int):void={ g(:int):void={} }` | the forms of other features with an unnamed parameter: nested functions (2), type aliases (1), `castable_subtype` bounds (2), types as values, `:C=C{}`; extension methods (4) agree now | none | yes: [Supported](../LANGUAGE.md#supported), Functions | the features' |
| lambdas | 14 | `Tests/Literals/Function.versetest:5`: `()=>a` (valid syntax) | parse error: lambdas `(X:int) => X` (11, which the tests call an error outside a map literal), `(1+2)(3) {4}` (2), `a{b},(c){d}` (1) | none | no | parser form: `=>` refused outside a map literal |
| path literals | 14 | `Tests/Bugs/FORT-582128-PathLiteralAsValue.versetest:5`: `Alias:=import(/Verse.org)` | `unknown function 'import'` (13, 12 of them aliases of the test runner's modules); `/a,/b` at statement level (1); a path as a value gives "the path /a as a value is not supported" | none | yes: [Source text](../LANGUAGE.md#source-text) | front-end feature: `import` aliases (the Book's ch. 16) |
| operator definitions | 14 | `Tests/Bugs/2023-01-17-CharLiteralAsOperand.versetest:6`: `prefix'-'(Operand:char):char=Operand` used by `assert{-'a'}` | `expected '(', ':' or ':=' after 'prefix'` | none | no | parser and front-end (overloads exist) |
| `first` with generators | 11 | `Tests/FlowControl/first.versetest:202`: `first{I->X:array{10,20,30}; X > 15}` | "a generator X : source in first is not supported yet" | none | yes: [Mutation, macros, tooling](../LANGUAGE.md#mutation-macros-tooling) | front-end feature (the Book's ch. 7, "First Expressions") |
| ranges as values | 11 | `Tests/FlowControl/for.versetest:17`: `for(X:int=2 .. 3)` | `a range a..b can only be the source of a for clause` | none | no | front-end |
| subtyping into `any` | 9 | `Tests/Any.versetest:60`: `MapCount(Map)` with `Map:[int]string` for `[t]any` | `expected [t]any, found [int]string` | none | no | front-end |
| casts openverse proves impossible | 8 | `Tests/Cast.versetest:18`: `not i0[c0{}]` | `no class is below both c0 and i0, so i0[…] would always fail` | none | no | a message becomes a warning: the test expects a cast that fails |
| `<closed>` functions | 7 | `Tests/closed.versetest:16` | `unsupported function specifier <closed>` | 3 `verse_vm_only` | yes (#494) | front-end |
| partial modules | 10 | `Tests/Modules/PartialModuleDefinitions.versetest:157`: `A<public> := module:` twice | `module A is defined twice` | none | no; the Book's ch. 16 | front-end |
| empty and next-line bodies | 5 | `Tests/RuntimeErrors.versetest:52`: an `assert:` with only comments in it | `expected an indented function body`: the harness turns an empty `assert:` into `Main()<decides>:void =` with no body | none | yes: [Supported](../LANGUAGE.md#supported), Blocks | the harness (an empty `assert:` is valid) |
| archetype blocks | 36 | `Tests/FunctionAsType.versetest:183`: `X := test_function_as_type:` | `unknown struct 'test_function_as_type'`: types of the test runner (5); `X:sup_f(sub) := sub_f(sup):`, an archetype block after a declared type, in a module of `ParametricTypes.versetest` that its variance cases and its `:decls` include (31, reached once the module's type aliases parse, and for `:decls` its `(c1()){…}` too) | 2 `verse_vm_only` | yes: [Supported](../LANGUAGE.md#supported), Structs | none (the runner's types) |
| comparable interfaces | 4 | `Tests/ComparableInterface.versetest:5`: `interface<unique>` compared | `… Interface is a class (only <unique> classes are comparable …)` | none | in part: [Classes](../LANGUAGE.md#classes), `<unique>` | front-end, small |
| other brace forms | 3 | `Tests/Bugs/SOL-8557-InitializeVarMissesDefDest.versetest:1`: `option{native_class:` and the fields indented below | `expected ';', a new line or '}', found ':'`: an archetype block inside braces opened on the line above (2), `function(i:int){…}` (1) | none | no | parser form |
| named tuple elements | 11 | `Tests/Bugs/FORT-590869-NamedWithDefaultCoercion.versetest:9`: `Apply(G, (2, ?Y := 3))` | `unexpected '?'` (3); "a named parameter inside a tuple parameter … is not supported yet" (8, `NestedNamedTupleParameters.versetest`, `Where.versetest:14`) | all `verse_vm_todo` (the 3) | yes for the parameters: [the rules and a design](tuple-parameters.md) | parser and front-end: tuple types with named elements |
| `tuple()` overloads | 3 → 0 (`tuple()` is a type of its own) | `Tests/ExtensionFields.versetest:48`: `(X:tuple()).Extension()` beside `(A:int).Extension()` | `… defined twice with parameters a call cannot tell apart, (void) and (int)` | none | yes: `tuple()` is `void`, which overlaps every type ([Overloading](../LANGUAGE.md#overloading)) | an owner decision: a unit type of its own |
| type conversions | 3 | `Tests/Cast.versetest:59`: `logic(false)=false` | `expected '{', found '('` | none | no | parser form |
| quoted operator names | 2 | `Tests/TimSyntax.versetest:108`: `operator'<='` (valid syntax) | `char literal must be one character` | none | no | parser form of operator definitions |
| `generator` types | 1 | `Tests/generators.versetest:298` | `unknown parametric type 'generator'` | none | no | front-end feature |

Sizes: *a message* is a check in the elaborator with information it already
has; *a parser form* is new syntax lowered to something the elaborator
already handles; *a front-end feature* needs new elaboration; *Core or
runtime* needs new Verse Core or C runtime operations.

## After the parser forms

The survey's syntax causes were then taken by the parser, one rule each
(`docs/LANGUAGE.md` describes each where its neighbours are described). 450
cases more agree; no program of openverse's suites or of a frozen corpus of
2,533 generated programs changed its bytecode or its messages, but for
three tests of openverse's own that held the old readings (an empty class
body, a quoted tab and a quoted non-ASCII character refused); and the 39
cases that had agreed only through a parse error now reach a rule
openverse does not check ([Accepted](#accepted-where-the-tests-expect-an-error)).

| Form (cause when surveyed) | The rule | Cases | Agree now | Left |
|---|---|---:|---:|---|
| path literals | a `/` where an operand starts, before a letter or digit, begins a path (`/label[@label]{/ident}`), read as a name the elaborator refuses as a value | 213 | 198 | `import(/…)` aliases (13), `/a,/b` (1), qualified names (1) |
| empty and next-line bodies | a body after `:` may be empty wherever one may be written; a braced body's `{` may start the next line at the definition's column; a value after `=`, `:=` or `=>` on the following lines is their block | 160 | 86 | a later obstacle (69), the harness's empty `assert:` (5) |
| empty parentheses | `class()` has no parents; `t()` is `t` | 42 | 9 | types as values, `castable_subtype` (33) |
| unnamed parameters | `F(:t)` gets a name no program can write; a function type's parameter may be a signature | 123 | 27 | a later obstacle (81), other features' forms (15) |
| `. expression` forms | a body may be `.` and an expression on its line, wherever `:` or `{…}` may | 31 | 26 | `spawn` in a failure context, field defaults (5) |
| `if` without `then`, block forms | `if`, `for` and `first` take their clauses in `(…)`, or as `{…}`, `:` and a block, or `.` and an expression, then `then`/`do` or nothing (the clause macro); `array`, `map`, `option`, `logic` and `spawn` take `:` and `.` bodies | 92 | 35 | `at`/`of` calls (12), `profile:` (2), a later obstacle (43) |
| archetype blocks, other brace forms | `X := c:` and the fields indented; a construction's or an array's items are separated by commas, or by `;` and new lines, not both | 35 | 6 | the test runner's types (5), a later obstacle (24) |
| `first` with generators | `first` reads its clauses as `for` does | 11 | 0 | a generator in `first`, refused as not supported (11) |
| non-ASCII char literals | a non-ASCII character in quotes is a `char32`; a tab may be quoted | 15 | 5 | `ToChar32` (7), quoted operator names (2), … |
| float literal suffixes | the suffix `f64`; `f32`, `f16` refused as not supported | 14 | 13 | `1e2,1e2f16,…` at statement level (1) |
| other syntax | `;` sequences as arguments and as a `case`'s value; `;` may end a braced block; definitions on a line separated by `;` or `,`; a `;` that ends a line does not take the next block's item (the side finding below); a block comment before a line's first token does not indent it | 205 | 37 | other syntax (156; see [Refused](#refused-where-the-tests-expect-a-valid-program)), a later obstacle (12) |

Nested tuple parameters (37 when surveyed) had been taken by #591 before;
the 17 cases left under that cause are lambdas (`(X:int) => X`, which the
tests call an error outside a map literal) and tuple destructuring.

## After the rule checks

The internal errors were then fixed ([Internal errors](#internal-errors)),
and the accepted refusals that are one check each were refused, one rule
each where its information is (`docs/LANGUAGE.md` says what each refuses).
With the parser forms, 229 cases more agree and none less (`compare`
against the baseline of the parser forms). The counts are of the accepted
refusals with the parser forms → now; the frozen corpus kept its bytecode
but for 12 generated programs that define an interface `first`, which the
Book refuses.

- **Reserved names** (83 → 2): `reservedNames` (`Front/Syntax.lean`): no
  definition at any scope; a top-level `using` must be followed by `{`.
  Left then: `Union.versetest:23, 290` (VerseVM-only), which expect a
  module-level `X := e` to state its type (ch. 16): refused since [the
  readings audit](#after-the-readings-audit).
- **Duplicate definitions** (24 → 18) and **constructor-like functions**
  (5 → 1; also `ParametricTypes.versetest:324`): only functions share a
  name in a scope; a local cannot take an overloaded function's name. Left:
  `ShadowDefinition.versetest` (15), `Enum.versetest:121`,
  `QualifiedIdentifier.versetest:310, 315` and `Overloading.versetest:171`:
  a member of a module, class or enum named like an enclosing definition,
  which ch. 10 ("Shadowing and Qualification") refuses and openverse's
  lexical lookup resolved inner-first; refused since, but for `:315`
  ([After qualified names](#after-qualified-names)).
- **Cyclic initializers** (4 → 2): a constant that depends on itself. Left
  then: `DefaultValueAssignment.versetest:102, 128`, a constant using one
  defined after it in its own scope: refused since [the readings
  audit](#after-the-readings-audit).
- **Float literal out of range** (12 → 0), **comment lexing** (6 → 0), and
  comments inside strings (2 different outputs → 0): the lexer.
- **Misplaced specifiers** (32 → 0), **`<final>` members** (13 → 1),
  **`<concrete>` classes** (22 → 7), **`<castable>`** (7 → 0),
  **`<persistable>` structs** (6 → 1; also `persistable.versetest:79, 91`):
  one table of where each specifier goes and what it requires
  (`EffectPolicy.specifierPlaces`); a class's `<final>` fields are kept as
  `$final:F` among its specifiers, so none is overridden below or set by a
  construction. Left: `final.versetest:125` (a final method and an
  interface's method of one name); a class below a `<concrete>` one with
  fields without defaults (7: `concrete.versetest:38, 76`,
  `SOL-3366:8, 15, 24`, `SOL-7781:28, 54`), which ch. 10 allows ("A concrete
  class may have subclasses that are not concrete") and the tests refuse;
  an enum field of a `<persistable>` struct (`persistable.versetest:59`:
  the parser does not keep an enum's `<persistable>`).
- **Redundant effects** (9 → 0): `<transacts>` implies the others.
- **`defer` as a block's value** (5 → 0): a `defer:` must have code after
  it in its block.
- **Control forms** (17 → 7): `return` in a constant's value or a field's
  default, and a `for` of literal clauses only. Left: a non-suspending arm
  of `race`, loops with no `break` (`Break.versetest:118, 161`), `return`
  inside a `for` that is a function's value (`Return.versetest:114, 117`),
  `using{/localhost}`.
- **Unreachable code** (39 → 30): a `case` arm after `_` or repeating one.
  Left: code after a `return` or `break`, `return` in a failure context or
  not in tail position, `_` on a closed enum whose values are all named and
  `return 3` in a `:void` function (the Book calls the last two warnings).
- **Failure where it is not allowed** (35 → 30): `not` of an expression
  that cannot fail. Left: the left of `or` (refused since [the readings
  audit](#after-the-readings-audit), once a `set` through a map's key, as
  the Book's own `RollbackTortureTest`'s `(set Map[I] = I) or Err()`, can
  fail), named-parameter and field defaults that fail or suspend, loop bodies
  inside failure contexts, `for` filters that cannot fail, effects of
  `spawn` and of unannotated functions.

## After the type aliases

Type aliases were then built, `name := t` and `name(u:type, …) := t`, with
the rules of [type-aliases.md](type-aliases.md): an alias is written out
where it is used before elaboration, so it is the type it names everywhere
([LANGUAGE.md](../LANGUAGE.md#type-aliases)). Against the baseline of the
rule checks, 27 cases more agree, 12 agree no more and none gives another
result; no program of openverse's suites or of the frozen corpus changed
its bytecode or its messages.

- **Agree now** (27): `TypeAlias.versetest` 31, 32, 37, 38, 39, 200, 203,
  206, 209, 212, 215, 218, 221, 224; `ParametricTypes.versetest` 20-23,
  307, 310, 315, 316, 609; `Tuple.versetest` 138, 165 and its `:decls`;
  `Bugs/FORT-995029-CrashHashingDynamicallyTypedMapKey.versetest:decls`.
- **Refused for their rule now** (25 agreements, 21 of them parse errors or
  missing features before, 4 refusals by another rule): an alias that names itself (`ParametricTypes.versetest`
  250-254, 273-275, `Tuple.versetest:174`, `SOL-4171-CallStackOverflow:5`,
  `2023-01-18-ClosedWorldFunctionBodyReferencesItself:3`), one used before
  its definition (`TypeAlias.versetest` 41, 42, 201, 204, 207, …, 225,
  `Tuple.versetest:179`), an alias that is no struct or class constructed
  (106) or used as a function (109). With `QualifiedIdentifier.versetest:160`
  (`Test := …` in a module, now refused where aliases are decided), the
  agreements a rule check gives went from 982 to 1,004.
- **Accepted refusals** (12, the cause "access specifiers"):
  `TypeAlias.versetest` 228-231 and 233-239 and `DigestVisibility.versetest:115`,
  a `<public>` alias of an internal class, enum, struct or interface, or of
  a compound of one (error 3593). They agreed before only because no alias
  parsed. The missing rule is the access specifiers' "a `<public>`
  definition names only public types", which openverse enforces for no
  definition (functions included): one rule with the others of that cause,
  an owner's decision.
- **Left** under type aliases: `Effects.versetest:305`, a function type
  written `type{F()<converges>:void}`. The 25 `TypeAlias.versetest` cases
  whose program includes the module `AliasesOfClasses` (23, 24, 53-55, 64,
  65, 76-78, 88, 89, 168-193) stop at its qualified definition
  `(AliasesOfClasses:)e<public> := (AliasesOfClasses:)d` (qualified names);
  without that line, the module's aliases of classes, enums and `int` run
  in both implementations. Others went past their aliases to another
  obstacle: an archetype block after a declared type in a module of
  `ParametricTypes.versetest` (30 cases, archetype blocks; its `:decls` too,
  once the library functions' `(c1()){…}` construction parses),
  `comparable` as a type (`FORT-995029` 10, 18), an alias `i() := i(void)`
  that shares its name with the parametric interface `i` ("defined twice",
  `SOL-7849` 10 and `:decls`), a field narrowed by an override
  (`BPVMOnly/RefinedMapKeyInterfaceOverride:97`).
- The `scoped{…}` definitions (`scoped_X := scoped{X}`), access scopes and
  no types, are counted under other syntax now (4 from type aliases, 5 from
  other type rules).

## After the library functions

The functions the tests call that openverse lacked were then added, each
written with Verse Core's existing operations, so Core, the proofs, OVBC and
the runtime are unchanged; [the library note](book-library-functions.md)
pins each from the Book's chapters, its Runtime API reference and Epic's
published API, and states what is left. 71 cases more agree, none fewer,
and the programs of openverse's suites and corpus keep their bytecode.

| Cause (cases) | Added | Agree now | Left |
|---|---|---:|---|
| character conversions (147) | the methods `ToCodeUnit`, `ToCodePoint`, `ToChar[]`, `ToChar32[]`, `ToAsciiChar32[]`, `ToAsciiString` (7 more of their own test file, counted under other causes, agree too) | 2 | 145: free `ToChar(N)`, `ToChar32(N)` |
| other library functions (94) | `Clamp` of ints and floats, `Sgn`, `F.IsFinite[]`, the built-ins of one signature as function values, array methods of a tuple receiver | 59 | 12 not translatable (`FloatConstants`), 1 comparison of an int and a float, 22 features |
| lambdas and destructuring (17) | `(X:t, _, Z:u) = e` | 3 | 14 lambdas |
| other syntax (195) | `let{…} do …`, `(t(int)){…}` | 4 | 191 |
| bitwise functions (159) | pinned, not implemented (built since: [After the Book's primitives](#after-the-books-primitives), 103 agree) | 0 | 159 |

The two steps, each measured from the rule checks' baseline, add up: with
both, 7,143 cases agree (7,057, 27 and 71 more, 12 fewer), 2,250 are
refused, 308 accepted where the tests refuse and 85 differ; no case agrees
with one alone and not with both. One case changes cause only with both:
`ParametricTypes.versetest:decls`, which needs both an alias and a
`(c1()){…}` construction to reach its archetype block.

## After extension methods

Extension methods were then built, with the rules and the design of
[their note](extension-methods.md) ([LANGUAGE.md](../LANGUAGE.md#extension-methods)):
`(R:t).M(…)` is an ordinary function whose first parameter is the receiver,
which a call `X.M(…)` finds in scope as a function's name is found. Against
the baseline of the library functions, 37 cases more agree, none fewer, and
none became an accepted refusal or a different result; the programs of
openverse's suites and of the frozen corpus keep their bytecode and
messages.

| Cause (cases) | Agree now | Left, and their cause now |
|---|---:|---|
| extension methods (53) | 33 | `LogicalOr.versetest` 133-140, an `or` of `?E` and `?F` (joins, 8), and its `:decls`, `comparable` (1); `ExtensionFields.versetest` 48, 70 and `:decls`, overloads on `tuple()` and `int`, which openverse's `tuple()`, the `void` that overlaps every type, cannot tell apart (`tuple()` overloads, 3); `NestedNamedTupleParameters.versetest` 68, 82, 92, named parameters inside a tuple parameter (named tuple elements, 3); `FORT-722788` `:13` and `:decls`, a module defined twice (partial modules, 2); `FORT-1126351-GenericSignalableReentrantConvertCrash` `:70` and `:decls`, `signalable(t)` (other library functions, 2); `MapMemoryLeak.versetest:11`, `map{}.RemoveKey[0]`, the type of an empty map for a generic receiver (other type rules, 1) |
| unnamed parameters (14) | 4 | `ExtensionFields.versetest` 171, 172, 178, 179 (`(:without_Q).Q():int=11` beside a class with a field `Q`) agree; 10 other features' forms |

- **Refused for their rule now** (11 expected errors that agreed by a parse
  error of the form): an extension method as a value
  (`ExtensionFields.versetest:61`, 3506), one with the parameters of its
  class's or interface's method (85, 90, 95, 100, 3532), overloads on
  `[]int` and `[int]int` (139, 3532), a subclass's method and an extension
  method that a call fits both (107, 3518), a bare call in a method that
  fits a function and the extension method with `Self`
  (`SOL-3515-CallingExtensionMethodWithoutSelf.versetest:23`, 3518), and a
  call of an extension method of a module the scope does not open
  (`FORT-559416-AddExtensionMethodsToForgotUsingMessage.versetest:5`, 3506).
  `OutOfScopeOverloads.versetest:24, 31` (3509) are refused for their
  overloads on `tuple()` and `int`; without that overload, the submodule's
  is not a candidate either. The receivers the tests refuse
  (`ExtensionFields.versetest` 8, 12, 55, 57, 79, 81: two parameters or
  none) and `(I:int).Member:int` (11) are the parser's refusals. So the
  agreements a rule check gives went from 1,004 to 1,015.
- **The harness.** The test runner's own extension methods `TakeExtension`,
  `PlusTwo` and `TestParametricExtensionMethod` ("The method is defined in
  /Verse.org/Tests/VerseTestScriptCmd", `ExtensionFields.versetest:157`) are
  test-runner names: 3 cases, refused before, are not translatable. Causes:
  the form of extension methods counts parse errors only; "a named parameter
  inside a tuple parameter … is not supported yet" counts under named tuple
  elements (5 cases its "not supported yet" had put under class and
  function specifiers: `NestedNamedTupleParameters.versetest` 18, 29, 39 and
  `:decls`, `Where.versetest:14`); `signalable(t)` and `awaitable(t)` under
  other library functions (`ParametricTypes.versetest:907` from other type
  rules); and `tuple()` overloads is a cause of its own.

## After the empty value

The owner decided that openverse follows the Book on the equality of empty
values, and then that it goes by the Book in everything; the rules and what
is left are in [empty-values.md](empty-values.md)
([LANGUAGE.md](../LANGUAGE.md#equality-and-the-empty-value)). `=` and `<>`
now compare values of any two comparable types: two values of different
types are equal only as one value, the empty value (`false`, `()`, a
`void` value, `""`, `array{}`, `map{}` and an empty option), a tuple and the
array of its elements, or one struct at two instances, part by part; an
empty `array{}` or `map{}` compared is the other operand's empty value; and
`tuple()` is the type of the empty value alone, no longer `void`. Against
the baseline of extension methods (7,180 agree, 2,210 refuse, 308 accept, 85
different), 74 cases more agree, 2 move from a refusal to a different
result, and none agree less: 7,254 agree, 2,164 refuse, 307 accept, 58
differ.

| Cause (cases) | Agree now | Left, and their cause now |
|---|---:|---|
| empty values are one value (32, different output) | 28 | `BoolQuery.versetest` 3, 4, `LogicalAnd.versetest` 29, `Precedence.versetest` 121: the value of `true?`, `true` in openverse, the empty value in the tests (empty values are one value, 4) |
| comparisons of different types (51, refused) | 35 | `CompareString.versetest` 168 to 182 and `:decls`: a tuple of a type parameter and a string, in generic code (comparisons of different types, 16) |
| empty containers (28, refused) | 6 (`array{}` or `map{}` compared, typed by the other operand: `Array.versetest` 88, 89, `FlowControl/for.versetest:352`, `Operators/CompareString.versetest` 29, 69, `Void.versetest:295`) | 20, empty literals elsewhere; `for.versetest` 317, 344 now differ (below) |
| `tuple()` overloads (3, refused) | 3 (`ExtensionFields.versetest` 48, 70, `:decls`) | none |
| a parametric struct compared across instances (1, different output) | 1 (`CompareStruct.versetest:43`) | none |
| other type rules (accepted) | 1 (`Void.versetest:223`: `X:tuple() = (1, 2)` is refused) | |

- **Moved, not agreeing:** `FlowControl/for.versetest` 317 and 344,
  `array{} = for(…) {I}`, were refused for the untyped `array{}`; they now
  compile and differ for the documented rollback of a `for` iteration
  (that cause, 8 → 10).
- **Not taken, from the tests:** `false` where a map is expected
  (`Map.versetest:343` refuses it, though the prose of chapter 2 allows
  it; it agrees, refused), and `true` as a type name
  (`FORT-582630-BranchResult.versetest:3` refuses `Result:true =
  branch:…`, which openverse, whose `branch:` gives `void`, would accept;
  the 20 cases of unknown `true` and `false` types stay refused).
- **The programs of openverse's suites and the frozen corpus** keep their
  bytecode but one, `tests/verse/empty_literal_compared.verse`, whose
  comparisons of empty values of different types now hold, as the Book
  says; the overload messages say `tuple()` where they said `void`.
- **Verse Core's equality** then became Verse's for the empty value at
  every depth (`Value.veq`, [empty-values.md](empty-values.md#4-design-b-as-built)):
  no case of the Book's tests changes verdict (a fresh run at main
  `7bf6dbd` gives the baseline again, 7,374 agree), as none
  compares empty values held two ways inside containers or through
  generic code; the 16 refused comparisons of a tuple of type parameters
  and a string stay refused.

## After qualified names

Qualified names were then built, with the rules of
[qualified-names.md](qualified-names.md): one resolver for every qualifier,
`(M:)x`, `(c:)m`, `(e:)v`, `(local:)X`, paths and `X.(M:)F(…)`, in uses and
in definitions' heads ([LANGUAGE.md](../LANGUAGE.md#qualified-names)); then,
on the owner's decision to follow the Book, its shadowing rule: no
definition takes the name of one around it unless qualified
([LANGUAGE.md](../LANGUAGE.md#shadowing)). Against the baseline of main
`d058cfd` (the empty value), 120 cases more agree and none fewer: 102 by
the qualified names, 18 by the shadowing rule; 25 accepted refusals agree
now and none was added. No program of openverse's suites or of the
frozen corpus changed its bytecode or its messages but those that shadow
(below).

- **Agree now by the qualified names** (102): `TypeAlias.versetest` 23 (the
  module `AliasesOfClasses` of [After the type aliases](#after-the-type-aliases):
  23, 24, 53-55, 76-78, 88, 89, 168-193); `QualifiedIdentifier.versetest`
  21 (10, 11, 15, 58, 78, 176, 297, 305, 308, 313, 318, 324, 347, 357, 368,
  373, 378, 383, 412, 452, 463); `Pointers.versetest` 19 (53-58, 72-77,
  87-92, `:decls`); `Modules/Module.versetest` 7 (211-217, `:decls`);
  `Type.versetest` 6 (59-63, `:decls`); `Bugs/SOL-3564` 5 (90, 107, 122,
  150, 176); `Bugs/SOL-7778` 4 (38, 54, 58, `:decls`; 58 compares two enums' values,
  which the empty value's comparisons allow); two each in
  `Bugs/2020-04-24-ArrayConcatIntoItself` (28, 31), `Bugs/FORT-951162` (13,
  `:decls`), `Interface.versetest` (135, 136),
  `Modules/ModuleDefinitions.versetest` (59, 222) and `VarSet.versetest`
  (109, `:decls`); one each in `Bugs/SOL-3104`, `Bugs/SOL-7579` and
  `DefaultNamed.versetest` (`:decls`), `Classes/QualifiedMethodInheritance`
  191, `Enum.versetest` 114, `ShadowDefinition.versetest` 14 and
  `TimSyntax.versetest` 94 (`a.(/c/d:)b`). `QualifiedIdentifier:58` and
  `:378` were counted under types as values. By step, measured on main
  `8f7719e`: the resolver with qualified definitions and uses, 52;
  `(local:)`, 48; path qualifiers, 1.
- **Agree now by the shadowing rule** (18, all accepted refusals before):
  `ShadowDefinition.versetest` 4, 271, 276, 281, 286, 291, 296, 328, 329,
  331, 332, 336, 337, 340, 341; `Enum.versetest` 121;
  `QualifiedIdentifier.versetest` 310; `Overloading.versetest` 171.
  `ShadowDefinition:14` and `Modules/Module:211-217`, which qualify their
  inner definitions, keep agreeing. Left: `QualifiedIdentifier:315`,
  `enum{public}`, a value named like the built-in attribute `public`, which
  openverse knows as no definition.
- **Accepted refusals that agree now by the qualified names** (7):
  `SOL-3564` 90, 107, 122, 150, 176, a qualified call through a class that
  inherits or overrides the method (the qualifier names the class or
  interface that introduces it); `QualifiedIdentifier` 78 (`using{(A:)B}`
  with no `A`) and 297 (`using{(local:)M}`).
- **Rules the new forms reached**, which openverse now checks, so that no
  case moved to "accepts" or "different result": the effects' names and
  `true` as definitions' names (`Effects.versetest:355-363`,
  `Enum.versetest:57`: `(m:)suspends := class{}`, 10 cases that had agreed
  through the parse error); a class's qualified member used bare beside an
  outer definition of its name, ambiguous (`ModuleDefinitions.versetest:71,
  88, 238`); and a field two classes declare, read through a qualifier
  (`InterfaceWithFields.versetest:247, 260`), which would have read
  openverse's one merged field and given a different result: refused.
- **Left under qualified names** (26 refused, 6 accepted): two members of
  one name in a class, `(c:)m` beside an inherited `m` or a field of two
  declarers (ch. 10, "Methods with Same Name"; 9: `SOL-3564:57, 66, 201`
  and `:decls`, `ShadowDefinition:113, 199`, `InterfaceWithFields:247, 260,
  562`), with members at uneven columns too (3, `ShadowDefinition:128, 145,
  146`); the test runner's package path or name (5:
  `QualifiedIdentifier:474, 482, 483`, `/Verse.org/VerseTests/…`;
  `Classes/QualifiedMethodInheritance:153` and `:decls`, `(VerseTests:)FE`);
  other features written with a qualifier (9): qualified extension method
  definitions (`SOL-8768:19`, `:decls`), the runner's `snippet{…}`
  (`Modules/Module:230, 232`), a union (`Union:80`), `(super:)X` as an
  unused value (`ParametricFunctions:119`), `(super:)` with an overloaded
  method (`Super:56`), a qualified macro `(/Verse:)for(…)` (`TimSyntax:325`)
  and `(/Verse.org/Verse:)GetSecondsSinceEpoch`, a function openverse lacks
  (`GetSecondsSinceEpoch:16`). Accepted: `SOL-3564:7, 18, 32, 45`, a call
  `(a:)F()` of the method being overridden through the class that
  introduces it, from the override (the tests' warnings 2003 and 2004, "use
  `(super:)`"), and `Super:183, 238` (`(super:)` of a method no class above
  has, in a method no case calls; `(super:)` in a class block): rules of
  `(super:)` openverse lacks.
- **Moved to another cause** (43): 33 `ParametricFunctions.versetest` cases,
  whose modules' qualified classes parse, reach `Obj.Get, Obj.Set` as a
  function's value (other syntax); `SOL-7503` (4: a struct, class or
  interface defined twice, told apart by its parameters),
  `QualifiedIdentifier:decls` (the runner's modules) and `TypeAlias:64, 65`
  (`ClassOfC0`, a type as a value) (other type rules); partial modules
  (`PartialModuleDefinitions:172, 176`) and `<localizes>`
  (`Localization:decls`).
- **Programs that shadow.** Of openverse's suites, 32 programs and 5 error
  tests that put a definition beside one of its name around it now qualify
  the inner one or rename (one error test, a capture the inlining refused,
  became a program); of the frozen corpus, 91 of 2,533 generated programs
  are now refused (74 a field, 17 a method `ma.Score`, named like an
  enclosing definition), and the generators no longer write such names.

## After the readings audit

[The readings audit](readings-audit.md) took every reading of LANGUAGE.md's
table, and the readings elsewhere that this survey names, against the
Book's prose and tests, and changed those the Book contradicts and the
front end can follow, one commit each. Against the baseline of qualified
names (7,374 agree, 2,069 refuse, 282 accept, 58 differ), 16 cases more
agree and none less: 7,390 agree, 2,066 refuse, 277 accept, 50 differ.

| Reading changed | Agree now |
|---|---|
| `ConcatenateMaps` lays the second map's pairs down after the first's, a key both have at the second's place (the API reference); it takes two maps (ch. 3) | `Intrinsics/ConcatenateMaps.versetest` 21, 33 |
| a failing range bound of a `for` gives no iterations, its effects rolled back (ch. 7) | `FlowControl/for.versetest:317`, `SoftwareTransactionalMemory.versetest` 74, 81 |
| an `and` is one scope, its left's names visible on its right (ch. 7) | none (`SOL-1830-LocalVariablesCanEscape.versetest` 26, 27 agreed by a refusal at another place, and still agree) |
| `set P op= e` evaluates `e`, then reads `P` | `ArrayAppend.versetest` 7(v), 140, 183 |
| a constant names only constants defined before it in its scope | `Features/DefaultValueAssignment.versetest` 102, 128 |
| a top-level constant states its type (ch. 16) | `Union.versetest` 23(v), 290(v) |
| a `set` through a map's key can fail (its key's reference is `<decides>`), so it is in a failure context | `Mutability.versetest:248`, `Bugs/FORT-623803-STMRollbackAfterReturn.versetest` 22 and `:decls` |
| the left of `or` must be able to fail | `Operators/LogicalOr.versetest:143` |

Left, with their designs in the audit: the rollback of a `for` iteration
(7: `for.versetest` 344, 362, 371, 392, `Range.versetest` 140, 159,
`SoftwareTransactionalMemory.versetest` 88), `return` and `break` out of a
failure context (deeply load-bearing: 88 of openverse's test programs and
302 of the frozen corpus use them), commas in blocks (4, and 22 parser
cases), `ToString` of a float (7, the C runtime and Core) and the
scheduler rows; comparison chains (1) are where the Book disagrees with
itself, and `ArrayAppend.versetest:12` (VerseVM-only) writes through a
reference taken before `e`, which openverse's values do not.

**The programs whose bytes or output changed**, each checked as the
reading's (the byte-identity oracle over the suites and the frozen corpus
of 4,826 generated programs; a program whose bytes changed was run with
both compilers):

- *`ConcatenateMaps`*: `concatenate_maps(_more)` and the void-key case of
  `bound-concatenate-maps(-control)` print the new order (a `[void]int` map
  keeps one pair); `bound-concatenate-state-control` changed bytes only.
- *`and`*: 70 generated choice programs (`choice-*`) and the tests
  `choice_and`, `choice_logic_functions`, `multi_frame_seq_lifted` changed
  bytes, not output (the `and` is lifted as one block);
  `concurrency_prelude_and_scope_real_cast` and the two `and` scope error
  tests were rewritten for the new scope.
- *`op=`*: 631 programs changed bytes (a new value with an effect is
  computed first); 572 print what they did. 22 generated `mv-*` programs
  print otherwise, each exactly as the mv model of the corpus's commit
  predicts once its sets read the old value after the right side; the
  37 tests that held the old order were rewritten to check the Book's (the
  audit lists them), and the rational fuzzer's model reads the old value
  after its right side.
- *constants*: `generics.verse` (a later constant, now defined first); 10
  tests and 7 generated `gadt_waiting_contexts-*` programs had an untyped
  top-level constant (refused now; the tests and the generator give its
  type).
- *a map's `set`*: programs that set a map's key change bytes (`true?`
  after the insert); 14 generated `classes-*` programs, 9 tests and one
  contract of `tests/lean/MetadataStorage.lean` set one outside a failure
  context (refused now; the generator and the tests write
  `if (set M[k] = v) {}` or a clause).
- *the left of `or`*: 282 generated `mv-*` programs have an `or` whose left
  cannot fail (refused now); the mv model wraps its left in a comparison
  that holds (`X <> 1000003`), and regenerated at those seeds its 281
  programs that run agree with the model.

## After access specifiers

Access specifiers were then built, with the rules of
[access-specifiers.md](access-specifiers.md): what each of `<public>`,
`<internal>`, `<protected>`, `<private>`, `<scoped{…}>` and
`<epic_internal>` admits, where each may be written, overrides, `var<…>`'s
write access, constructors, and the rule that a definition exposes nothing
less visible than itself ([LANGUAGE.md](../LANGUAGE.md#access)). Against
the baseline of the readings audit (main `ce5e444`: 7,390 agree, 2,066
refuse, 277 accept, 50 differ), 145 cases more agree and none fewer: 7,535
agree, 2,028 refuse, 170 accept, 50 differ. Every accepted refusal of the
cause "access specifiers" agrees (107):

| Rule | Cases |
|---|---:|
| where a specifier may be written, one in a place (3594, 3543, 3642): `ArchetypeAccessSpecifiers` 43, 45, 49; `Classes/AccessSpecifiers` 350, 355, 360, 364, 447-464; `InterfaceAccessVisibility` 36-38; `Interfaces/AccessSpecifiers` 256, 261; `Modules/Module:36`; `ModuleDefinitions` 129, 130, 315, 316; `scoped:91` | 24 |
| none on an override (3650): `AccessLevelInheritance` 13, 23, 43, 55, 130, 711, 761, 787, 799, 811 | 10 |
| a member used where its access does not admit it, through a value or bare (3593): `Classes/AccessSpecifiers` 51-132, `Interfaces/AccessSpecifiers` 51-132 (12), `AccessLevelInheritance` 676, 835, `SOL-5564:3` | 15 |
| a constructor, `class<internal>` and `class<protected>`, in a construction or as a parent: `ArchetypeAccessSpecifiers` 15, 22, 36; `Classes/AccessSpecifiers:438`; `InterfaceAccessVisibility:9`; `ParametricTypes:478` | 6 |
| an override of a member its class may not use: `AccessLevelInheritance` 33, 67, 751, 823; `Classes/AccessSpecifiers:467` | 5 |
| a signature that names something less visible (3593): `DigestVisibility` 20, 27, 72-103, 115; `TypeAlias` 228-239 (11); `ParametricTypes` 1260, 1272 | 22 |
| a field with no default less visible than its constructor: `Classes/AccessSpecifiers` 205, 212, 412-427; `Interfaces/AccessSpecifiers` 285-306 | 22 |
| a specifier that is no keyword and names no access level: `Attributes/intrinsic` 4, 5, 9 | 3 |

And 38 valid programs it refused agree: `var<w> X<r>` parses (12:
`AccessLevelInheritance` 257, 270, 299, 344, 357, 369, 429, 444, 493;
`scoped` 496, 509; `InterfaceWithFields:636`); `<scoped{…}>` and `S :=
scoped{…}` (19: `AccessLevelInheritance` 142, 159, 181; `scoped` 5, 12,
19, 26, 33, 53, 60, 381, 410, 419; `SOL-7898` 151, 172, 182, where a member
a `using` opens that the use may not see is no candidate; `Interface` 338,
358, 368); and `<epic_internal>` (7: `DigestVisibility` 122, 128-130, 153,
155, 157). 12 of the 107 are refused by checks the parser makes (where a
specifier goes, and none on an override), which the harness counts as
refused by the parser.

- **Left** in these files: `AccessLevelInheritance` 605, 619, 849 and
  `Modules/Module:167` (definitions at column 3 of the test file, other
  syntax), 669 and `:decls` (a module defined twice, partial modules), 863
  (an override of a field with no new default, overrides of fields);
  `ComparableInterface:37`, `ModuleDefinitions` 164 and 279 and
  `Interface:33` for other causes; getter and setter accessors (3). The
  package-scoped cases (`vpackage`, `CanCallerAccessEpicInternal/`, most of
  `Modules/AccessSpecifiers` and `scoped`) are not translatable.
- **Programs.** No program's bytes changed (the byte-identity oracle over
  every suite and the frozen corpus). Six of openverse's tests used a
  class's internal field or method from outside its module and now mark it
  `<public>`; no program of the frozen corpus is refused, as its generators
  write no module whose members are used outside it.

## After `comparable`

`comparable` is a type ([its design and what it rests
on](comparable-type.md), [LANGUAGE.md](../LANGUAGE.md#comparable)): a value
of every comparable type converts to it boxed, `=` with it compares value
and type, it keys maps and joins unrelated comparable types, and a generic
function's type parameter is boxed by the evidence of its
`subtype(comparable)`. Against the baseline of access specifiers (main
`9263665`: 7,535 agree, 2,028 refuse, 170 accept, 50 differ), 135 cases
more agree and none less: **7,670 agree, 1,893 refuse, 170 accept, 50
differ** (re-recorded from a fresh run; the same 135 against the readings
audit's baseline).

| Cause before | Cases | Agree now | Left |
|---|---|---|---|
| `comparable` as a type | 126 | 100: `Comparable` 41 (the generic `Equal` and `NotEqual` included), `EnumCompare` 12, `RollbackTortureTest` 10, `SOL-5496` 7, `CompareString` 6, `ParametricTypes` 4, `BinaryAddArray` 4, `Attributes/unique` 4, `Map` 3, `Any` 2, `LogicalOr` 2, and `CompareRational`, `NamedParameterOverloads`, `FlowControl/Case`, `ComparableInterface`, `SOL-6529` one each | 26 |
| comparisons of a tuple of type parameters and a string | 16 | 16 (`CompareString` 168 to 182 and `:decls`, by boxes) | 0 |
| joins of comparable types | 16 | 16 (`Any` 111 to 126: `?int` and `?float` at `?comparable`; `LogicalOr` 133 to 140: `?E` and `?F`) | |
| others | 3 | `BinaryAddArray:45` (`[]int + []float`), `ConcatenateMaps:60` (`[string]int` and `[string]float`), `DisjointTypesAllowedInComparisonAndPointerDeref:3` (an `if` of an int and a string compared) | |

The 26 left need other features: `concrete_subtype(comparable)` (10,
`MetatypeConcreteSubtype`), a field overridden at a narrower type (4,
`MetatypeConcreteSubtype` 116, 284, 289, 294), variance of parametric
classes and interfaces at `comparable` (6, `SOL-6739`), a function type's
join at a parameter of type `comparable` (1, `Comparable:216`,
VerseVM-only), `weak_map` (1), a `set` through a call (1, `Map:472`) and
`GetRandomInt` (2, `FORT-995029`).

**The programs whose bytes or output changed** (the byte-identity oracle
over the suites and the frozen corpus, against the base, main `7bf6dbd`
with #602; a program whose bytes changed was run with both compilers in
Lean and C): none's output changed. 111 changed bytes: 109 because two
comparable types with nothing in common now join at `comparable`, not
`any` (ch. 1, 1276; ch. 14): 98 generated `heterogeneous-*` programs (a
choice of an int and a string), and the tests `any`, `if_join_order`,
`choice_heterogeneous_contracts`, `choice_heterogeneous_fields`,
`choice_branch_calls_join`, `choice_dictionary_associated_later_argument`,
`choice_dictionary_correlated`, `choice_first_unrelated`, `choice_more`,
`class_cast_refine_first_join`, `class_cast_refine_if_type`; and 2 because
generic code now compares a type parameter with another type by boxes
(`generics` and `empty_values_nested`: `X = true`, `X = false`, `X = ""`).
Three error tests changed their message: `array_elements_differ` (a
`[]comparable` now: "no ToString for comparable"; `array_elements_any`
keeps the `[]any` case), `concatenate_maps_types` (maps of an int and a
string join at `[int]comparable`; the refusal is now of a class value) and
`qualified_path_not_type` (the built-in types listed include
`comparable`); three compile now and compare as the Book does, so they
left `tests/errors`: `eq_core_values`, `eq_core_params` and
`eq_generic_tuple_string` (their cases are in `tests/verse/comparable_type`
and `comparable_generic`).

## After the load-bearing readings

[The readings audit](readings-audit.md#the-load-bearing-readings-built)
had designed four readings and left them, as load-bearing. Three were then
built, one commit each; the rollback of a `for` iteration was built later
([what a `for` undoes](#after-what-a-for-undoes)). Against
the baseline of `comparable` (main `77bc509`: 7,670 agree, 1,893 refuse,
170 accept, 50 differ), 62 cases more agree and none fewer: **7,732 agree,
1,869 refuse, 136 accept, 46 differ** (re-recorded from a fresh run; the
same 62 against the baseline of access specifiers).

| Reading | Agree now |
|---|---|
| warnings (the Book's 2000, 2002, 2302): code never reached, a `return` of a value in a `void` function, a `_` after a closed enum's every value, printed `FILE:LINE:COL: warning: …` and compiled; the harness takes an expected error whose codes are all warnings as satisfied by a warning | 17: `FlowControl/Reachability.versetest` 5, 11, 23, 39, 57, 76, 91, 99, 100, 107, 108; `FlowControl/Case.versetest` 154, 272, 280; `Enum.versetest:356`; `Bugs/SOL-4194-…versetest:20`; `FlowControl/Return.versetest:179` |
| a `return` or `break` may not leave a failure context, and a `<decides>` function's `return` is in tail position | 17: `Bugs/SOL-4199-BreakFromIf.versetest` 4, 15, 51, 60, 87; `Reachability.versetest` 12-15; `Return.versetest` 115, 118, 148, 158, 159, 161, 162, 163 |
| commas in a block make a tuple | 28: `SemicolonsVsCommas.versetest` 70, 91, 95, 100, 103, 106; `Option.versetest:44`; `FlowControl/for.versetest:293`; `Bugs/2021-09-03-OptionalTupleAssertionFailure.versetest:3`; `v1-Mix-comma-and-semicolon-in-archetype-instantiation.versetest` 232 and `:decls`; 17 parser cases (`TimSyntax.versetest` 72, 75, 220, 224, 226, 229, 231, 242, 257, 264, 265, 268, 272, 275, 276; `Tuple.versetest` 67, 70) |

No case expecting a valid program gets a warning but those whose test
expects it. **The programs whose bytes or output changed**, each checked as
the reading's (the byte-identity oracle over the suites and a corpus of
2,734 programs regenerated from the generators at the readings' base,
`corpus2`): with the warnings, 38 programs print warnings and nothing else
changes (18 tests, which say so in `NAME.warnings`, 2 upper-bound
fixtures, 18 generated `break-first` programs); with the jump rule, 404
generated programs are refused (each by it: the old generators' breaks and
returns among clauses, and `<decides>` early returns), 66 tests and 14
error tests whose subject was such a jump are deleted and 20 rewritten
with their output unchanged, and no other program's bytes change; with
commas, 53 programs of the old `generic_mv.py`, whose `option{}` clauses
were separated by commas, hold a tuple and are refused, and nothing else
changes. Against main `77bc509`, the merge changes exactly these programs
(482 of 5,710) and no other.

## After attributes, types as values and the syntax forms

Three groups of refusals were then taken, one cause per commit:
attributes, with the rules of [attributes.md](attributes.md); types as
values, the part the front end can build, with the map and the design of
[types-as-values.md](types-as-values.md); and the syntax the parser still
refused ([LANGUAGE.md](../LANGUAGE.md#attributes) describes each). Against
the baseline of the load-bearing readings (main `34e76e1`: 7,732 agree,
1,869 refuse, 136 accept, 46 differ), 273 cases more agree and one fewer:
**8,004 agree, 1,598 refuse, 135 accept, 46 differ** (re-recorded from a
fresh run).

| Cause (cases at the base) | Agree now | Left, and why |
|---|---:|---|
| attributes (137) | 94: `Attributes/Attributes.versetest` 16-31 (9); `CustomAttributes.versetest` 23-73 (10); `available.versetest` 6-62, 290, `:decls` (11); `deprecated.versetest` (36); `2021-10-05-AttributeNames` 3-5; `SOL-1729…:decls`; `Enum.versetest` 75, 525-592 (6); `Reachability.versetest:94`; `Return.versetest` 85-88, 139, 140, `:decls`; `Roundtrip/Comments` 126-144 (4); `KnownBugs:62`; `SemicolonsVsCommas:97`; `TimSyntax` 172-175 | 35: fields with accessors `<getter(…)><setter(…)>` (32, parsed and refused), `WebDataSyncService` (2: a module's `var` of a `weak_map`), `TimSyntax:138` (`x:=3` untyped at the top level) |
| types as values (238, with the structural types `comparable` left) | 87: `Cast.versetest` 57-71, 98-149; `Subtype.versetest` 66-103, 148-185; `Castable.versetest` 91-374 (20); `MetatypeConcreteSubtype` 4, 8, 99, 314, 320, 326; `Any.versetest` 25, 30; `SOL-7475` 4, 41, 45, `:decls`; `TypeParam:10`; `TypeValue:58`; `ParametricTypes:239`; two `:decls`; and the 3 type conversions (`Cast.versetest` 59, 61, 62) | 135: a metatype as a type parameter's bound (`where t:castable_subtype(c)`, `ParametricFunctions` 39, `Castable` 9, #502); `classifiable_subset` (20); metatypes of other types than classes (`subtype(int)`, `castable_subtype(any)`: `Subtype` 113-142, `Castable` 609-654); `castable_concrete_subtype` (6); `type` values of other types and a type given as an argument (`TypeParam`, `ParametricTypes` 605-1329); `concrete_subtype(comparable)` |
| other syntax (126) and block forms (16) | 61: `F of X`, `F at X` (`Operators/Of`, `At`, 26; `SemicolonsVsCommas` 39, 40); `profile` (`profile_simple`, 10); pointers `e^`, `^t` (`Roundtrip/Comments` 77-82, `Roundtrip/Operators` 10-13, `Pointers:5`); module items at their own columns (`AccessLevelInheritance` 605, 619, 849, `Module:167`); declarations with no body (`Roundtrip/Newlines` 4, 18); `FunctionTypes` 15, 29; `TimSyntax` 133, 283, 297, 298, 324 | 80: Tim Sweeney's parser tests (35: specifiers on names, `a<b>->c`, which comparisons make ambiguous; `&x`, `do:=3`, `capture{…}`), a module's `var` (`weak_map`, 6), types in type parameters' places (`TypeParam`, 5), function types written as signatures (`FunctionTypes`, 5), a constructor's delegation outside a constructor (`Classes/Constructor`, 5), roundtrip tests (6), live variables (`when`, 2), and 16 more of one or two each |
| lambdas, nested functions and their parameters (55) | 24: lambdas parse (`Literals/Function.versetest`, `FunctionTypes` 8-31, `TimSyntax:367`), refused as nested functions in programs | 33: nested functions (#492) |
| control forms (7 accepted) | 2: `Return.versetest` 114, 117 (a `return` inside a returned `for`) | |

- **Rules the new forms reached**, which openverse now checks, so that the
  cases that agreed through a parse error still agree: a `return` is no part
  of the value a function returns (`Return.versetest` 120-133, 3534); no
  `return` or `break` leaves a `spawn` (`SpawnAndTask.versetest` 878, 887,
  3551); no `profile` in an initializer (`profile_simple.versetest:144`,
  3675); a join of type values is at their metatype before the expected
  type, castable only when its bound is (`Castable.versetest` 145, 168,
  3509); an attribute class is named in attributes only (`SOL-1729…` 16-52,
  3670); and the attributes' own rules (where, what, fields). The uses of
  deprecated definitions are warnings (2009), through the compiler's
  warnings: 23 cases.
- **Moved the wrong way** (1): `deprecated.versetest:435`,
  `using{/Verse.org/VerseTests/TestModule}` of a deprecated module, which
  expects the warning 2009 and agreed through the parse error of
  `@deprecated`: openverse ignores a `using` of a package's path, here the
  test runner's (the harness's: such paths are left, [After qualified
  names](#after-qualified-names)), so it gives no warning.
- **Programs.** Against main `34e76e1`, over every suite and the corpus of
  2,734 generated programs (`corpus2`), no program's bytes, output or
  messages changed but: the new tests; two error tests of an arrow
  expression, which now expect the lambda's refusal
  (`unsupported_arrow_expression`, `unsupported_arrow_zero`); and two tests
  of values that never come, `never_spreads_maps` and
  `tuple_never_conversions`, whose `return F((return 9, 3))` the rule above
  refuses, rewritten `R := F((return 9, 3)); return R`, with their output
  unchanged and their warnings at their new lines. `of` and `at` became
  reserved words; no program of openverse's named anything so.

## After the Book's primitives

Three items that needed Verse Core or the runtime, by the Book
([`ToString` of a float](readings-audit.md#tostring-of-a-float), [the
bitwise functions](book-library-functions.md#bitwise-functions), [the
scheduler rules](scheduler-conformance.md#the-books-scheduler-rules)), built
on main `34e76e1` and merged with attributes, types as values and the
syntax forms. Against the baseline of the latter (`4efd536b`: 8,004 agree,
1,598 refuse, 135 accept, 46 differ), 110 cases more agree and 56 refused
cases now differ: **8,114 agree, 1,439 refuse, 135 accept, 95 differ**
(re-recorded from a fresh run; against the baseline of main `34e76e1`, the
same 110 and 56 were measured before the merge: 7,842, 1,710, 136, 95).

| Item | Cases before | Agree now | Left |
|---|---|---|---|
| `ToString` of a float: six digits after the point, the exact value rounded half to even, every integer digit, the sign kept, as the API and `FloatToString.versetest` (Verse Core's `VFloat.fixed6`, the C runtime's `%.6f`) | 7 different | 7: `Intrinsics/FloatToString.versetest` 15, 18, 19, 21, 22, 23, 24 | 0 (25 and 26 use the test runner's `FloatConstants`) |
| the bitwise functions, written with Verse Core's operations on 64-bit ints (no Core, format or runtime change) | 159 refused | 103: `Math/Bitwise.versetest`'s 84 untagged cases within int64, its 13 `bp_vm_only` cases (the overflow error), and 6 `verse_vm_only` ones whose result is the same (a negative count's failure, a runtime error) | 56 `verse_vm_only` cases now differ (cause int-precision, 26 → 82): they assume unbounded ints, and their own operands overflow here (`9223372036854775807 + 1`, `Pow2_64`), the Blueprint VM's documented behaviour, as the 26 before them |
| `Sleep(S)` rounds up; `Sleep(0.0)` completes at once | none translatable (the Book tests no `Sleep`; ch. 14's examples are not run by the harness) | | |

`scripts/book-conformance.sh compare` reports the 56 as worse (a refusal
became a different result); each is a `verse_vm_only` case of unbounded
ints, and no other case is worse than on either branch's baseline but
`Attributes/deprecated.versetest:435`, which the attributes' baseline
already had as accepted. **The programs whose bytes or output changed**,
each checked as the item's (the byte-identity oracle, extended to run each
program in C, over the suites and the corpus `corpus2`): with `ToString`,
572 programs print floats differently (60 `floats-*` and 482 `mv-*`
generated programs, 28 tests and 2 upper-bound fixtures; with the
attributes merged, `of_at_calls` too), and each new output is Python's
`'%.6f'` of the old shortest round-trip value; no bytes change. With the
bitwise functions, none. With `Sleep` rounding up, every program with a
`Sleep` changes its bytes by one primitive (`fround` to `fceil` in the
prelude's `sleepResume`), and three tests' output, each a sleep whose
product `30·S` rounded down before (1.2, 1.4999999999999998, and 4.5, a tie
to even). With `Sleep(0.0)`, every program with a `Sleep` changes its bytes
by one primitive (`fge` to `fgt`), the tests that used a zero sleep as a
one-tick wait now write `Sleep(0.01)` and print what they printed,
`scheduler_audit_sleep` shows the new rule, and 7 generated `conc-*`
programs (zero durations) change their output, each reproduced exactly when
their zero sleeps are made one tick.

## After source upper bounds

Source upper bounds admitted (#502; [the rules and what stays
refused](upper-bound-evidence.md#rules-of-the-book-and-what-openverse-follows)):
the guard that refused every bound but `subtype(comparable)` lifted, three
rules a bound had hidden behind it added, and `castable_subtype(c)` taken
as a bound. Against the baseline of main `84ee83c` (8,114 agree, 1,439
refuse, 135 accept, 95 differ), 17 cases more agree and none fewer: **8,131
agree, 1,422 refuse, 135 accept, 95 differ** (re-recorded from a fresh run).

| Cause (cases at the base) | Agree now | Left |
|---|---:|---|
| metatypes (137 refused) | 17: `ParametricFunctions.versetest` 46, 51, 57, 237, 248, 589; `ParametricTypes.versetest` 1338, 1354; `Castable.versetest` 519, 527, 536, 553, 558, 634, 677, 710 and its decls | 118; 2 of the 137 (`Castable.versetest` 563, 601) get past the bound to a generic function joined as a value with no expected type (#214), now under types-other (137 → 139) |

- **Agreeing for the right reason now.** Lifting the guard alone made four
  cases that agreed through its message accepted, each a rule openverse
  lacked, and each now refused by it: a bounded type parameter no
  parameter determines (`ParametricFunctions.versetest` 586, 3503), a type
  alias whose type applies a bound it breaks (`ParametricTypes.versetest`
  639, 3509), and a public parametric type with a less visible bound
  (`ParametricTypes.versetest` 1284, 1294, 3593). Of the 33 cases the guard
  decided on main, the 16 that agreed through its refusal agree now with
  messages of their own, 7 that it refused agree now, and 10 are refused
  for another feature (`ParametricFunctions.versetest`'s declarations, which
  give a type as an argument, `F(t:type, X:t)`).
- **Left of the cause.** `subtype(t)` of a type parameter and a type given
  as an argument (`ParametricTypes.versetest` 1305-1329, `TypeParam.versetest`,
  `FORT-1059276.versetest`, `SOL-8302…`; with `ParametricFunctions.versetest`'s
  declarations, about 45 cases), `concrete_subtype(c)` as a bound
  (`MetatypeConcreteSubtype.versetest` 49, refused by rule), and the
  metatypes of other types than classes.
- **Programs.** Against main, over every suite and the corpus of 2,734
  generated programs (`corpus2`), no program that compiled on main changed
  its bytes, output or messages. Two messages of refused programs changed:
  `tests/errors/generic_constraint` (an unknown bound, `subtype(printable)`,
  is the unknown type's error now) and the overloading matrix's
  `class_bound`, which now runs and prints 2; and the 155 upper-bound
  fixtures the guard refused now run or give their own refusals.

## After what a `for` undoes

The last of the load-bearing readings ([the readings
audit](readings-audit.md#what-a-for-undoes)): a `for`'s clauses are one
search, which commits at the body and undoes, at its end, what it did
since its last success. Built on main `34e76e1` for the `for`s whose
generators are over ranges, arrays, maps and strings and choices of values
(every `for` of the Book's tests), then merged with main `84ee83c` and with
[source upper bounds](#after-source-upper-bounds). Against the baseline of
main `84ee83c` (8,114 agree, 1,439 refuse, 135 accept, 95 differ), 7 cases
more agree and none fewer: 8,121 agree, 1,439 refuse, 135 accept, 88
differ; with source upper bounds, **8,138 agree, 1,422 refuse, 135 accept,
88 differ** (re-recorded from a fresh run; against each branch's baseline
nothing is worse, and the other branch's cases are the better ones: 17
against this one's, 7 against source upper bounds'; against the baseline
of main `34e76e1` the same 7 were measured before either merge: 7,739,
1,869, 136, 39).

| Reading | Agree now |
|---|---|
| a `for`'s clauses are one search: what a source, a range's bounds or the clauses before a later generator did is undone when nothing after them reaches the body | 7: `FlowControl/for.versetest` 344, 362, 371, 392; `Range.versetest` 140, 159; `SoftwareTransactionalMemory.versetest:88` |

**The programs whose bytes or output changed**, each checked as the
reading's (the byte-identity oracle, extended to run each program in C,
over the suites and the corpus `corpus2`, 5,713 programs, against main
`34e76e1`): 566 differ, 507 in their bytes alone (a `for` whose clauses can
do something before its last generator's elements, by the conservative
test the lowering uses: a call, a `Print`, a write; each prints what it
printed), and 59 in their output: 40 `choice-*` and 14 `mv-*` generated
programs, each of which its generator's model, with the rule, predicts
exactly; `choice_more` and `choice_construct_default_order`, whose `for`s
expected the old rule; and the three new tests (`for_search`,
`for_search_waits`, `for_search_old_paths`). No compiler message or exit
code changed. Over all the programs the bytecode is 1.8% larger.
With source upper bounds merged, the same oracle against a compiler built
at its head (`3cfbf1c8`, 5,787 programs) finds 568 that differ: the same
566, and the upper-bound fixtures `container-view-iteration` and
`container-view-iteration-state`, which compile only since source upper
bounds, whose `for`s take their sources through a bound's view, a call the
lowering's test counts as a possible effect: their bytes change, not their
output.

## After fields with accessors, type arguments and metatypes

Three Book features that were left with designs, built on main `532f79d`
(the Book's primitives, with the application refactor #609), one commit
each, with two fixes of built-ins before them. Against that baseline
(8,114 agree, 1,439 refuse, 135 accept, 95 differ), 65 cases more agree
and none is worse: **8,179 agree, 1,374 refuse, 135 accept, 95 differ**
(re-recorded from a fresh run; `compare` after each commit: 0 worse, and 27,
then 50, then 65 better).

| Item | Cases before (cause) | Agree now | Left |
|---|---|---|---|
| fields with accessors, `var X<getter(G)><setter(S)>:t = external{}` ([accessors.md](accessors.md)) | 32 refused, parsed and refused (attributes, 31; unnamed parameters, 1) | 27: `Attributes/CustomClassVarAccessors.versetest` 260, 282, 456, 488, 531, 534, 550, 586, 609, 614, 675, 693, 726, 730; `DeepMutabilityForCustomClassVarAccessors.versetest:373` (a path's setter); `InterfaceWithAccessors.versetest` 16, 36, `:decls`; `InterfaceWithFields.versetest` 439, 494; `LengthOptimizationSafety.versetest` 48, 66, 70, `:decls` (a field with storage given accessors below, read through the interface); `FORT-889314` 44, `:decls`; `CustomAttributes.versetest:76`. Their 14 refusals still agree, each by its rule (3523, 3553, 3600, 3671, 3502, 3688) | 5, other causes now: `CustomClassVarAccessors.versetest:558` (a construction in a field's default calls the setter, which has no convergence contract); `FORT-976754` 58, `:decls` (overloads of one name with different access, which openverse refuses); `InterfaceWithFields.versetest` 463 and `:decls` (two interfaces' accessors of one name in one class, #70; a field override with no default) |
| a type given as an argument and used as a type, `FalseOption(t:type):?t` | about 6 (metatypes, syntax-other) | 23: `ParametricTypes.versetest` 605, 618, 624, 706; `TypeParam.versetest` 59, `:decls`; 16 cases of `ParametricFunctions.versetest` (158 to 696) whose module `Var` declares `F<public>(t:type, X:t)`; and `2021-04-26-DisjointTypesAllowedInComparisonAndPointerDeref:4`, a comparison of values of different types (a comparison's operand takes the other's type only as a hint, which `False(int) = False(logic)` needs) | `Bar(t)` with `t` a type parameter (`TypeParam.versetest:49`, VerseVM; its BPVM twin, :43, expects the link error openverse gives); a refinement type written as an argument (`ParametricFunctions.versetest:464`) |
| metatypes of other types, `subtype(int)`, `subtype([]c)`, a type's name as a value; `concrete_subtype(any)`, `concrete_subtype(comparable)` | about 30 (metatypes, types-other) | 15: `Subtype.versetest` 113-119, 140-142; `TypeParam.versetest` 3, 15; `MetatypeConcreteSubtype.versetest` 12, 16, 26 | `Subtype.versetest:120` (`subtype(type{f():void})`, which the parser does not read); `TypeParam.versetest` 18-38, 54 (types written as expressions other than names: `Identity([]int)`, `Identity(class2(int))`); `castable_subtype(any)` (`Castable.versetest` 609-618) |

- **Rules the new forms reached:** a type argument after a parameter whose
  type uses it is refused (`SOL-4357-TypeType.versetest:28`, 3502), which
  the first measure of the type arguments accepted; the tests' refusals of
  `castable_subtype(int)` and `concrete_subtype(int)` (3509) and of a
  construction through `concrete_subtype(comparable)` (3545) still agree.
- **Moved the wrong way:** none. Nine refused cases changed cause, still
  refused (`CustomClassVarAccessors.versetest:558`, `FORT-976754`,
  `InterfaceWithFields.versetest:463`, `:decls`: from the accessors' parse
  refusal to the rules above; `ParametricFunctions.versetest` 192, 327, 464,
  546, 653 and `TypeParam.versetest:32`, `GenerateFunctionForParametricInterface:10`,
  `FORT-741838:83`: past the type arguments to what is left).
- **With source upper bounds.** Merged with [After source upper
  bounds](#after-source-upper-bounds) (#610), a parameter `t:subtype(c)` or
  `t:castable_subtype(c)` a function uses as a type is a bounded type
  argument (`where t:subtype(c)`), so 11 cases more agree that need both:
  `ParametricFunctions.versetest` 84, 89, 94, 103, 109, 147, 152, 155, 164
  (its declarations give types as arguments and bound type parameters) and
  `ParametricTypes.versetest` 1305, 1313 (`u:subtype(t)` of an earlier type
  argument; 1321 and 1329, of function types, are left): 8,207 agree, 1,346
  refuse, 135 accept, 95 differ; `compare` against each branch's baseline:
  0 worse, 76 better than #610's, 28 better than this one's.
- **With what a `for` undoes.** Merged then with main `669ba92` ([After what
  a `for` undoes](#after-what-a-for-undoes), #611), re-recorded from a fresh
  run on the merged compiler: **8,214 agree, 1,346 refuse, 135 accept, 88
  differ**; `compare` against main's baseline (8,138, 1,422, 135, 88): 0
  worse, 76 better (this branch's); against this branch's: 0 worse, 7
  better (#611's).
- **Programs.** Against main `532f79d`, over every suite and the corpus
  `corpus2`, no program's bytes, output or messages changed but the new
  tests, `field_accessors` (the refusal of the form, removed),
  `type_value_of_int` (`subtype(int)` works: it now tests
  `castable_subtype(int)`), and the two fixes' (`Quotient[7, 2, 1]` was an
  internal error and is refused; `Err(Foo, 5)` was accepted unelaborated
  and is refused).

## The remaining causes: a map

A map of every cause left at main `669ba92` (8,138 agree, 1,422 refuse,
135 accept, 88 differ), made before the work of [After the remaining
causes](#after-the-remaining-causes): for each cause the forms inside it,
what the Book says, how the tests mark it, what openverse does, the size of
the change and the mechanism it extends, and a verdict. Causes owned by
other work are named and left: `metatypes` (118), accessors (`attributes`,
35), `concrete-classes` (7, a question for the owner: [Concrete classes and
their subclasses](https://github.com/rudi-cilibrasi/openverse/wiki/Concrete-classes-and-their-subclasses)),
`for-rollback` (done since: [After what a `for` undoes](#after-what-a-for-undoes)).
Each form was read case by case with `scripts/book-conformance.sh show`;
"prose" is the Book's chapters at the pinned revision, file and line.

### Accepted where the tests refuse (135)

Each of these is a rule openverse lacks; they come first.

| Cause | Form | Cases | The Book | openverse | Size; mechanism | Verdict |
|---|---|---:|---|---|---|---|
| effect-checks (29) | E1. a named parameter's default has only the heap effects of its function, and neither fails nor suspends, also in a `<decides>` or `<suspends>` function (3512) | 16: `DefaultNamed.versetest` 820, 824, 844, 852-878 | prose silent on a default's effects (ch. 6 line 105: "Verse evaluates default values in the function's defining scope"); the tests' sections `decides`, `suspends`, `reads` … `transacts` (`DefaultNamed.versetest` 805-878) | a default is elaborated at each call, its effects the caller's; a failing one refused only at a call of a function that is not `<decides>` | one check: each default elaborated once at its definition, in its function's scope (`elabFn`), its effects checked as the body's (`fxCheck`); `--extended-defaults` keeps openverse's call-site defaults, as it keeps computed field defaults (#511) | do |
| | E2. a `loop`'s body is no failure context, also in a `<decides>` function (3512) | 3: `SOL-1987…:22`, `SOL-4199-BreakFromIf.versetest:80`, `FlowControl/Case.versetest:291` | the tests: "`decides` is not allowed in `loop`" (`SOL-4199…:79`), "Failable inside loop is disallowed" (`SOL-1987…:22`); ch. 8 line 122: "Functions marked with `<decides>` create a failure context for their entire body" | the body inherits the failure context | one check in `.loop` (`ExpressionControl`) | do |
| | E3. a field's default cannot fail (3512) | 1: `Effects.versetest:537` | ch. 13 line 830: "Class member initializers and block clauses are implicitly restricted to have no more effects than what the class declares" (a class declares no `<decides>`) | accepted | one check in `elabFieldDefaults` | do |
| | E4. `spawn` has `<transacts>`'s heap effects (3512) | 2: `Effects.versetest:558` (bp), `:573` (verse), both in a `<computes>` function; 2 more `bp_vm_only` ones (`:557`, `:565`, in a `<transacts>` function), whose VerseVM twins are valid | the tests: "spawn requires the transacts effect in addition to the effects of the spawned async function" (`Effects.versetest:554`); ch. 14 line 737: "spawn works in immediate functions, class constructors, module initialization—anywhere you can write code" | accepted | one check: `noteFx` in `elabSpawn` | do the 2; leave the BPVM pair (its `no_rollback`) |
| | E5. a function with no heap specifier is `no_rollback`: a `<transacts>` function or a class's `block` cannot call it (3512) | 3: `Effects.versetest` 490, 551, 552 (and T16) | ch. 13 line 302: "The `<transacts>` is the default for functions"; line 122: `no_rollback`, "To be deprecated; Transactions disallowed"; the tests `Effects.versetest:489-495` | unannotated means `<transacts>` | a rule over every call, and a harness question: the runner's `assert{F0(…)}` (`Any.versetest:9`) calls unannotated functions in what must be a failure context, where `no_rollback` is refused | left: the Book disagrees with itself, an owner decision |
| | E6. a `for`'s filter must be able to fail (3513) | 1: `FlowControl/for.versetest:223` | ch. 7 line 657: "Each filter must be failable"; line 836: "Filters must be failable" | accepted | one check in `elabFor` | do |
| | E7. a module constant constructing a `<transacts>` class (3512) | 1: `ParametricTypes.versetest:465` | as I1 | accepted | as I1 | do with I1 |
| initializer-effects (8) | I1. a module constant's initializer has no side effect (3582): no `<writes>`, which a call of an unannotated function has | 4: `Features/DefaultValueAssignment.versetest` 200, 215, 225; `Modules/ModuleDefinitions.versetest:279` | the tests: "all non-local variables initializers (module, instance) can't have side effects" (`DefaultValueAssignment.versetest:199`), "calling methods (which may have side-effects) produces an error" (`ModuleDefinitions.versetest:278`); prose silent (ch. 16 line 617 lets a module make `<allocates>` objects "as long as their construction does not actually allocate mutable memory") | a constant's effects are inferred, any allowed | one check where they are inferred | do |
| | I2. a module constant whose construction allocates mutable memory (link error 9003) | 4, all `verse_vm_only`: `GlobalVariables.versetest` 86, 90, 97, 105 | ch. 16 line 617 | accepted (openverse refuses a constant that holds a mutable object, not one whose construction makes one it drops) | a link-time check of what construction runs | left (VerseVM's link time) |
| interface-rules (7) | R1. an interface named twice among one definition's parents (3592) | 4: `Interface.versetest` 33, 40, 92; `InterfaceDiamond.versetest:74` | the tests: "It's ok to inherit the same interface more than once, but not directly" (`Interface.versetest:31`); prose silent | accepted | one check in `classHierarchy` | do |
| | R2. `<override>` in an interface (3523) | 3: `Interface.versetest` 194, 199; `InterfaceDiamond.versetest:89` | the tests: "Interfaces can not override anything" (`Interface.versetest:193`, also `InterfaceWithFields.versetest:312`); prose silent | accepted | one row of `EffectPolicy.checkPlaces` | do |
| qualified-names (6) | Q1. `(super:)M` only in an override of `M` (3612) | 2: `Super.versetest:183` (another method), `:238` (a class's `block`) | the tests: "super on another method" (`Super.versetest:192`), "Calling `(super:)` from blocks is not allowed" (`:237`); ch. 10 line 1050: "`(super:)F(X)` within the qualified method calls the parent class's implementation of that same qualified method"; but line 379: "it invokes the superclass's implementation of a method on the object you are already in" | accepted ([qualified-names.md](qualified-names.md) pins the rule, not checked) | one check in `elabSuperCall` | do |
| | Q2. `(a:)F()` in an override where `(super:)` is meant: the warnings 2003 and 2004 | 4: `SOL-3564…` 7, 18, 32, 45 | the tests' comments ("2003 - should use super", "2004 - you can't reach a: as super:") | accepted, no warning | a warning (`warnAt`) | do if cheap |
| control-forms (5) | C1. a `loop` with no `break` of its own and no `return`, outside a `<suspends>` function (3579) | 2: `FlowControl/Break.versetest` 118, 161 | the tests: "Ensure loop is not empty", "Ensure loop has matching break" (`Break.versetest` 117, 160); ch. 7 line 463: a loop "continues until explicitly broken" | accepted (runs out of fuel) | one source rule (`Elab/Source.lean`) | do |
| | C2. every arm of `race` and `rush` can suspend (3538) | 1: `Coroutines/Concurrency.versetest:832` | the tests: "Ensure all top-level expressions in race/rush are async" (`:831`); prose silent (ch. 14 line 230 asks two async arms of `sync`) | accepted | one check beside `sync`'s (`Elab/Expr.lean`) | do |
| | C3. `using{/localhost…}` (3544, 3587) | 2: `Modules/Using2.versetest` 86, 90 | the tests ("Explicitly using a "/localhost" package is not allowed", `:85`); ch. 16 line 349: "all imports must be resolvable when your code is compiled" | a `using` of a path is ignored | a registry of the paths openverse has | left (with T13) |
| type-checks-other (25) | T1. a default on a positional parameter (3625) | 1: `2023-01-18-FunctionParameterWithoutDomain.versetest:12` | ch. 6 line 51: "Named parameters with default values are truly optional" | accepted, the default ignored | one check | do |
| | T2. a named argument before a positional one (3629) | 1: `DefaultNamed.versetest:122` | ch. 6 line 101: "Invalid: named arg before positional" | accepted | one check at calls | do |
| | T3. a `var` field in a struct (3607) | 1: `Classes/Struct.versetest:31` | the tests ("Structs cannot contain pointers") | accepted | one check | do |
| | T4. `set` of a field of a struct that is not `<computes>` (3509) | 1: `Mutability.versetest:426` | ch. 5 line 735: "Only structs marked `<computes>` (pure structs) allow field mutation through a variable" | accepted | one check in `elabSet` | do |
| | T5. `return` or `break` out of a construction's field value (3626) | 1: `Classes/Constructor.versetest:528` | prose silent | accepted | one check in `checkJumps` | do |
| | T6. `option{}` with nothing in it (3622) | 1: `Option.versetest:94` | the tests | accepted | one check | do |
| | T7. a type parameter no parameter determines (3503) | 4: `ParametricFunctions.versetest:374` (named nowhere), 348, 356, 361 (named only where it is contravariant) | the tests | refused for bounded ones only | `UpperBounds.checkDetermined`; the contravariant ones need variance | do 374; the others with variance |
| | T8. `void` as a type argument is no top type | 2: `Void.versetest` 246, 260 | the tests | accepted | the conversion to `void` at a type parameter | left (subtle, 2 cases) |
| | T9. a tuple parameter beside a named one does not take two arguments | 1: `FORT-744399…:62` | the tests ("Doesn't work in ShipVerse") | accepted | | left (a limit of Epic's compiler) |
| | T10. a join of two classes with two common supertypes | 2: `SOL-5838…` 13, 22 | the tests | joined at the class | | left (a rule of joins) |
| | T11. polymorphic and mutual recursion of parametric classes | 3: `ParametricTypes.versetest` 263, 265, 269 | the tests: "Polymorphic recursion is not yet supported", "Mutual recursion is not yet supported" (`:262`, `:268`) | supported | none | left (Epic's limit; openverse is more general); **done since**: ch. 10's prose disallows both too ("Disallowed: Polymorphic Recursion", "Disallowed: Mutual Recursion"), so they are refused, as the Book is followed ([After classes and subtyping](#after-classes-and-subtyping)) |
| | T12. a public parametric class with a `var` field of its parameter (3552) | 2: `ParametricFunctions.versetest` 431, 438 | the tests (3552, not implemented) | supported | none | left (Epic's limit) |
| | T13. a `using` of a path that names no module, or names a class (3587) | 2: `Modules/Using2.versetest:94`, `QualifiedIdentifier.versetest:152` | as C3 | ignored | as C3 | left |
| | T14. an enum of more than 256 values (3552) | 1: `Enum.versetest:171`, bp | the BPVM's | accepted | none | left |
| | T15. a deprecated module used through the runner's path (2009) | 1: `Attributes/deprecated.versetest:435` | | the runner's path is ignored | harness | left |
| | T16. an unannotated function as a `<transacts><decides>` function value | 1: `FunctionTypes.versetest:191` | as E5 | | as E5 | left with E5 |
| epic-limits (23) | L1. the BPVM's code generation (IR errors) | 10, all bp | the BPVM's; their VerseVM twins are valid | accepted | none | left |
| | L2. arrays and maps as map keys, also inside a key's option, tuple or struct (3502) | 8: `Map.versetest` 45, 46, 223, 224; `Operators/CompareMap.versetest` 58, 59, 71, 72 | ch. 3 line 760: "Arrays and maps are both comparable … yet neither may serve as a map key … The one exception is `string`"; line 762; but line 1025: "Maps can be used as keys of other maps if all values and keys from it are comparable" | accepted | one check where key types are checked | do (the tests and line 760) |
| | L3. failure in a map literal's key (3502) | 1: `Map.versetest:249` | ch. 3 line 831: "failure in map literal keys is not implemented"; the tests (`:245`) | accepted | one check | do |
| | L4. a strict bound of a refinement past the `int` range (3502) | 2: `WhereConstrainedInts.versetest` 97, 100 | the tests | accepted | one check in `Refine` | do |
| | L5. `ParametricFunctions.versetest:366` | 1 | as T7 | | variance | with T7 |
| | L6. a parametric interface with a `var` field (3502) | 1: `ParametricFunctions.versetest:496` | the tests | accepted | none | left (Epic's limit) |
| name-limits (19) | names equal but for case, names too long for Unreal names (link errors) | 19, all bp: `FORT-793952…` (16), `FORT-555217…` 25, 31, 37 | the BPVM's; `FORT-793952…:376-385` (verse) are valid | accepted | none honest: a limit of the engine's names, no rule of the language | left |
| syntax-other (3) | S1. a field and a `block` with no separator in braces | 1: `Classes/ClassBlockClause.versetest:19` | the tests (3100) | accepted | parser | do |
| | S2. a `.` followed by a space, a line break or a comment | 2: `ReserveDotSpace.versetest` 5, 6 | the tests (3100) | accepted | lexer | do |
| concrete-classes (7) | a class below a `<concrete>` one | 7 | an owner's question | | | left (owner) |
| duplicate-definitions (1) | `enum{ public }` | 1: `QualifiedIdentifier.versetest:315` | the tests | accepted | | left |
| final-members (1) | a `<final>` method does not implement an interface's method of its name | 1: `Attributes/final.versetest:125` | the tests' comment (`:121`) | accepted | | left |
| persistable (1) | an enum that is not `<persistable>` in a `<persistable>` struct | 1: `persistable.versetest:59` | ch. 17 | every enum taken to persist | the parser keeps an enum's `<persistable>` | do if cheap |

### Refused where the tests accept (1,422)

| Cause | Forms (cases) | The Book; tags | openverse; where | Size | Verdict |
|---|---|---|---|---|---|
| library-chars (145) | free `ToChar(N)` (132) and `ToChar32(N)` (13), called with parentheses in `Literals/Char.versetest:77, 222` | declared nowhere: the API has only the `<decides>` methods `N.ToChar[]`, `N.ToChar32[]` (`docs/api`, `verse_api_overrides.md:590, 1434`); the test runner's | "unknown function 'ToChar'" | harness: free calls of these names not translatable, the methods' cases kept | do |
| types-other (139) | the test runner's names (26: `native_property_rollback_test` 13, `NestedTupleParameters`'s natives 6, `SOL-8267` 3, `StmCallbackErrors`, `FunctionAsType:235`, `QualifiedIdentifier:decls`, `NativeTwoParams`); library APIs (12: `classifiable_subset_var` 7, `subscribable_event_intrnl` 3, `GetRandomInt` 2); types as values (10); function values joined or converted (14, 11 verse); overload and name rules (19: refinement overloads 4, `i()` beside `i(t)` 6, a local `Args` 2, a user `ToString` 3, …); `<computes><allocates>` (4); `spawn` (7, 6 verse); archetype `let:`/`block` (4); definitions as expressions (2); unit and bottom typing (10: a loop with no break as `int`, `return` as an operand, `?` on `not`, …); containers (9); inference (4); map keys of related classes (4); literal-typed locals (2); F-bounded classes (6); cyclic field defaults (3, verse); others (3) | per form; 20 verse, 1 verse_vm_todo | per form | harness for the 26; one check each for about 25; the rest front-end features, and Core for F-bounded classes (#63) and `GetRandomInt` | harness names: do; the rest left, listed |
| union-types (136) | `union{…}` | all `verse_vm_only` (`Union.versetest:15`; "Macro 'union' does not exist in BPVM", `:8`); in no chapter | parse errors | front-end and Core | left (VerseVM-only, not in the Book's chapters) |
| metatypes (118) | | | | | left (other work) |
| library-diagnostic (93) | `ToDiagnostic(V).String` of every kind of value, through `any` (`Intrinsics/ToDiagnostic.versetest`) | ch. 2 lines 867-884: "the exact format… may vary between VM implementations"; API `ToDiagnostic(Value:any)<predicts><reads>:diagnostic`; 7 verse, 1 bp | "unknown function 'ToDiagnostic'" | Core: `any` keeps no value in openverse ([any](../LANGUAGE.md#any)); a box with a type code, a printer and a shortest round-trip float formatter (runtime); 12 cases expect the runner's package path | left (Core and runtime) |
| class-specifiers (84) | `<final_super>` (81: 71 `GetCastableFinalSuperClass`, verse_vm_todo, which also need that function and `castable_subtype` values; 9 more); `<converges>` on an abstract method (1); `<native_callable>` (1); a `<persistable>` class (1) | ch. 11 lines 1673-1726; ch. 13 lines 127, 439-445 | "not supported yet (#11)", #494 | one check each, with their rules (`<final_super>` needs a parent, 3679; a `<persistable>` class's fields) | left (#11 and its library function; owner decisions on #494) |
| syntax-other (78) | specifiers after an expression `a<b>` (10); `->` as an expression (7); `e:t` and `where` on any expression (5); reserved words as names (6); `try`/`catch`, `&x`, units `123{m/s}`, trailing blocks, `is total`, `for(…)<par>`, `f?(…)` (9); pointers (2); `var x:int` with no value (1); mixed `,`/`;` (2, a semantic error in ch. 1); constructor delegation in an archetype (4, ch. 10 lines 272-275); a block comment as an interpolant (1, ch. 2 lines 804-821); others (14); 17 others' (metatypes 9, nested functions 5, …) | `TimSyntax.versetest` is "converted from Tim's parser test suite" (35 cases), no prose; 4 verse | parse errors | parser forms; most parse-only (`refusedForm`) | left but the prose-backed ones, listed |
| live-variables (50) | `live`, `when`, `upon`, `await`, `batch`, `set live` | all `verse_vm_only`; ch. 15 is "Unreleased Feature" (line 3) | | front-end, Core and runtime | left (unreleased) |
| override-defaults (46) | `X<override>:t` with no default (5); with no default and a narrowed type (8); a narrowed type with a default (23); coerced method overrides (10) | ch. 10 lines 2114-2141 and 3172-3175 agree with the tests on fields; lines 371-374 ("method signatures must match exactly") contradict them on methods | "must give a new default", "must have the type it inherits" (`classFields`, `checkSignatures`) | one check for the 5; narrowing a front-end feature (the field's type at the subclass); bridges for methods | the 5: do if cheap; the rest left |
| variance (38) | a parametric class's instances by variance (bivariant 18, covariant 10, contravariant 10), all `ParametricTypes.versetest` 59-177, 506, 537; with `SOL-6739…` (15 under joins and subtyping-to-any), 53 | ch. 10 lines 1306-1490 | type arguments compared exactly (`refUp`, `nominalSubtype`); Core's `sub` too (`Core/HeapExamples.lean:499`: "type arguments are not covariant") | bivariant: front-end (an unused parameter left out of Core types); co- and contravariant: Core and proofs | left (Core) |
| archetype-blocks (36) | the runner's types (5); a module of `ParametricTypes.versetest` that 31 cases include though the file has no `using` of it (harness over-inclusion; with each case's own module 17 agree, 2 need an empty `C(args):` archetype, the rest reach variance and metatypes) | 2 verse | | harness: a module's members visible only through a `using` | left (harness design; reaches variance) |
| set-forms (35) | `set live` (28, verse, live variables); `set` through a call's result or a construction (6); `set M[1,2]` (1) | ch. 5 line 148; ch. 1 lines 1010-1013 | `elabSetWith`: a path from a variable | small front-end: bind the root to a local | left, listed |
| attributes (35) | | | | | left (accessors: other work) |
| localization (34) | `<localizes>` message constants (6) and functions (24), `Join` (2), others (2) | ch. 12 lines 885-1100; API `Localize`, `Join`, `message` | "unknown or unsupported specifier <localizes>" | front-end feature: a message as its rendered string (no Core) | left (a feature of its own) |
| spawn-in-failure-context (29) | `spawn` written in an assert's body: 21 at its top level, 1 in a `loop`, 7 in a failing `if:` (verse, also `await`) | ch. 14 lines 735-738: "spawn works … anywhere you can write code"; no test refuses `spawn` for being in a `<decides>` body; `Main()<decides>` is a faithful translation | "spawn cannot be in a failure context" (#156, `elabSpawnIn`), stricter than either VM | one check, kept only in a `<suspends>` function's failure contexts (the lowering counts the spawn as a suspension there); 13 agree, 7 become different results (awaiters run inside `Signal`, a documented gap), 1 bp case accepted (`SoftwareTransactionalMemory.versetest:505`, the BPVM's) | do if its different results are acceptable; else left |
| nested-functions (29) | | ch. 6 line 1077: "Unreleased Feature" | | #492 | left (unreleased) |
| qualified-names (26) | two members of one name in a class (12); the runner's package path (7); `snippet{…}` (2, the runner's); others (5) | ch. 10 lines 978-1025 | | front-end feature (members keyed by qualifier); harness | left |
| weak-map (23) | | | | #491, Core | left |
| library-other (23) | `GetCastableFinalSuperClass` (15, verse_vm_todo); `FitsInPlayerMap` (3, persistence); `signalable(t)` (2); `GetSecondsSinceEpoch` (2, a clock); `awaitable` (1, the runner's) | | | #11; persistence; a clock primitive (runtime) | left |
| effects-of-classes (23) | `class<computes><allocates>` and the like | ch. 13 lines 99-106: one exclusive specifier combines with additive ones; ch. 3 lines 1184-1194 write `class<unique><allocates><computes>` | refused (`EffectPolicy.checkSpecs`, `checkExclusive`): openverse's own reading, the effect conformance note | one check, and `Choice.inlineFns`'s test of "effect-free"; 20 agree, 5 more elsewhere | do if cheap |
| module-objects (21) | `MakeNull` (17, the runner's, verse_vm_todo); module constants holding `<unique>` objects (4) | ch. 16 line 617 | "would hold an object with var fields or of a <unique> class" | harness for 17; Core module state for 4 | harness: do |
| empty-containers (20) | `array{}` and `map{}` with no type from context | ch. 1 line 1274 writes `Empty := array{}`; ch. 2 line 1276 | "the type of an empty array{} must be given" | front-end: `[]false` | left |
| singleton-types (19) | `true` (15) and `false` (4) as types | ch. 2 lines 1233-1300, ch. 11 line 1226 | "unknown type 'true'" | one check, and an owner decision (`true` as `void`) | left (owner) |
| joins (15) | SOL-6739 (7, variance); function values (4); a map literal's values (3); `0=(false? or 0)` (1) | | | one check for 4; variance | left |
| operator-definitions (14) | `operator'+'`, `prefix'-'` overloads (11); through interpolation (2); operator names as identifiers (1) | ch. 4 line 646 | parse error | parser form and overloads | left |
| path-literals (13) | `import(/…)` aliases of the runner's modules (12); `import(/Verse.org)` (1) | ch. 16 lines 452-470 | "unknown function 'import'" | harness for 12; a module alias | left |
| first-forms (11), ranges (11) | generators in `first` (18); a typed range in `for` (4) | ch. 7 lines 923-1010 | "a generator … in first is not supported yet" | front-end features | left |
| partial-modules (11) | one module in several parts | the tests ("there isn't any reason why…", `PartialModuleDefinitions.versetest:176`) | "module X is defined twice" | front-end, with two checks of the parts' agreement | left |
| subtyping-to-any (11) | SOL-6739 (8, variance); a function value at an `any` result (1); others (2) | | | one check for 1 | left |
| named-tuple-elements (11) | named parameters in a tuple parameter (8); named tuple values (3, verse_vm_todo) | ch. 6 lines 371-425 | [tuple-parameters.md](tuple-parameters.md) | owner decision | left |
| impossible-casts (8) | 4 a harness translation drops the class that makes the cast possible; 4 genuine | | "would always fail" | harness; a warning for the genuine ones | left |
| unnamed-parameters (8), empty-bodies (5), nested-tuple-parameters (4), archetype-separators (3), char-literals (2), block-forms (2), generators (1), type-aliases (1), closed-functions (7), comparable-classes (4) | parser forms (mostly `TimSyntax`); 5 empty `assert:` bodies (a harness translation error); `<closed>` (6 verse, functions as types); unique interfaces with no class below them (4) | | | parser forms; harness; one check each | the empty bodies: do (harness); the rest left |

### The order

Cases moved per unit of risk, the accepted refusals first, since each is a
rule openverse lacks: E1 (16); the harness's test runner names, free
`ToChar` and `MakeNull` (145 + 17, no risk); R1 and R2 (7); E2, E3, E6 (5);
E4 (2); I1 with E7 (5); Q1 (2); C1, C2 (3); T1-T6 (6); L2, L3, L4 (11); S1,
S2 (3); then the refusals: `spawn` in a failure context (13), `<computes>`
with heap effects (20), the empty `assert:` bodies (5).

## After the remaining causes

The [map](#the-remaining-causes-a-map) worked down from its order, one
cause or form per commit, each rule pinned in
[book-remaining-rules.md](book-remaining-rules.md) and described in
[LANGUAGE.md](../LANGUAGE.md); merged with main `669ba92` (#611) and
`7f12181` (#612). Against main `7f12181` (8,214 agree, 1,346 refuse, 135
accept, 88 differ, 3,721 not translatable), measured with each branch's
own harness from fresh runs: **8,267 agree, 1,148 refuse, 87 accept, 88
differ, 3,914 not translatable**; no case that agreed agrees no longer, and
none became an accepted refusal or a different result. Merged with
[weak maps and module-scoped vars](#after-weak-maps-and-module-scoped-vars)
(#614) and measured from a fresh run: **8,289 agree, 1,124 refuse, 87
accept, 88 differ, 3,916 not translatable**. Against this work's baseline
before the merge: 0 worse, 22 better (the weak maps'), 2 not translatable
(`weak_map.versetest` 183, 684); against #614's: 0 worse, 53 better (this
work's), 176 not translatable (the test runner's names this work found). A
weak map's key follows a map key's rule ([the
rules](book-remaining-rules.md#map-keys-and-a-refinements-range)), which no
case of the Book reaches.

| Cause (main → now) | Done | Left, and what it needs |
|---|---|---|
| effect-checks (29 → 7) | 22: a named parameter's default is its function's (`DefaultNamed.versetest` 820-878, 16); a loop's body is no failure context (`SOL-1987…:22`, `SOL-4199…:80`, `Case.versetest:291`); a field's default cannot fail (`Effects.versetest:537`); a literal `for` filter (`for.versetest:223`); a module constant constructing a `<transacts>` class (`ParametricTypes.versetest:465`) | `no_rollback` as the default of a function (3, an owner decision: the Book disagrees with itself); `spawn`'s `<transacts>` effects (2, and 2 of the BPVM's: 12 tests spawn from narrower functions); the whole filter rule (153 tests, 826 generated programs) |
| type-checks-other (25 → 20) | 5: a positional parameter's default, a named argument first, a struct's `var` field, a `return` out of a construction's field value, `option{}` | contravariant type parameters (3, variance: Core); `void` as a type argument (2); joins with two common supertypes (2); limits of Epic's compiler (6: polymorphic recursion, ShipVerse's tuple parameter, 3552); `using` paths (2) and the runner's path (1); an enum of 256 values (1, BPVM); `no_rollback` (1); a type parameter no parameter names (1) |
| epic-limits (23 → 12) | 11: arrays and maps as map keys (8), a failing map literal key, a refinement's strict bound past the range (2) | the BPVM's code generation (10); a parametric interface's `var` field (1); variance (1) |
| initializer-effects (8 → 4) | 4: a module constant has no side effect | link-time allocation at module scope (4, VerseVM's link check) |
| interface-rules (7 → 3) | 4: an interface named twice among the parents | `<override>` in an interface (3: openverse's interface defaults, #53, 32 tests and 45 generated programs; an owner decision) |
| control-forms (5 → 3) | 2: a loop that nothing leaves outside `<suspends>` | an immediate arm of `race` (1: 9 tests race one; an arm calling a suspending function value is not yet known to suspend); `using{/localhost…}` (2: openverse ignores the paths it has not) |
| qualified-names (6 → 6) | | `(super:)` of another method or in a block (2: 27 tests, 20 generated programs); the warnings 2003 and 2004 (4) |
| name-limits (19), concrete-classes (7), syntax-other (3), and one each of duplicate-definitions, final-members, persistable | | the BPVM's name limits; the owner's question; parser checks of `.`+space and a field's separator; `enum{public}`; a final method and an interface's; an enum's `<persistable>` |
| library-chars (145 → 0) | not translatable: the test runner's free `ToChar(N)`, `ToChar32(N)` | |
| module-objects (21 → 4), types-other (147 → 122), archetype-blocks (36 → 31), library-other and spawn (1 each) | not translatable: 48 cases of the runner's names (`MakeNull`, `native_property_rollback_test`, …) | module constants of `<unique>` objects (Core module state) |
| empty-bodies (5 → 0) | 5: an `assert:` of comments only is an empty body (the harness) | |

- **Programs.** Over every suite and the corpus `corpus2`, against main
  `7f12181`: no program changed its bytes, output or messages but the new
  tests and those the commits list. Refused by a rule now: 116 + 27 + 86
  generated programs of `corpus2` (`gadt_defaults` 9, `gadt_spawn_defaults`
  14, `gadt_waiting_contexts` 20, `generic-mv` 53 and 86 more,
  `gadt_contexts` 20, `equality` 27), and the error tests whose message the
  rules change (`default_fails`, `multi_named_default_fails`,
  `suspends_default`, `signal_no_rollback_constant`). Tests rewritten for
  a rule, output the same: 23 that built a module constant through an
  unannotated helper or class (`<computes>` added), 5 that wrote a named
  argument first, 2 that declared a struct's field `var`, 2 whose function
  failed out of a loop (`class_cast_refine_for_return_lazy`,
  `choice_suspends_return_lazy_returns`, the function dropped),
  `overflow` (a `break` never taken), `empty_values_nested` (a map keyed by
  an option), `initializer_convergence_hidden_first` (its `first{}` in
  `option{}`); and 11 whose failing default was not their subject: six
  `choice_dictionary_numeric_*` write their rational field's default `1`
  rather than `1/1`, which can fail, three `initializer_convergence_*`
  (`choice_function`, `choice_literal`, `failable`) catch the failure in
  the default's own `if`, and `multi_named_params` and
  `multi_recursive_named` lose their failing defaults to
  `multi_named_params_failing_default` and
  `multi_recursive_named_failing_default`. 44 tests of openverse's own
  default reading (waiting, dispatched and spawned defaults, a default's
  effects at its caller's, a failing default; #283, #459, #468) and those
  two new ones select `--extended-defaults`, their bytes the same.
- **The gate's generators** write what the rules accept: `mv.py` and
  `generic_mv.py` a named argument last (the place drawn for it is drawn
  still); `generic_mv.py`'s recursive named group ends its recursion in the
  callee's first clause, not in a failing default; `gen-equality.py` keys
  no map by a type with an array or map in it (`[string]logic` where it
  had `[[]int]logic`; a map case keyed so is drawn and not written);
  `gadt_contexts.py`, `gadt_waiting_contexts.py` and `test-choice-size.sh`
  construct their module constants' classes `<computes>`;
  `gadt_defaults.py`'s methods whose defaults write are `<transacts>`. The
  option is passed only where a model's subject is the extension:
  `gadt_spawn_defaults` (a `<computes>` method's writing defaults, #468),
  `gadt_waiting_contexts` and the size check's waiting-default cases
  (defaults that wait, #283), and the initializer model run under it
  before.
- **Where the Book disagrees with itself** (openverse follows the tests):
  a `<decides>` body's loop (ch. 8 line 122 against
  `SOL-4199-BreakFromIf.versetest:79`); maps as map keys (ch. 3 line 1025
  against line 760 and `Map.versetest` 223-224); `var` in a `for` clause
  (ch. 7 lines 842-843 against `for.versetest:235-236`); and, left, the
  default effects of a function (ch. 13 line 302 against
  `Effects.versetest:490`), `(super:)` (ch. 10 line 379 against
  `Super.versetest:192`), `spawn` "anywhere" (ch. 14 line 737 against
  `Effects.versetest:558`), and a loop of `break` alone (ch. 7 line 532
  against `Break.versetest:4`).

### What is left

Of the map, the causes whose subjects are other work (metatypes, about
76; the attributes' 4) or unreleased in the Book (union types 136, live
variables 50, nested functions 29, all VerseVM-only or marked "Unreleased
Feature"), and: the Core and runtime items (`ToDiagnostic`, 93: an `any`
that keeps its value, a printer and a shortest float formatter; variance,
38 and 15 more; weak maps, 23; module state, 4; F-bounded classes, 6;
`GetRandomInt` and a clock); the owner's decisions (`no_rollback`,
`<override>` in an interface, `(super:)`'s reach, `spawn`'s effects and
`spawn` in a failure context, 13 more agreeing at the cost of 7 different
results through awaiters run inside `Signal`; the first three, the
`race` arms' and the whole filter rule done since, and `spawn` in a failure
context looked at again and kept, [After the held rules](#after-the-held-rules); `true` and `false` as
types, 19; `<concrete>` subclasses); and front-end features, each of its
own: `<computes><allocates>` classes (20, with `Choice.inlineFns`'s test
of what is effect-free), localization (34), operator definitions (14),
generators in `first` (18), partial modules (11), two members of one name
(12), empty containers typed `[]false` (23), `set` through a call's
result (6), and the parser forms of `TimSyntax.versetest`.

## After weak maps and module-scoped vars

`weak_map(k, v)` and module-scoped `var`s ([weak-map.md](weak-map.md):
the Book's rules, whether weakness is observable, the design), built on
main `669ba92` in two commits (`compare` after each: 0 worse, 21 better),
merged with main `7f12181` (#612), and a declaration `var x:int` with no
value parsed. Against main's baseline (8,214 agree, 1,346 refuse, 135
accept, 88 differ, 3,721 not translatable), 22 cases more agree and none
is worse: **8,236 agree, 1,305 refuse, 135 accept, 88 differ, 3,740 not
translatable** (re-recorded from a fresh run on the merged compiler).

| Cause (cases on main) | Agree now | Not translatable now | Left |
|---|---|---|---|
| `weak_map` (23) | 18: `weak_map.versetest` 36, 73, 81, 89, 98, 113, 138, 145, 161, 194, 206, 213, 221; `Map.versetest` 381, 388, 464; `SOL-7231-NamedParameterMeet` 21, `:decls` | 1: `weak_map.versetest:183` (`TestWeakMap`, the test runner's digest round trip) | 4, other causes now: `weak_map.versetest` 41, 48 (an `assert_valid` that defines `Main` with parameters, which openverse's `Main` cannot have); `:32` (`t := weak_map(int, int)` in a body, a type as a value: metatypes); `Map.versetest:401` (VerseVM: a `set` through a key of a sibling class in a failure context, which fails at run time there and is refused here, as the map's twin `:363`) |
| module constants of mutable classes (21) | none | 17: `FORT-635190` (16), `FORT-721882` (1) call `MakeNull`, the test runner's null object | 4: `GlobalVariables.versetest` 72-74, `:decls`, module constants of a `<unique>` class, which need their initializers run once before `Main` (below) |
| a module-level `var` (27 cases stopped at the parser's `var`: 9 refused, under syntax-other and attributes, and 18 refusals that agreed so) | 1: `Pointers.versetest:4` (`var x:int`, valid syntax) | 1: `weak_map.versetest:684` (`Session`, `session_key`: the engine's session keys, and what the assertion at 675 wrote) | 7: `weak_map.versetest` 6, 624, 639, 668, 669 reach their key classes' `<allocates><computes>` now (effects-of-classes; with `<computes>` taken out of those classes, 6, 624, 668, 669 and 667, refused there before, are accepted, checked by hand, and 639 needs a `<persistable>` class, #11); `WebDataSyncService.versetest` 5, `:decls` reach the engine's attribute `@expose_to_web_data_sync_service_reads` |
| other type rules: a map read with a key of a class above or beside its keys (3) | 3: `Map.versetest` 354, 394; `Array.versetest:117` | | |

- **Agreeing for the right reason now.** The weak map's refusals were
  agreements through `unknown parametric type 'weak_map'` and are now each
  its rule's (`weak_map.versetest` 55, 62, 104, 117, 125, 130, 156;
  `Map.versetest:410`; `persistable.versetest:83`). Of the module-scoped
  `var`s' refusals that agreed through the parser's refusal of `var`,
  `weak_map.versetest:16` and `GlobalVariables.versetest` 5, 39 agree by
  the rule of their type now; `Function.versetest` 147, 157 and
  `Overloading.versetest` 152-158 by the refusal of a `var` function; and
  `weak_map.versetest` 20, 26, 168, 174, 631, 648, 657 reach their key
  classes' `<allocates><computes>` first, and with it taken out each is
  refused by its own rule (the value's persistence, the key's specifier,
  the whole map read or replaced, the limit of four; checked by hand).
- **Not translatable, and why.** The 51 cases of `weak_map.versetest` the
  survey already counted (`Persistence`, `persistent_key`) and the two
  above need the engine's persistence: keys made valid and invalid
  (`SetValid`, `Joined`, `Dropped`, the runtime error `WeakMapInvalidKey`),
  the update journal (`RecordUpdates`, `TakeRecordedUpdates`), sessions
  (`Session.Reset`), and module state that one assertion leaves for the
  next in the runner's one program. A stand-in class for `persistent_key`
  would make the cases translate but not agree: every one of them reads or
  writes under a key whose validity an earlier assertion set, or checks the
  journal. Only `FitsInPlayerMap` (605, 611, 615; the API reference's
  persistence limit check) is translatable and refused, under
  library-other.
- **Programs.** Against main, over every suite and the corpus `corpus2`
  (5,825 programs), no program's bytes, output or messages changed.

## Classes and subtyping: the map

The causes about classes and subtyping, the largest front-end group left,
measured on main `e451452` (8,236 agree, 1,305 refuse, 135 accept, 88
differ). For each: its forms (cases looked at with `show`), the Book's
rule, the VM tags, what openverse does, the mechanism a change extends,
the size, and then an order by cases per unit of risk. Chapter lines are
of the Book's `docs/`, test lines of its `Tests/`.

**class-specifiers (84) and library-other (15 of them).**
- *Forms.* `<final_super>` on a class (72 cases of
  `GetCastableFinalSuperClass.versetest`, 7 of
  `Attributes/FinalSuperAttribute.versetest`, `Castable.versetest:659`,
  `MetatypeConcreteSubtype.versetest:58`), refused as "not supported yet
  (#11)"; and the two functions of the API reference,
  `GetCastableFinalSuperClass[B, X]` and
  `GetCastableFinalSuperClassFromType[B, T]`, "unknown function" (15 cases
  of the same file, under library-other, whose slice has no `<final_super>`
  class). The other three are not classes: `<converges>`
  (`Effects.versetest:304`), `<native_callable>`
  (`ModuleDefinitions.versetest:164`), `<persistable>` (#11).
- *Rule.* Ch. 10, "Final" (`10_classes_interfaces.md:2904-2950`):
  `<final_super>` "guarantees that all subclasses of this class will always
  directly inherit from it"; `<final_super_base>` "marks the root of a
  restricted inheritance tree" and works with `GetCastableFinalSuperClass`,
  "which finds the `<final_super>` class in the hierarchy for a given
  instance". Ch. 11, "final_super and Type Queries"
  (`11_types.md:1673-1840`): both functions return "the least specific
  `<final_super>` class that: 1. Directly inherits from the specified base
  type 2. Is in the inheritance chain of the instance/type", and fail
  otherwise. The API reference: `GetCastableFinalSuperClass(base_type:type,
  Instance:base_type)<reads><decides>:castable_subtype(base_type)`,
  "Return an immediate subclass of base_type that is <castable> and
  <final_super> and is also shared with Instance. Otherwise failure", and
  `GetCastableFinalSuperClassFromType(base_type:type,
  sub_type:subtype(base_type))`, the same "shared with sub_type". The
  tests add: a `<final_super>` class needs a parent (3679,
  `FinalSuperAttribute.versetest:51`), a class right below a
  `<final_super_base>` class or interface is `<final_super>` (3680; built
  already), an interface below one need not be (:28); the instance must be
  of the base type (3509, `GetCastableFinalSuperClass.versetest` 102-125);
  the result is a `castable_subtype` of the first argument (127-145,
  182-202); the class found must be castable (332, 337); and a type that
  is not a class (`int`, `float`, `any`, 297-304) makes the call fail.
- *VM.* `verse_vm_todo` ("not defined in the new VM because of gaps in VNI
  support for types", `GetCastableFinalSuperClass.versetest:29`): the
  BPVM's expectations, with no VerseVM twin; the survey counts them.
- *openverse.* Refuses `<final_super>` (`classHierarchy`) and knows neither
  function. The specifier's places (`EffectPolicy.specifierPlaces`) and the
  3680 rule are built.
- *Mechanism.* `resolveSpecifiers`/`CDef` for the specifier;
  types as values (`TypeValues.desugar`, [types-as-values.md](types-as-values.md))
  for the result: `C` as a value is an object of `$type:C`, below
  `castable_subtype(B)` for each `B` above a castable `C`. A call becomes a
  call of a helper the front end writes, a chain of casts `C[X]` over the
  candidate classes, topmost first. No Verse Core.
- *Size.* Up to 96 cases (81 + 15), and the 7 refusals of the file keep
  agreeing, each by its rule.

**effects-of-classes (28).**
- *Forms.* `<computes>` with `<allocates>` (or `<reads>`, `<writes>`) on a
  class or an interface (`Attributes/allocates.versetest` 6, 13, 57;
  `Attributes/unique.versetest` 90-137; the key classes of `Map.versetest`,
  `Operators/CompareMap.versetest` and `weak_map.versetest` 6, 624, 639,
  667-669). The same form on a struct (`allocates.versetest:20`,
  syntax-other) and a function (`:27`, types-other) is refused for the
  same reason.
- *Rule.* Ch. 13 (`13_effects.md:99-105`): "Effect specifiers can be
  further divided into *exclusive* specifiers (`<converges>`, `<computes>`,
  `<transacts>`) and *additive* specifiers (`<suspends>`, `<decides>`,
  `<reads>`, `<writes>`, `<allocates>`). A function may have at most one
  exclusive specifier but can combine multiple additive ones"; the table
  (`:115-116`): `<computes>` implies `{}` of the heap. The tests:
  `allocates.versetest:4-5`, "Combines with <varies> and <computes>, but
  redundant with <transacts>", and `unique.versetest:87-89`, "<varies> and
  <computes> require an explicit <allocates>".
- *VM.* None.
- *openverse.* Refuses `<computes>` with any heap effect, for classes and
  functions (`EffectPolicy.checkSpecs`, `Signatures.checkExclusive`).
- *Mechanism.* The effect sets: `<computes>` with additive heap specifiers
  is the set of those specifiers (`constructionFx`, `allowedFx`).
- *Size.* 28, and the struct's and function's 2.

**override-defaults (47).** Three forms.
- *(a) A field `<override>` without a value* (`Attributes/override.versetest`
  3, 33, 133, `:decls`; `Attributes/concrete.versetest` 59, 110, 230;
  `SOL-3366:53`; `SOL-3731` 22, 23, `:decls`; `InterfaceWithFields` 377,
  `:decls`; `AccessLevelInheritance:863`), refused: "must give a new
  default". Ch. 10, "Overriding Members" (`10_classes_interfaces.md:3172-3175`):
  "Field overrides can provide different default values or specialize to
  subtypes"; the tests construct the class with the field given
  (`override.versetest:33`), and `concrete.versetest:110-114` re-declare a
  defaulted field with no value ("is this actually valid?").
- *(b) A field overridden at a subtype* (`MetatypeConcreteSubtype` 13:
  `comparable` to `int`, `float`, `logic`; `Any.versetest` 163, 164: `any`
  to `int`; `Bugs/BPVMOnly/RefinedMapKeyInterfaceOverride` 7: `int` to a
  refinement, a class to a `<unique>` one, tuples and options of them;
  `InterfaceWithFields:358`: a class to its subclass; and with (a):
  `override.versetest` 3, 133, `SOL-3731`, `AccessLevelInheritance:863`,
  `InterfaceWithFields:377` (`[]int` to `tuple(int, int)`)), refused:
  "must have the type it inherits". The same quotation: "fields can only
  be overridden with subtypes". The BPVM-only file has no VerseVM twin.
- *(c) A method overridden at a coerced signature*
  (`CoercedOverrides.versetest` 99-111: parameters `(X:int, Y:int)` by
  `(X:[]int)`, then by `(X:any)`, `<decides>` dropped;
  `FORT-642876-CollidingCoercedOverrideNames` 86-193: results `[]t` by
  `tuple(t, t)`, `<suspends>` dropped; `ParametricTypes.versetest:578`:
  `F(:tuple())` by `F()`), refused: "must have the signature of". Ch. 10
  says "method signatures must match exactly" (`:3175`), but allows a
  narrower result (`:539-567`).
- *openverse.* A class's table gives a field the type of the topmost class
  that has it (`TyEnv.coreFieldTy`); an override gives only a new default.
- *Mechanism.* (a): `classFields`, a field with no default; (b): a field a
  class types otherwise than one above it, read through accessors
  (`TyEnv.fieldAcc`, #205), the class table at the narrower type; (c): the
  dispatch adapters of #351 that coerce a result.
- *Size.* (a) 7 alone, (b) 25 more with (a), (c) 10.

**variance (38) and archetype-blocks (36).**
- *Forms.* `c(sub)` where `c(super)` is expected and the reverse, for
  classes and interfaces covariant, contravariant or bivariant in their
  parameter (`ParametricTypes.versetest` 59-177, 506, 537). The 34
  archetype-blocks cases of the same file stop at the parser first:
  `X:sup_f(sub) := sub_f(sup):`, a construction of a parametric class by a
  block archetype with no fields, in the file's shared modules
  (`ClassContravariantSubtyping` and the like), and those modules convert
  across variance, so every case of the file that takes the shared
  definitions needs variance as well. (`FunctionAsType` 183, 198 are
  VerseVM-only natives.) `SOL-6739-ParametricTypeMeetAndJoin` (8, under
  subtyping-to-any) joins such types.
- *Rule.* Ch. 10, "Instantiation and Identity" (`:1312-1490`): "The
  variance of a parametric type depends on how the type parameter is used
  within the class definition": covariant in return positions, contravariant
  in parameter positions, invariant in both, bivariant in none, and
  "Variance is computed over a type's full member set, including members
  inherited from a parametric base".
- *openverse.* Parametric classes are invariant. Verse Core's subtyping of
  references (`VTy.sub`, `Core/Typing.lean`) requires the target's type
  arguments to be a prefix of the source's, equal position by position, and
  the typing of a reference (`hasTy`) requires the object's recorded type
  arguments (`HeapTy`) to have the type's as a prefix, exactly. A view
  (#351) relates arguments by equalities only. A front-end conversion
  cannot help: the value is a reference, so a copy would lose its identity
  (`var` fields, `<unique>`), and representing a covariant parameter
  otherwise (boxed in `dyn`) would change every parametric class's layout.
  So variance needs Core: designed in [variance.md](variance.md) and left
  for the owner.
- *Size.* 38 + 34 + 8.

**singleton-types (19)** (`Void.versetest` 13, `FindFirstAsync…` 3,
`FORT-1054384` 2, `ParametricTypes:711`): `true` and `false` written as
types (`X:true = false`, `Y:?true = X` with `X:?void`). Not classes: the
type `true` holds the empty value alone and `false` none, which is the
empty-value work's (#600) to define; left.

**subtyping-to-any (11).** 8 are variance (`SOL-6739`); 3 convert a value
to one with `any` inside, `[int]string` to `[t]any` (`Any.versetest:60`)
and `type{_(:int):int}` to `type{_(:int):any}` (`Any.versetest:152`,
`SOL-3799:16`), a rebuilt map and a wrapped function value: not classes;
left.

**interface-rules (7 accepted that the tests refuse)** and the class cases
among type-checks-other and effect-checks: `Interface.versetest` 33, 40, 92
and `InterfaceDiamond:74` (an interface named twice among the parents) are
`feat/book-remaining-causes`'s; `Interface.versetest` 194, 199 and
`InterfaceDiamond:89` (`<override>` in an interface) the owner's; and
`ParametricTypes.versetest:465` (a module constant that constructs a
`<transacts>` class) is that branch's "a module constant has no side
effect". Two are classes and one check each:
`ParametricTypes.versetest` 263, 265 (a parametric class whose field names
itself at other type arguments) and 269 (two parametric classes whose
fields name each other). Ch. 10, "Disallowed: Polymorphic Recursion" and
"Disallowed: Mutual Recursion" (`:1578-1630`): "Polymorphic recursion
occurs when a parametric type references itself with a **different type
argument**", "Mutual recursion between multiple parametric types is not
supported either". `SOL-5838` 13, 22 refuse an array of two classes whose
nearest common supertypes are two (a class and an interface) even at an
expected element type both are below; openverse takes the expected type
there by design (LANGUAGE.md, "Subtyping and dispatch"), so it is a
reading for the owner, left.

**Order** (cases per unit of risk; dangerous first when cheap):
1. Polymorphic and mutual recursion of parametric types: 3 accepted
   refusals, one check in `classHierarchy`; risk: programs of openverse's
   own that have such fields.
2. `<final_super>` and the two functions: up to 96 cases, new forms only
   (no program that compiles today changes).
3. `<computes>` with additive heap effects: 30 cases, one rule in two
   places; programs that test the old refusal change.
4. Field overrides without a value, then at a subtype: 32 cases; the
   second changes the class table's field types and reads.
5. Method overrides at coerced signatures (10): adapters; after 4.
6. Variance (80 with the cases it unblocks): Verse Core, designed only.

## After the found bugs

Bugs found while doing other work, fixed one per commit on main `fb5e514`
and merged with main `e451452` (#614): an attribute on a
qualified definition of a module, the attribute an expression's refusal
names, the rational helpers of programs that use none, dead code in the
warnings of code never reached, the order of access errors, a `false` that
infers a type parameter, the markers of helpers used only in an
interpolation, and an empty `array{}` or `map{}` where a `comparable` is
expected. Against main's baseline, one case more agrees and none is worse:
8,237 agree, 1,304 refuse, 135 accept, 88 differ, 3,740 not translatable.
The one is `ParametricTypes.versetest:333`,
`assert{F7(false).Method(true)=true}`: `F7(false)` infers `t` as `logic`.
Merged with [the remaining causes](#after-the-remaining-causes) (#615,
`5103064`), a fresh run gives **8,290 agree, 1,123 refuse, 87 accept, 88
differ, 3,916 not translatable**: against #615's baseline the same one case
is better and nothing else changed; against this branch's before the merge
nothing is worse (53 more agree, 176 are the test runner's names, not
translatable now). The baseline and the tables of this note are from that
run.

## Forms of expressions, statements and the library: a map

A second map, at main `fdb1127` (8,290 agree, 1,123 refuse, 87 accept, 88
differ), of the causes that are forms of expressions, statements and the
library, beside [the first map](#the-remaining-causes-a-map), whose
verdicts it verified case by case with `scripts/book-conformance.sh show`
and the test files. Classes and subtyping (`class-specifiers`,
`override-defaults`, `variance`, `archetype-blocks`, `effects-of-classes`,
`singleton-types`, `subtyping-to-any`, `interface-rules`, `metatypes`) and
five rules that retire openverse readings (`race`/`rush` arms, `spawn`'s
effects and `spawn` in a failure context, `(super:)`, `<override>` in an
interface, every `for` filter) are other work; forms of theirs found in
these buckets are listed at the end. Left as before: `name-limits` and
`epic-limits` (the Blueprint VM's limits), `concrete-classes` (the
owner's), `union-types`, `live-variables` and `nested-functions`
(VerseVM-only or unreleased). "ch. N" is the Book's chapter at the pinned
revision, `docs/0N_*.md` and line; a test is `FILE:LINE` under `Tests/`;
(v) is `verse_vm_only`, (b) `bp_vm_only`; every case is untagged unless
marked.

### Accepted where the tests refuse (42 of these causes)

| Cause | Form (cases) | The Book | openverse | Mechanism; size | Verdict |
|---|---|---|---|---|---|
| syntax-other (3) | A1. a `.` followed by a line break or a comment, `O.⏎f`, `O.<#c#>f` (2: `ReserveDotSpace.versetest` 5, 6) | the tests (3100), which take `O. f` and `O<#c#>.f` (`:3`, `:4`, `:7`); prose silent | parsed as `O.f` | lexer: what may follow `.`; small | do |
| | A2. a field and a `block` with no separator in braces, `class{x:int block{}}` (1: `Classes/ClassBlockClause.versetest:19`) | the tests (3100; and `:20`, on lines of their own, valid) | parsed | parser: a separator after a field in braces; small | do |
| type-checks-other (20) | A3. `set S.M = …` of a struct that is not `<computes>` (1: `Mutability.versetest:426`) | ch. 5 `05_mutability.md:735`: "Only structs marked `<computes>` (pure structs) allow field mutation through a variable"; the tests (3509, `:425` valid with `struct<computes>`) | any struct's field set through a `var` | one check in `elabSet`; measure openverse's tests of structs | do |
| | A4. a type parameter that no parameter's type names, `F(:u where t:type, u:type)` (1: `ParametricFunctions.versetest:374`) | the tests (3503): `:338` `F(() where t:type):?t` refused too, `:376` `G(() where t:type):(t->void)` valid | refused only for a bounded one (`UpperBounds.checkDetermined`) | the same check for every type parameter, by where it occurs | do |
| | the rest (18) | | | | left, with the first map's reasons: contravariant type parameters (3, variance), `void` as a type argument (2: `Void.versetest` 246, 260, `class1(void){}.Foo(X)` with `X:int` refused), joins with two supertypes (2, class agent), Epic's limits (6), `using` paths (2), the runner's path (1), an enum of 256 values (1, b), `no_rollback` (1) |
| effect-checks (7) | `no_rollback` as the default of a function (3: `Effects.versetest` 490, 551, 552) | ch. 13 `13_effects.md:302`: "The `<transacts>` is the default for functions"; the tests (3512) | `<transacts>` | a rule over every call; the harness's `assert{F0(…)}` calls unannotated functions where `no_rollback` is refused | left: the Book disagrees with itself, and the tests with each other |
| | `spawn`'s effects (4: `Effects.versetest` 557 (b), 558 (b), 565 (b), 573 (v)) | | | | other work |
| control-forms (3) | A5. `using{/localhost}`, `using{/localhost/…}` (2: `Modules/Using2.versetest` 86, 90) | the tests (3544, 3587: "Explicitly using a "/localhost" package is not allowed", `:85`); `:94` `/localhostkinda` refused for another reason (3587, a path that names nothing) | a `using` of a path is ignored | one check where a `using`'s path is read | do |
| | an immediate arm of `race` (1: `Coroutines/Concurrency.versetest:832`) | | | | other work |
| initializer-effects (4) | a module constant whose construction allocates mutable memory (4, v: `GlobalVariables.versetest` 86-105) | ch. 16 `16_modules.md:617` | | VerseVM's link-time check | left |
| qualified-names (6) | the warnings 2003, 2004 for `(a:)F()` in an override (4: `SOL-3564…` 7, 18, 32, 45) | the tests' comments | accepted, no warning | a warning; the rule is unstated | left |
| | `(super:)` of another method or in a block (2: `Super.versetest` 183, 238) | | | | other work |
| duplicate-definitions (1) | A6. an enum value named `public` unqualified, `enum{ public }` (1: `QualifiedIdentifier.versetest:315`) | the tests (3532; `enum{ (A:)public }` valid, `:313`, "even if they alias a reserved word"; `enum{for}` 3514) | accepted | a name of the language's own definitions (the access specifiers) taken by an unqualified member | left: the rule (which names) is not stated; 1 case |
| persistable (1) | A7. an enum that is not `<persistable>` as a field of a `<persistable>` struct (1: `persistable.versetest:59`) | ch. 17 `17_persistable.md:190`: "Non-persistable enums - Enums without `<persistable>` specifier cannot be used"; the tests (3662) | an enum's `<persistable>` is parsed and dropped (`Parser.lean`), every enum persists | keep the specifier; one check in the persistable types | do |
| final-members (1) | a `<final>` method does not implement an interface's (1: `Attributes/final.versetest:125`) | the tests' comment (`:121`) | | a class rule | class agent |

### Different output (6 of these causes)

| Cause | Case | The Book | Verdict |
|---|---|---|---|
| comparison-chains (1) | B1. `not 1 <> 2 <> 1` (`Operators/Associativity.versetest:9`) | the Book disagrees with itself ([the wiki](https://github.com/rudi-cilibrasi/openverse/wiki/Where-the-Book-disagrees-with-itself), "Comparison chains with `<>`"): ch. 1 `01_expressions.md:890-891` chains every comparison; the tests make `<>` left-associative (`:6-9`) and chain `<`, `<=`, `>`, `>=` (`:11-33`) | do: follow the tests, `<>` left-associative (its left operand is all that precedes it, whose value is the leftmost operand), the others chained |
| empty-values-equal (4) | B2. `true? = false`, `not true??`, `(true? and true?) = false`, `x := true? or true; x = false` (`Operators/BoolQuery.versetest` 3, 4; `LogicalAnd.versetest:29`; `Precedence.versetest:121`) | the Book disagrees with itself (the wiki, "The value of `X?` on a `logic`"): ch. 8 `08_failure.md:57` "succeeds with that value"; ch. 2 `02_primitives.md:1233-1250` (the type `true` describes the empty value) and the tests: the empty value | do if the bytes it changes are only of programs that use the value: follow the tests |
| compound-set-order (1) | `set X[0] += if (set X = …; 0=0) …` (v: `ArrayAppend.versetest:12`) | a VerseVM split: its native twin `:23-27` says "TODO (SOL-9022): This doesn't produce the same result as the non-native array"; `:140`, `:183` (untagged) take openverse's order | left: a VM split, the untagged tests agree |

### Refused where the tests accept (my causes: 589)

| Cause | Forms (cases) | The Book | openverse; where | Mechanism; size | Verdict |
|---|---|---|---|---|---|
| types-other (121) | archetype clauses `let:` and `block` in a construction (4: `CustomClassVarAccessors.versetest:300`, `FORT-687100…` 51, 66, `Classes/Constructor.versetest:38`; and `Constructor.versetest:5` under block-forms) | ch. 10 (archetype instantiation); the tests | "a struct field is given as Name := value" (`Elab/Expr.lean`) | a construction's clauses: `let:` definitions before the fields, `block` run first; front end | do if time |
| | a `for` body at an expected element type (3: `SOL-4137…` 11, 21, `:decls`) | the tests | the body elaborated with no expected type: `false` is a `logic` | pass the element type into the body; one change | do |
| | `Args` defined by a program (2: `DefaultNamed.versetest:274`, `Math/Math.versetest:84`) | `Args` is openverse's (the command line), not the Book's | "'Args' is already the name of a function or constant" | add openverse's `Args` only when a program uses it and defines none | do |
| | a map literal's values of types with nothing in common join (3, under joins: `Any.versetest` 133, 134, `Map.versetest:164`) | the tests ("coerced to [key_type]any", `Any.versetest:131`); ch. 3 | "the values of this map have different types" | the join an array literal's elements have; one change in `elabMapLit` | do |
| | bottom typing: a `loop` that only `return` leaves as a function's value (2: `SOL-2336…` 10, `:decls`), `Y+(return)` (3: `FlowControl/Return.versetest` 143, 154, 155), `?` on a `not` (2: `Literals/Logic.versetest` 72, `:decls`), `()` where a `logic` is expected (2: `Void.versetest` 215, 219) | ch. 7; ch. 2 `02_primitives.md:1247` ("`true` is a subtype of `logic`, so the unit value flows into logic positions") | `void` where `never` or `logic` is expected | the type of a loop no `break` leaves (`never`); `void` to `logic` | left (each its own; the last with B2 and the singleton types) |
| | a tuple of ints concatenated with `+` (2: `ParametricFunctions.versetest` 416, 426); `for{I->X:Xs, I}`'s body a tuple (1: `FlowControl/for.versetest:445`); `logic{g[]}` of a parameter (1: `Function.versetest:83`); `F(:a)` beside `F(:[]a)` of an empty struct (1: `Overloading.versetest:260`); a user `ToString` beside the built-in (3: `Literals/String.versetest` 242, 243, `:decls`) | the tests | refused, each for its own reason | one check each | left, listed |
| | the test runner's (2: `weak_map.versetest` 41, 48 define `Main` with parameters) | | | harness: "the file defines `Main`" | do (harness) |
| | `GetRandomInt` (2), `classifiable_subset_var` (7), `subscribable_event_intrnl` (3) | the API reference | unknown | library: a random primitive (runtime); classifiable subsets and events (#11) | left |
| | inference: a type parameter of a map's value or a function's result (2: `2023-02-08-MapMemoryLeak…:11`, `SOL-5452…:6`); a generic function as a value (4: `Castable.versetest` 563, 601 (v), `ParametricFunctions.versetest` 192, 327) | the tests | "cannot infer", "is generic" | unification from an expected type; #214 | left |
| | `spawn` of a call whose arguments suspend (6, v: `FORT-571286…` 26, 34, 42; `SOL-4209…` 30, 39, 48), `spawn` in a `defer` (1: `defer.versetest:1094`) | ch. 14 | #156 | the lowering of `spawn` | left (other work touches `spawn`) |
| | cyclic field defaults (3: `DefaultValueAssignment.versetest:289` (v), `Pointers.versetest` 124, 125); a field's default calling a setter during construction (1: `CustomClassVarAccessors.versetest:558`) | the tests | refused (#511) | lazy defaults | left |
| | F-bounded classes (6: `FORT-642876…`); a type parameter passed on as a type argument (3: `FORT-741838…`, the BPVM's reading, [the wiki](https://github.com/rudi-cilibrasi/openverse/wiki/Where-the-Book-disagrees-with-itself)); `<computes><allocates>` functions (4: `Attributes/allocates.versetest:27`, `Effects.versetest` 174, 202, 253); types of one name and two arities (6: `SOL-7503…`, `SOL-7849…`); two interfaces' methods (3: `InterfaceWithFields.versetest` 86, 238, 463); a function type converted (2: `Void.versetest` 92, 104); refinement overloads and subtypes (6: `WhereConstrained{Floats,Ints}.versetest`); map keys of sibling classes (2, v: `Map.versetest` 363, 401); an override's overload (1: `Overloading.versetest:128`); function joins through `any` (8, v: `SOL-6945…` 53, 61, `FunctionTypes.versetest` 220, 227, `Void.versetest` 140-152); metatypes (4: `MetatypeConcreteSubtype.versetest` 153, 162, `ParametricFunctions.versetest` 464, `TypeAlias.versetest` 64, 65 (a class alias), …); `EmptyParametric()` (1); `ParametricTypes.versetest:222` (v); `ParametricFunctions.versetest` 546, 653, 719, 732, 752, `:decls` (a parametric class's `[]t` field default, `comparable` at `int`, a method's arity); `Classes/IdentifierSuper.versetest:4`, `Inheritance.versetest:3` (`attribute`), `Definitions.versetest:37` and `CustomClassVarAccessors.versetest:642` (definitions in expressions), `SOL-6109…:decls` (an overloaded function as a value), `FORT-976754…` (2, overloads' access), `QualifiedIdentifier.versetest:decls` (the runner's module) | | | class and subtyping rules (Core for F-bounds and variance), and the rest each its own | class agent (classes, subtyping, metatypes); the runner's module: harness (below); the rest left |
| library-diagnostic (93) | `ToDiagnostic(V).String` of every kind of value (`Intrinsics/ToDiagnostic.versetest`, 6 v, 1 b, 1 v) | API `ToDiagnostic(Value:any)<predicts><reads>:diagnostic`; `diagnostic`'s `String` and `diagnosable` are `<epic_internal>`; ch. 2 `02_primitives.md:867-884` ("may vary between VM implementations") | unknown function | every case passes its value through a parameter `Value:any` (`:5`, `:149`, `:206`): a `ToDiagnostic` over statically known types reaches none; an `any` that keeps its value (Core `void` now), a shortest round-trip float printer (21 cases), the runner's package path (12 expect `(/Verse.org/VerseTests:)`), type values (19) | left, designed (a research note) |
| syntax-other (69) | `TimSyntax.versetest` (35: specifiers after an expression `a<b>`, `->` and `:` as expressions, `try`/`catch`, `&x`, units, `do`, `for(…)<par>`, …), `Roundtrip/*` (5), `FunctionTypes.versetest` 4-27, 262 (6: `f(:int):int` types as expressions, `map` as a name), constructor delegation outside a constructor's body (4: `Classes/Constructor.versetest` 122, 280, 648, 655), `TypeParam.versetest` 18-38 (4: `[]t`, `?t`, `->` as type arguments of calls), `ParametricFunctions.versetest` 469, 490 (2), `Mutability.versetest:479`, `Type.versetest:20`, `ParametricTypes.versetest:375`, `generators.versetest:29`, `String.versetest:229`, `Attributes.versetest:44`, `allocates.versetest:20`, `SOL-3662…:49`, `2020-06-18-…:decls`, and VerseVM's (3: `Union`, `when`, `NestedFunctions`) | `TimSyntax.versetest` is "converted from Tim's parser test suite", parse-only; no chapter | parse errors | parser forms, one each | left: no prose; the first map's verdict |
| set-forms (35) | C1. `set` through a call's result or a construction, `set F(…).X = …`, `set c0{}.X += …` (6: `AssignmentSequencing.versetest` 17, 23, 38, 44; `FORT-779650…` 27, `:decls`); C2. `set M[1,2] = 1` (1: `Map.versetest:472`) | ch. 5; the tests pin the order: the root, then the keys, then the value (`AssignmentSequencing.versetest` 17-48) | "openverse supports set X = …" (`elabSetWith`) | bind the root to a local first; `M[1,2]` as `M[(1,2)]`; front end | do |
| | `set live` (28, v) | | | | left (live variables) |
| localization (34) | D1. `<localizes>` constants and functions of `message`, `Localize`, `Join`, messages as fields, in arrays, named and tuple parameters (34: `Localization.versetest`, `LocalizationJoin.versetest`, `SOL-3887…`, `SOL-3734…`) | ch. 12 `12_access.md:885-1100`; API `Localize(Message:message)<reads>:string`, `Join(Messages:[]message, Separator:message)<transacts>:message`, `message := class<epic_internal>`; ints "formatted with comma separators" (`:964`); the tests' refusals (forms without `: message`, 3639; a value that is no string literal, 3638; a parameter of a class or an option, 3509; a message in a function, 3651; `{"print"}`, 3652), which agree now through the unknown specifier | "unknown or unsupported specifier <localizes>" | a front-end desugaring with the source rules: a message is its default text rendered (no cultures); a helper for comma-grouped ints | do |
| qualified-names (26) | the test runner's package path `/Verse.org/VerseTests` and its `snippet{…}` (8: `QualifiedMethodInheritance.versetest:153`, `:decls`, `QualifiedIdentifier.versetest` 474, 482, 483, `GetSecondsSinceEpoch.versetest:16`, `Modules/Module.versetest` 230, 232) | the runner's | "has no name or path in openverse" | harness: not translatable | do (harness) |
| | two members of one name in a class, `(c:)M` beside an inherited `M` (10: `SOL-3564…` 57, 66, 201, `:decls`, `InterfaceWithFields.versetest` 247, 260, 562, `ShadowDefinition.versetest` 113, 199, `Super.versetest:56`) | ch. 10 lines 978-1025 | "a second method … beside the one … inherits" | members keyed by qualifier | class agent |
| | others (8: `SOL-8768…` 19, `:decls` (a qualified extension field), `ParametricFunctions.versetest:119` (`(super:)X` as a value), `ShadowDefinition.versetest` 128, 145, 146 (parse), `TimSyntax.versetest:325`, `Union.versetest:80` (v)) | | | | left |
| library-other (22) | `GetCastableFinalSuperClass` (15, `verse_vm_todo`), `signalable(t)` (2), `GetSecondsSinceEpoch` (2), `FitsInPlayerMap` (3) | the API reference | unknown | #11; a clock primitive (runtime); persistence | left |
| empty-containers (20) | D2. `array{}` and `map{}` with no type from context: `A1:=array{}`, `array{}.Remove[0,0]`, `array{}+""`, `Concatenate(array{})`, `for(X:array{}, …)`, `Map:=map{}` (20; and `Intrinsics/Concatenate.versetest:4`, `Concatenate()`, under types-other) | the tests; ch. 1 `01_expressions.md:1274` writes `Empty := array{}`; ch. 3 `03_containers.md:273`: "Without a type annotation, the compiler cannot determine what type of array you want" | "the type of an empty array{} must be given" | the element type `false`, below every type (`Ty.never`); an empty array of it converts to every array type | do |
| joins (16) | the map literal's values (3, above); function values joined by their types' subtyping (5: `ParametricTypes.versetest` 1321, 1329, `WhereConstrainedInts.versetest` 237, 241, `Comparable.versetest:216` (v), `SingleParamArray.versetest:94` (v)); variance (7: `SOL-6739…`) | | | | the map's values: do; the rest class agent (subtyping, variance) |
| operator-definitions (14) | `operator'+'(L, R)`, `prefix'-'(X)` defined by a program and used by the operators (13: `2023-01-17-CharLiteralAsOperand…`, `Overloading.versetest` 206-212, `StringInterpolationPlus.versetest`), `TimSyntax.versetest:230` | the tests; ch. 4 names `operator'+'` in an error message only (`04_operators.md:646`), ch. 11 `11_types.md:939` declares `operator'='` | parse error | a function's name `operator'op'`; an operator not built in calls the overload; front end | do if time |
| path-literals (13) | `import(/Verse.org/Tests/VerseTestScriptCmd/…)`, the runner's modules (12: `QualifiedIdentifier.versetest` 33-55; with `:decls` under types-other); `Alias:=import(/Verse.org)` (1: `FORT-582128…:5`) | ch. 16 `16_modules.md:452-470` | "unknown function 'import'" | harness for 12 (the runner's package, not translatable); a module alias for 1 | do (harness); the alias left |
| partial-modules (11) | one module in several parts (11: `PartialModuleDefinitions.versetest` 157-176, `available.versetest` 317, 326, `AccessLevelInheritance.versetest:669`, `FORT-722788…`) | the tests (`:157-176`, with the parts' access and qualifiers agreeing, 3623) | "module X is defined twice" | the modules' flattening: parts of one name merged, with two checks | do if time |
| ranges (11), first-forms (11) | D3. generators in `first` (11: `FlowControl/first.versetest` 24-202, `:decls`), with ranges among `first`'s clauses (7: `first.versetest` 36-51, 206); a typed range binding `X:int := a..b`, `X:int = a..b` (4: `Exercises/TwoSum.versetest` 30, 33, `:decls`; `FlowControl/for.versetest:17`) | ch. 7 `07_control.md:923-1010` ("the same binding syntax as `for`", `:972`) | "a generator X : source in first is not supported yet"; "a range a..b can only be the source of a for clause" | `first` with generators: the `for` search stopped at the first success; a typed binding over a range | do |
| named-tuple-elements (11) | named parameters in a tuple parameter (8); named tuple values (3, `verse_vm_todo`) | ch. 6 `06_functions.md:371-425` | refused ([tuple-parameters.md](tuple-parameters.md)) | front end, designed there | left |
| impossible-casts (11) | casts that cannot succeed, which the tests accept (11) | the tests | refused ("would always fail") | a refusal openverse adds; 4 of them need a class the harness drops | left (a warning would follow the Book; measured later) |
| unnamed-parameters (7), nested-tuple-parameters (4), archetype-separators (3), char-literals (2), type-aliases (1), generators (1) | parse-only forms of `TimSyntax.versetest` and `Roundtrip/*` (`:C=C{}`, `(A, B):=…`, `'ab'`), `g(:int):void={}` nested (2), `t(u:type):=type{…}` (1), `[int;int]`, `generator(t)` (1), `type{F()<converges>:void}` (1) | no prose | parse errors | parser forms | left |
| closed-functions (7) | `<closed>` (6 v, `FunctionAsType.versetest`; 1 `closed.versetest:16`) | | #494 | | left (owner) |
| comparable-classes (4) | `<unique>` interfaces with no class below compared (4: `ComparableInterface.versetest`) | | | | class agent |
| module-objects (4) | module constants of `<unique>` classes (4: `GlobalVariables.versetest` 72-74, `:decls`) | ch. 16 `16_modules.md:617` | one object per use | initializers run once before `Main`: the module state of [weak-map.md](weak-map.md) | left (designed there) |
| block-forms (3) | `block` in a construction (1, above); `spawn{}` of several expressions (1, v: `SpawnAndTask.versetest:1030`); `branch` in a loop (1, v: `branch.versetest:183`) | | | | left |

### The order

Cases per unit of risk, the accepted refusals first: A1, A2 (3, parser
checks); A3, A4, A5, A7 (5, one check each); the harness's runner names
(13 + 8 + 2); B1 (1); then D2 (20+), D1 (34), D3 (22), C1 and C2 (7), the
map literal's join (3), the `for` body's expected type (3), `Args` (2); B2
if its bytes allow; then the archetype clauses, partial modules and
operator definitions as time allows; `ToDiagnostic` designed in a note.

## After classes and subtyping

The causes about classes and subtyping ([the map](#classes-and-subtyping-the-map)),
built on main `e451452` in eight commits, one form each, with the rules
pinned in [classes-and-subtyping.md](classes-and-subtyping.md) and the
Verse Core design for variance in [variance.md](variance.md); merged with
main `b70272c` (#615) and `fdb1127` (#616). Against main's baseline (8,290
agree, 1,123 refuse, 87 accept, 88 differ, 3,916 not translatable), 162
cases more agree and none is worse: **8,452 agree, 964 refuse, 84 accept,
88 differ, 3,916 not translatable** (re-recorded from a fresh run on the
merged compiler; `compare` after each commit: 0 worse).

| Form | Rule (where) | Agree now | Left |
|---|---|---|---|
| polymorphic and mutual recursion of parametric types | refused: a parametric class or interface names itself in its fields only at its own type parameters, and none names another that names it back (ch. 10, `checkParametricRecursion`) | 3 accepted refusals: `ParametricTypes.versetest` 263, 265, 269 | |
| type values have no effect | making a type value and casting through one is `<computes>` (`TypeValues`) | (needed by the next) | |
| `<final_super>`, `GetCastableFinalSuperClass[FromType]` | a `<final_super>` class has a parent; the queries give the castable `<final_super>` class right below `B` on the instance's (or type's) chain, topmost first, and fail otherwise (ch. 10, 11, the API; `FinalSuper.desugar`); `any`, `comparable` are values of `type` | 95: `GetCastableFinalSuperClass.versetest` 87, `Attributes/FinalSuperAttribute.versetest` 7, `Castable.versetest:659`; its 7 refusals agree by their rules | `MetatypeConcreteSubtype.versetest:58` agrees through the last row |
| `<computes>` with additive heap effects | `<computes><allocates>` allows those (ch. 13: one exclusive specifier, any additive ones; `constructionFx`, `checkSpecs`, `checkExclusive`) | 30: `Attributes/allocates.versetest` 6, 13, 20, 27, 57; `Attributes/unique.versetest` 90-137 (6); `Operators/CompareMap.versetest` 8 and `:decls`; `Map.versetest` 151, 174; `weak_map.versetest` 6, 624, 667, 668, 669; `Effects.versetest` 174, 202, 253 | 3, other causes now: `Map.versetest:143` (a map literal of two sibling classes), `Map.versetest:decls` (`false` as a type), `weak_map.versetest:639` (a value type that does not persist, its rule) |
| a field `<override>` without a value | it re-declares the field with no default (the tests: `Attributes/override.versetest` 29-47; `classFields`) | 5: `Attributes/override.versetest:33`, `Attributes/concrete.versetest` 59, 110, 230, `SOL-3366:53` | |
| a class's field re-declared at a subtype | a field that is no `var` may be narrowed; the class and those below hold it at the narrower type, reads through those above convert it up (ch. 10, "Overriding Members"; `TyEnv.narrowed`, `fieldSrc`) | 19: `Attributes/override.versetest` 3, 133, `:decls`; `Any.versetest` 163, 164; `RefinedMapKeyInterfaceOverride.versetest` 7; `InterfaceWithFields.versetest` 358, 377; `MetatypeConcreteSubtype.versetest` 116, 284, 289, 294; `AccessLevelInheritance.versetest:863` | |
| `T{}` through a field of a `concrete_subtype` | in a method, as for a local, with the construction budgets of every `<concrete>` class it may construct (ch. 11; `SOL-8627`) | 10: `MetatypeConcreteSubtype.versetest` 58, 216-263 (8), `:decls` | `MetatypeConcreteSubtype.versetest` 153, 162 (`Type := c; Type{Value := 42}`, fields given through a type value whose type is its class's) |
| variance | Verse Core relates references' type arguments by equality ([variance.md](variance.md)) | | 38 + 31 (archetype-blocks) + 8 (`SOL-6739`): designed, for the owner |

- **Per cause, at `e451452` and now** (the merged branches' changes
  included): class-specifiers 84 → 3 (81 agree; left `<converges>`,
  `<native_callable>`, `<persistable>`, none about classes);
  library-other 23 → 7 (the 15 query cases agree); override-defaults 47 →
  13 (33 agree, 1 is qualified-names now: `InterfaceWithFields.versetest:decls`
  reaches `(Class112:)Value`, a second method of a name); effects-of-classes 28 → 0 (25 agree, 3
  other causes, above); variance 38 → 38; archetype-blocks 36 → 31 (5 not
  translatable since #615); singleton-types 19 → 20 (`Map.versetest:decls`
  reaches `false` as a type now); subtyping-to-any 11 → 11; interface-rules
  7 → 3 (#615's 4; the 3 left are `<override>` in an interface, the
  owner's).
- **Moved the wrong way:** none. Cases that changed cause and stay
  refused: the three above; `SOL-8627-concrete_subtype-effects.versetest:3`
  agrees by its rule now (it agreed through "unknown struct" before);
  `Attributes/override.versetest:38` and the `SOL-9745` refusals agree by
  the construction and `<concrete>` rules (they agreed through "must give
  a new default").
- **Where the Book disagrees with itself:** the API reference types
  `GetCastableFinalSuperClassFromType`'s second parameter
  `sub_type:subtype(base_type)`, and its tests pass types outside it and
  expect a failure at run time (`GetCastableFinalSuperClass.versetest` 109,
  303, 304, 330, 331); openverse follows the tests
  ([classes-and-subtyping.md](classes-and-subtyping.md#final-super-classes)).
  Ch. 10 says "method signatures must match exactly" (`:3175`), the tests
  override at coerced signatures (`CoercedOverrides.versetest` 86-113,
  `FORT-642876`); left, below.
- **Left, with what each needs:** method overrides at coerced signatures
  (`CoercedOverrides` 4, `FORT-642876` 5, `SOL-3731` 3 with a result `t`
  over `comparable`, `ParametricTypes.versetest:578`): an adapter per
  override that converts its arguments (a tuple of parameters to an array,
  `any`) and result (a tuple to an array, a type parameter to its bound's
  box) and drops `<decides>` or `<suspends>`, as the spawned dispatch's
  adapters convert a result; variance: Verse Core ([variance.md](variance.md));
  singleton types `true` and `false` (20) and the three conversions to a
  type with `any` inside: not classes, the empty value's and the
  conversions' work; `SOL-5838` 13, 22 (a join refused at an expected type
  both classes are below): the owner's reading.
- **Programs.** Against main `fdb1127`, over every suite and the corpus
  `corpus2` (5,890 programs in both), no program's bytes, output or
  messages changed but three tests that pinned what the Book's rules
  change: `tests/errors/class_param_const_mutable.verse` (its class named
  itself at other type arguments; it reaches the `var` field through
  another class now, same message), `tests/errors/fx_computes_and_reads.verse`
  and `tests/errors/fx_generic_computes.verse` (they pinned the refusal of
  `<computes><reads>`; they pin now that such a function may not write);
  `tests/errors/iface_placeholder_grows.verse` is
  `parametric_recursion_interface.verse`, refused where its type is
  defined; and the construction-effects oracle
  (`tests/scripts/test-construction-effects.py`) checks `<computes>` with
  each heap subset instead of its refusal.

## After the forms of expressions, statements and the library

[The map of forms](#forms-of-expressions-statements-and-the-library-a-map)
worked down from its order, one form per commit, each rule pinned in
[book-forms-rules.md](book-forms-rules.md) and described in
[LANGUAGE.md](../LANGUAGE.md), and `ToDiagnostic` designed in
[to-diagnostic.md](to-diagnostic.md); built on main `fdb1127`, merged with
main `215af57` (#617). Against main `215af57` (8,452 agree, 964 refuse, 84
accept, 88 differ, 3,916 not translatable), from fresh runs of both:
**8,544 agree, 856 refuse, 77 accept, 87 differ, 3,940 not translatable**;
no case that agreed agrees no longer, none became an accepted refusal or a
different result, and 24 refusals are the test runner's now (not
translatable). The baseline is from the run on the final commit.

| Cause (main `215af57` → now) | Done | Left, and what it needs |
|---|---|---|
| syntax-other, accepted (3 → 0) | a `.` followed by a line break or a comment (`ReserveDotSpace.versetest` 5, 6); two members of a class in braces with no separator (`ClassBlockClause.versetest:19`) | |
| type-checks-other, accepted (17 → 15) | a struct's field set only when the struct is `<computes>` (`Mutability.versetest:426`); a type parameter its signature names nowhere (`ParametricFunctions.versetest:374`) | contravariant type parameters (variance), `void` as a type argument, Epic's limits, `using` paths, `no_rollback`: the first map's reasons |
| control-forms, accepted (3 → 1) | `using{/localhost…}` (`Using2.versetest` 86, 90) | an immediate `race` arm (other work) |
| comparison-chains, different (1 → 0) | `<>` is left-associative, the others chain (`Associativity.versetest:9`) | |
| localization (34 → 0) | `<localizes>` messages, `Localize`, `Join` | |
| empty-containers (20 → 0) | `array{}`, `map{}` and `Concatenate()` with no type from their context are of `false`; an empty map of `false` joins another | (as types-other) `false + array{}` (`Array.versetest:108`), `array{}.ReplaceAll(array{}, array{})` (`ArrayReplaceAll.versetest:12`) |
| first-forms (11 → 1), ranges (11 → 0) | generators in `first`, a filter of one that cannot fail refused; a range's typed binding | `first{X:=1..5, 3*X>10}`, a generator in a tuple (`first.versetest:206`) |
| singleton-types (20 → 15) | `false` as a type (5) | `true` as a type (15): `()` typed `tuple()` first, which `void` must not convert to (`FORT-582630-BranchResult.versetest:3`) |
| path-literals (13 → 1), qualified-names (27 → 20), types-other (118 → 109) | the test runner's modules (`import(/Verse.org/Tests/VerseTestScriptCmd/…)`, 13) and package path (`(/Verse.org/VerseTests…:)`, 11), not translatable; a snippet's own `Main(Data:…)` renamed (`weak_map.versetest` 41, 48, `ParametricTypes.versetest:283`); `Y+(return)` (`Return.versetest` 143-155) | `Alias:=import(/Verse.org)`; two members of one name (class agent); the rest of types-other as the map lists |
| library-diagnostic (93) | | designed ([to-diagnostic.md](to-diagnostic.md)): an `any` that keeps its value (60), a shortest float printer in Verse Core (18), the runner's path (13), unbounded ints (6) |

- **Programs.** Over every suite and the corpus `corpus2` (5,937
  programs), against main `215af57` compiling the same sources, the only
  programs whose code, messages or exit changed are the new and rewritten
  tests and 46 generated programs of the `mv` model that write a `<>` after
  another comparison (`mv-plain` 23, `mv-rec` 9, `mv-bif` 7, `mv-mv` 7),
  whose meaning the rule changes; the model now follows it, and 1,000 of
  its seeds agree in Lean, C and the model (984 run, 16 skipped as over
  12,000 lines, 0 bad). Tests rewritten, output the same: ten that set a
  plain struct's field declare it `<computes>` (`structs`,
  `generic_structs`, `nested_set`, `set_op_order`, `set_op_order_paths`,
  `choice_set_path_more`, `weak_map`, `class_refs_paths`,
  `iface_field_set_paths`, `mutation_tooling`; their code the same), and
  the error test `set_path_not_var`; `fn_values_method_instance_unused`
  and `alias_type_parameter` name their type parameter; four error tests
  of a phantom type parameter are refused for it now
  (`fn_value_open_phantom`, `fn_method_instance_phantom`,
  `fn_method_tuple_phantom`, `fn_context_method_phantom`);
  `dot_body_next_line` gets the lexer's message; four error tests are valid
  programs now and moved to `tests/verse` (`empty_literal_int`,
  `if_clause_both_untyped`, `if_clause_refining_untyped`,
  `first_generator`).
- **Where the Book disagrees with itself** (openverse follows the tests):
  an empty `array{}` with no type (ch. 3 `03_containers.md:273` against
  ch. 1 `01_expressions.md:1274` and `Array.versetest:90`); `<>` (ch. 1
  `01_expressions.md:890-907` against `Associativity.versetest:6-9`, already
  on the wiki); a type parameter only a function type's parameter names
  (`ParametricFunctions.versetest:348` against VerseVM's
  `FORT-592189-MaybeCoerceToTypeCrash.versetest:44`; openverse keeps
  accepting); and, left, `true?`'s value (ch. 8 `08_failure.md:57` against
  ch. 2 `02_primitives.md:1233-1250` and `BoolQuery.versetest` 3, 4, on the
  wiki).

## After variance

The variance of parametric classes and interfaces (ch. 10, "Instantiation
and Identity"), built in Verse Core with its proofs and in the front end
([variance.md](variance.md)), on main `215af57` and merged with main
`84285c1` (#618). Against main's baseline (8,544 agree, 856 refuse, 77
accept, 87 differ, 3,940 not translatable), 47 cases more agree and none is
worse or changed otherwise: **8,591 agree, 809 refuse, 77 accept, 87
differ, 3,940 not translatable** (re-recorded from a fresh run on the
merged compiler; before the merge, against `215af57`'s 8,452: 8,499, the
same 47).

| Form | Rule (where) | Agree now | Left |
|---|---|---|---|
| a class's or interface's instances by variance | each type parameter covariant, contravariant, invariant or bivariant by its uses in the members, inherited ones included, function types' parameters contravariant (ch. 10; `TyEnv.bookVariances`); a conversion also needs Verse Core's subtyping of the two references, by each concrete class's variances (`Sigs.inferVariances`, `refUp`) | 38: `ParametricTypes.versetest` 59-156 (32: each kind for classes and interfaces, directly, through a class or interface below, with methods and with function-typed fields), 174-177 (4: instances of the file's shared classes), 506, 537 | |
| joins and conversions by variance | at an expected type, both at it; without one, a class above both at its arguments' join by variance (`joinTyShaped`) | 9: `SOL-6739-ParametricTypeMeetAndJoin.versetest` 6, 11, 16, 25, 99, 104, 109, 122, 216 | 6: 38, 138 (to an instance at `any`, which holds no value in openverse); 58, 74, 161, 177 (a contravariant interface or class whose implementation holds the parameter in a field, `Data:t`: Verse Core types a reference by its object's own class) |
| an archetype block with no fields | `X := c(args):` with nothing indented below is `c(args){}` (the Book's tests; `Parser`) | (needed by the archetype-blocks cases) | the 31 archetype-blocks cases now stop at `default_param.class1` defined twice: a type named at two arities, `class1(t)` and `class1()` (`i()` beside `i(t)`), in a module that each case includes (harness over-inclusion) |

- **Per cause, at `84285c1` and now** (the same at `215af57`, where
  types-other was 118 → 149): variance 38 → 0 (38 agree); archetype-blocks
  31 → 0 (they parse and reach `types-other`: the type named at two
  arities); subtyping-to-any 11 → 5 (6 `SOL-6739` agree); joins 16 → 13 (3
  `SOL-6739` agree); types-other 109 → 140 (the 31).
- **Moved the wrong way:** none.
- **Where the Book disagrees with itself:** the tests comment out the
  variance of a class with a `var` field, "# TODO: classes containing
  pointer members aren't allowed." (`ParametricTypes.versetest:163`,
  `:182`), where ch. 6, "Polarity and Variance", has one as an invariant
  class: "`c(t:type) := class{var X:t}  # Mutable field makes c invariant
  in t`" (`06_functions.md:1495`). openverse follows ch. 6: a `var` field of
  `t` makes its class invariant in `t`.
- **Left, with what each needs:** the 6 `SOL-6739` cases (`any` holding a
  value; an override typed at its object's own type arguments and called
  through the declared signature, in Verse Core: [variance.md](variance.md),
  "What is left"); the 31 archetype-blocks cases: a type named at two
  arities.
- **Programs.** Against main `84285c1`, over every suite and the corpus
  `corpus2` (5,957 programs in both: 5,909 the same), no program's output,
  messages or exit code changed but this work's 13 new tests (`variance_*`,
  which main refuses or refuses otherwise); 35 programs' bytes changed (32 of the corpus' `heterogeneous`
  programs, `tests/verse/choice_heterogeneous_contracts.verse`,
  `fn_values_method_variance_contexts.verse` and
  `multi_method_tuple_ordinary_other_receiver_inside_class.verse`): their
  choices' alternatives are instances of a covariant class at different
  type arguments (`box(int)` and `box(string)`), which join at the class
  now (`box(comparable)`), as the Book's subtyping has them, where they were
  kept apart before; each runs as before, in Lean and in C.

## After the held rules

The five rules of the accepted refusals that [After the remaining
causes](#after-the-remaining-causes) measured and left for the owner, built
by the owner's rule ("for everything we go by the book for now"), one rule
per commit, each pinned in [book-remaining-rules.md](book-remaining-rules.md)
with what it retires; merged with main `fdb1127` (#616), `215af57` (#617)
and `84285c1` (#618). `compare` after each, against the baseline of the
commit before (totals: agree, refuse, accept, differ, not translatable):

| Rule | Totals after it | Better |
|---|---|---|
| main `b70272c` | 8,289, 1,124, 87, 88, 3,916 | |
| every arm of `race` and `rush` can suspend | 8,290, 1,124, 86, 88, 3,916 | `Coroutines/Concurrency.versetest:832` |
| merged with `fdb1127` (main: 8,290, 1,123, 87) | 8,291, 1,123, 86, 88, 3,916 | |
| `spawn` has `<transacts>`'s effects | 8,293, 1,123, 84, 88, 3,916 | `Effects.versetest` 558, 573 |
| `(super:)M` only in an override of `M` | 8,295, 1,123, 82, 88, 3,916 | `Super.versetest` 183, 238 |
| merged with `215af57` (main: 8,452, 964, 84) | 8,457, 964, 79, 88, 3,916 | |
| an interface overrides nothing | 8,460, 964, 76, 88, 3,916 | `Interface.versetest` 194, 199, `InterfaceDiamond.versetest:89` |
| every filter of a `for` can fail | 8,460, 964, 76, 88, 3,916 | none: `FlowControl/for.versetest:223` agreed already, through the literal filter's rule |
| merged with `84285c1` (main: 8,544, 856, 77, 87, 3,940) | 8,552, 856, 69, 87, 3,940 | |
| every filter of a `first` with a generator can fail | 8,552, 856, 69, 87, 3,940 | none: `FlowControl/first.versetest:30` agreed already (main's literal-or-name check), and agrees by this rule |
| merged with `feat/variance` `6c615aa` (#619: 8,591, 809, 77, 87, 3,940) | 8,599, 809, 69, 87, 3,940 | against #619: the 8 above; against this branch: variance's 47 |

Against main `84285c1`'s baseline (8,544 agree, 856 refuse, 77 accept, 87
differ, 3,940 not translatable), 8 accepted refusals agree and nothing is
worse: **8,552 agree, 856 refuse, 69 accept, 87 differ, 3,940 not
translatable**. Merged with [variance](#after-variance) (#619), and
re-recorded from a fresh run on the merged compiler, with the tables above
and the appendices: **8,599 agree, 809 refuse, 69 accept, 87 differ, 3,940
not translatable**; against #619's baseline 8 better (this work's) and
none worse, against this branch's 47 better (variance's) and none worse.

- **Per cause, on main `84285c1` and now:** control-forms 1 → 0;
  effect-checks 7 → 5 (left: `no_rollback` as a function's default effect,
  3, and the BPVM's `spawn` in a `<transacts>` function, 2, its
  `no_rollback` reading of `spawn`); qualified-names 6 → 4 (left: the
  warnings 2003 and 2004); interface-rules 3 → 0.
- **Moved the wrong way:** none; no case became an accepted refusal or a
  different result.
- **`spawn` in a failure context** (#156, 29 refusals): looked at again
  ([the rule](book-remaining-rules.md#spawn-has-transactss-effects)) and
  kept: relaxed outside `<suspends>` functions, 13 cases agree, 7 give a
  different result (awaiters run inside `Signal`) and the BPVM's
  `SoftwareTransactionalMemory.versetest:505` is accepted, and the form
  cannot tell them apart.
- **Programs.** Against main `84285c1`, over every suite and the corpus
  `corpus2` (5,906 programs in both, 38 in main's only, 32 in this
  branch's only): 5,140 the same (against #619's compiler, after the merge:
  5,919 in both, 5,153 the same, and the same 766 differ, none of
  variance's tests among them); of the 766 that differ, 653 are programs
  of corpus2 a rule refuses now (`spawn` 20, `(super:)` 20, an interface's
  override 24, a filter 589) and 38 more whose refusal on main gives way to
  a rule's message first (`generic-mv` 16 and 21, `gadt_contexts` 1); 69
  are tests rewritten to the Book's forms, their output the same (their
  code changed); 5 are error tests rewritten to keep their subject in the
  Book's forms, and 1 (`first_filter_name`) has the general rule's message.
  The 38 programs only main has are the tests deleted and renamed, the 32
  only this branch has the new tests and the renamed ones.

## After `ToDiagnostic`, `true` and the full type-parameter rule

The list #618 left ([what is left](#after-the-forms-of-expressions-statements-and-the-library)),
in its order: `ToDiagnostic`, `true` as a type, the full rule of
determined type parameters, then smaller forms, one per commit, each rule
pinned in [to-diagnostic.md](to-diagnostic.md) and
[book-forms-rules.md](book-forms-rules.md) and described in
[LANGUAGE.md](../LANGUAGE.md). Built on main `84285c1`, merged with
`396c9f8` (#619) and `dca5ad1` (#620). Against main `dca5ad1`'s baseline
(8,599 agree, 809 refuse, 69 accept, 87 differ, 3,940 not translatable),
from a fresh run on the final commit, whose verdicts are the baseline now:
**8,692 agree, 703 refuse, 65 accept, 92 differ, 3,952 not translatable**.
93 cases more agree (89 refused before, 4 accepted refusals), 12 refusals
are the test runner's (not translatable), and 5 refusals give a different
result (below).

| Form | Rule (where) | Agree now | Left |
|---|---|---|---|
| `ToDiagnostic` | in a program that calls it, an `any` is an object that prints its value, of a class the front end writes per type (`Front/Diagnostic.lean`, `wrapAny`, `Requests.anys`); the format of the Book's tests | 62 (`Intrinsics/ToDiagnostic.versetest`: booleans 2, ints 11, rationals 10, chars, char32s and strings 24, options 4, arrays and tuples 6, a map 1, `diagnosable` objects 2, a diagnostic's diagnostic 1, `ToDiagnostic` as a value 1) | floats 14 (refused: the shortest round-trip printer is Verse Core's); the test runner's path in the expected string 11 and its `tuple_struct` 1 (not translatable); `verse_vm_only` ints past 64 bits 5 (now a different result, int-precision); type values 18 (not translatable, as before) |
| `true` as a type | the type of the empty value alone, as `tuple()`; `void` and `true` interchange inside options, arrays and maps; `void` to `logic`; a `branch:`'s value an `any` (`resolveTy`, `Ty.unitUp`, `elabBranch`) | 12 (`Void.versetest` 50, 56, 68, 80, 177, 215, 219, 253, 267, `:decls`; `FORT-1054384` 17, `:decls`) | `true` in a function type, 5 (`Void.versetest` 100, 161-173, under types-other now); `true?`'s value, 4 (designed, [the rule](book-forms-rules.md#the-value-of-true)) |
| every type parameter given by the parameters | by the Book's variance: where values go in, a parameter's covariant place or the result's contravariant one; the expected result no longer gives one (`checkDeterminedTypeParams`) | 4 accepted refusals (`ParametricFunctions.versetest` 348, 356, 361, 366) | |
| a map literal's disjoint values | joined as an array literal's elements (`elabMapLit`) | 3 (`Any.versetest` 133, 134, `Map.versetest:164`) | |
| a `for` body at the element type expected | elaborated again at it when its value does not convert (`elabECore`) | 3 (`SOL-4137…` 11, 21, `:decls`) | |
| `Args` bound by a program | openverse's `Args` only when the program binds none (`argsAndMethodOverloads`) | 2 (`DefaultNamed.versetest:274`, `Math/Math.versetest:84`) | |
| `set` through a call's result or a construction; a key of several values | the root bound first, then the keys and the value (`elabSet`) | 7 (`AssignmentSequencing.versetest` 17, 23, 38, 44; `FORT-779650…` 27, `:decls`; `Map.versetest:472`) | `set live` (VerseVM's live variables) |

- **Per cause, on main `dca5ad1` and now:** library-diagnostic 93 → 14;
  singleton-types 15 → 0 (12 agree; the 5 of a function type are
  types-other now); type-checks-other, accepted, 15 → 12 and epic-limits,
  accepted, 12 → 11 (the type-parameter rule); joins 13 → 10; set-forms
  35 → 28; types-other 140 → 138 (7 agree, 5 more of `true` in a function
  type); int-precision, different, 82 → 87. The rest unchanged (a fresh
  run of main `dca5ad1` with causes: 8,599, 809, 69, 87, 3,940).
- **Moved the wrong way:** 5 cases, `Intrinsics/ToDiagnostic.versetest`
  36-40 (`verse_vm_only`): refused before (no `ToDiagnostic`), they run
  now and their own operands overflow, `(9223372036854775807+1)*1+0`,
  openverse's ints being the Blueprint VM's (cause int-precision, 87 now),
  as the 56 bitwise cases before them did. No case that agreed agrees no
  longer, and none became an accepted refusal.
- **Where the Book disagrees with itself:** `true?`'s value (ch. 8
  `08_failure.md:57` against `Operators/BoolQuery.versetest` 3, 4, on the
  wiki), left. What the wiki lists as a split by VM for a type parameter
  named only by a function type's parameter is none:
  `FORT-592189-MaybeCoerceToTypeCrash.versetest:44`'s `MakeClosure` names
  `payload` in its result's function type's parameter, which determines it
  as `ParametricFunctions.versetest:376-378` has it, and its BPVM twin
  (`:4`) is an IR error (3502), not this rule's.
- **Programs.** Over every suite and the corpus `corpus2`, against main
  `dca5ad1` (5,948 programs in both, 3 only in main's, 16 only in this
  branch's): 5,880 the same; the 68 whose code, messages or exit changed
  are listed in each commit: the tests the type-parameter rule rewrote (43 of
  `tests/verse`, their output the same; 2 deleted; 3 error tests), 19 whose
  `branch:` value is an `any` now (their output the same), one whose `()`
  converts to `logic` (`empty_values_nested`, its output the same), the 4
  generated programs of `gadt_function_values` and `gadt_method_instances`
  the rule refuses (the models write the Book's form now, 1,000 seeds each
  agree in Lean, C and the model), and the error test
  `choice_dictionary_write_call_target`, a valid program now; every program
  that never calls `ToDiagnostic` keeps its bytes under it.

## After awaiters inside `Signal`

The Book's rule that a `Signal` resumes its awaiters inside it, in the
order they suspended, each until it waits again or ends, before it returns
(the API's `event`, `Signal`; its tests `Event.versetest:21-32`, the
`FORT-1088027` and `FORT-1126351` cases), built in the lowering and the
concurrency prelude ([the rule, the design and what was built](scheduler-conformance.md#awaiters-run-inside-signal));
with it, `spawn` in a failure context (#156) is allowed, as the tests have
it, and `--event-fifo` is gone. On main `dca5ad1` (#620). Against main's
baseline (8,599 agree, 809 refuse, 69 accept, 87 differ, 3,940 not
translatable), 20 refused cases agree and one Blueprint-only refusal is
accepted: **8,618 agree, 789 refuse, 70 accept, 87 differ, 3,940 not
translatable** (re-recorded from a fresh run).

| Cases | Why they agree now |
|---|---|
| `Bugs/FORT-1088027-MultipleArmsCompleteDuringSpawn.versetest:39`, `FORT-1088027-OldGenerationWakeDuringSpawn.versetest:47`, `FORT-1088027-UseOfNullInitializedDynamicallyTypedValue.versetest` 65, 92, 116, `FORT-1126351-RaceArmSuspendedAfterResolution.versetest:46`, `FORT-1126351-RaceArmsDoNotStartAfterResolution.versetest:33` (7) | awaiters run inside `Signal`, a race resolved there stops its unstarted arms; and `spawn` in an assertion |
| `Event.versetest:54`, `Coroutines/SpawnAndTask.versetest:1027`, and `Bugs/` `2021-03-23-CoroutineOverrideParameterNameMismatch:5`, `FORT-571286-…:51`, `FORT-582630-BranchResult:16`, `FORT-713847-RaceCoerce:12`, `FORT-760026-…:22`, `SOL-3628-SuspendsMethodSuperCall:13`, `SOL-3629-SuspendsMethodEffectSubtype:12`, `SOL-3911-SuspendsArgumentAsForIterable:11`, `SOL-4284-InfiniteLoopTriggersUObjectLimit:18`, `SOL-9691-CaptureSuper:11`, `SamplingProfiler.versetest:25` (13) | `spawn` in an assertion's body (a failure context) |

- **Per cause, on main `dca5ad1` and now:** spawn-in-failure-context 28 →
  0: 20 agree; the 7 `LiveVariables.versetest` cases (450-545) are refused
  now for `await` of a live variable (live-variables, unreleased), and
  `Coroutines/Concurrency.versetest:1537` for `NextTick` (types-other,
  unreleased).
- **The concurrency files** (agree/refuse/accept, before → after):
  `Event.versetest` 0/4/0 → 1/3/0; `Coroutines/SpawnAndTask.versetest`
  5/2/0 → 6/1/0; the five `FORT-1088027`/`FORT-1126351` files above 4/7/0
  → 11/0/0 (their other cases need `CoroUtils`); the generic
  `signalable` ones stay refused (the `signalable` interface); `Coroutines/Concurrency.versetest` 12/1/0,
  `FlowControl/Concurrency/branch.versetest` 4/1/0, `when.versetest`
  7/15/0, `LiveVariables.versetest` 12/44/0 unchanged;
  `SoftwareTransactionalMemory.versetest` 31/0/0 → 30/0/1.
- **Moved the wrong way:** `SoftwareTransactionalMemory.versetest:505`,
  inside `bp_vm_only{…}` ("STM doesn't support spawn, don't allow in
  decides"), refuses a `spawn` in a `<transacts><decides>` function, which
  openverse now accepts. The tests split by virtual machine: the VerseVM's
  (`LiveVariables.versetest:450-545`, `verse_vm_only`) spawn in `if: …;
  false?` and expect success, as every untagged assertion that spawns
  does; openverse follows those. Nothing else is worse, and no case
  changed to a different result.
- **Programs.** Against main `dca5ad1`, over every suite and the corpus
  `corpus2` (5,951 programs): 5,792 the same; 158 programs' bytecode
  changed, each one that uses an event type, 120 of them with the same
  output and 38 with another (the 22 tests and 8 upper-bound fixtures whose
  expected output changed, each re-derived by hand, and 8 corpus programs);
  one error test is accepted now (`choice_refined_spawn_body_failure`, a
  test of the refusal, moved to `tests/verse`).

## Ten causes to remove first

Ranked by cases moved per unit of risk. A count is the upper bound above;
"dangerous" marks a cause whose cases are accepted refusals or different
output, which matter more than their number.

1. **Done since: reserved names (83 accepted refusals; a message; 81 now
   agree).** Refuse as
   definition names the 65 names of `Tests/NamesReservedForFuture.versetest`,
   `_` (which the Book itself reserves), `subtype`, `castable_subtype`,
   `Self` and `local`, in the check that already reports "'X' is defined
   twice". Eight of openverse's own test programs define `first` or
   `repeat` (`tests/verse/clause_macros.verse`, …) and would be renamed.
   Dangerous, and the cheapest item here.
2. **Done since (shadowing across scopes since [After qualified
   names](#after-qualified-names), forward references among constants since
   [the readings audit](#after-the-readings-audit)): one-line checks for the other
   dangerous acceptances (101 accepted refusals and 2 different outputs;
   messages).** Extend "defined twice"
   to classes, structs, enums, interfaces and to a type and a function of
   one name (24, of which the silent first-wins acceptance is the worst);
   refuse module constants that depend on themselves or on a later one, as
   openverse already refuses a field default that does ("the default of
   field 'M' of c41 depends on itself") (4, today a recursion-limit stop at
   run time); refuse a float literal that rounds to infinity (12); refuse
   misplaced specifiers (30), `<final>` misuse (11), redundant effects (9),
   `defer` as a block's value (5); and in the lexer refuse a stray `#>`
   (6) and strip `<#…#>` inside string literals as the Book requires (2
   wrong outputs).
3. **Path literals (213 refusals; a parser form). Done**
   ([After the parser forms](#after-the-parser-forms)): a path is a token
   in expression position; path qualifiers came with qualified names
   ([After qualified names](#after-qualified-names): `(/Verse.org/Verse:)int`
   is `int`, other paths are refused). Left: `import(/…)`.
4. **Empty bodies and empty parentheses (202 refusals; parser forms).
   Done.**
5. **Unnamed parameters (123 refusals; a parser form). Done.**
6. **Character conversions (140 refusals; built-ins). Done** as the API
   reference declares them, methods ([After the library
   functions](#after-the-library-functions)); the free `ToChar(N)` and
   `ToChar32(N)` most of the cases call are declared nowhere.
7. **Block and dot forms (163 refusals; parser forms). Done**, but for
   generators in `first`, which parse and need the elaborator (a lazy
   generator, as `for`'s, stopped at the first success).
8. **Done since: access specifiers (107 accepted refusals; a front-end
   feature).** Enforced as [access-specifiers.md](access-specifiers.md)
   pins them, the documented reading retired; all 107 agree, and 38
   refusals more ([After access specifiers](#after-access-specifiers)).
9. **Done since: bitwise functions (159 refusals; Core and runtime, or
   Verse Core's operations).** Built with Verse Core's operations, 103
   agree and 56 `verse_vm_only` cases differ ([After the Book's
   primitives](#after-the-books-primitives)). As pinned: `BitAnd`, `BitOr`, `BitXor`, `BitNot`, `BitShiftLeft`,
   `BitShiftRight` on `int`, pinned in [the library
   note](book-library-functions.md#bitwise-functions):
   either new primitives next to the nine whose C is proved by QuickProof's
   `arith_exact` and whose Lean seams are in `Core/Seams.lean`, or code over
   the existing ones, as the character conversions are. 84 untagged and 13
   `bp_vm_only` cases could agree; the 62 `verse_vm_only` ones assume
   unbounded integers and would mostly become different results under the
   BPVM reading. The owner's decision.
10. **Attributes (131 refusals; a parser form, then a front-end feature).**
    Parse `@name` and `@name{…}` before a definition and accept the
    built-in ones (`@editable`, `@deprecated`, `@experimental`,
    `@available`) without meaning; custom attributes (`class(attribute)`)
    and their scopes come after.

Next in line (unreachable code, a reachability pass, is done: [After the
load-bearing readings](#after-the-load-bearing-readings)): the `ToDiagnostic` printer (93), and `of`/`at` calls (27, a parser form the
Book's chapters do not describe); type aliases and extension methods are
done ([After the type aliases](#after-the-type-aliases), [After extension
methods](#after-extension-methods)).
The larger semantic item, types as values (198), needs Core work and an
owner's design (`comparable` as a type is built: [After
`comparable`](#after-comparable)); union types (136) and live variables
(50) are VerseVM-only or unreleased. The empty-values equality (30 different
outputs) is dangerous but changes Core equality: it needs an owner
decision first; [the readings audit](readings-audit.md) designs the
readings the tests contradict that it did not change.

## Not covered, and why it matters

- 1,264 cases need the runner's virtual packages and modules (`vpackage`,
  `vmodule`): versioned packages (`?UploadedAtFNVersion`), scopes
  (`InternalAPI`, `PublicAPI`), `@deprecated`/`@experimental` across
  packages, compatibility constraints (`CompatibilityConstraints.versetest`,
  320 cases) and package cycles. openverse's [programs of several
  files](../LANGUAGE.md#programs-of-several-files) could stand in for
  `vmodule` alone; nothing in openverse corresponds to versions and scopes.
- 552 concurrency cases use `CoroUtils` (`Tick`, `WaitTicks`, `LogEvent`),
  the runner's scheduler controls, so `Coroutines/` (229 cases) is measured
  on 25 only; the [scheduler audit](scheduler-conformance.md) remains the
  reference there.
- All 991 `Serialization/` cases, persistence and JSON need the engine.

## Side findings

- [LANGUAGE.md](../LANGUAGE.md#supported)'s Supported table says classes
  have "no `var` fields", while its [Classes](../LANGUAGE.md#classes)
  section lists `var` fields, and the tests' classes with `var` fields
  (`Tests/FlowControl/for.versetest:362`) compile: the table row is stale.
- A snippet ending a class field with `;`
  (`Tests/Attributes/final.versetest:27`, `DataMemberX<final>: int = 0;`)
  made openverse read the next top-level definition as part of the class,
  and report "the program has no Main() function". Fixed with the parser
  forms: a `;` that ends a line does not take the next block's item.

## Rerunning and the guard

```sh
git clone https://github.com/verselang/book ~/book && git -C ~/book checkout beaa719ba165cbf33eff462f2b0fe078a6dd9ab0
lake build && make -C runtime
scripts/book-conformance.sh run ~/book --results /tmp/book.tsv --causes   # totals, causes, per-case TSV
scripts/book-conformance.sh compare ~/book                                # against the baseline
scripts/book-conformance.sh show ~/book Tests/Any.versetest:25            # the program a case becomes
scripts/book-conformance.sh baseline ~/book                               # after an intended change
```

A run takes about a minute with the default eight jobs and needs no
network. `compare` prints every case whose verdict changed: `WORSE` (it
agreed and no longer does, or it became an accepted refusal, a different
output or an internal error), `BETTER` (it agrees now), `CHANGED`, `NEW`
and `GONE`, and exits 1 when any case got worse. The baseline holds
identifiers and verdicts only. `compare` is deliberately not part of
`scripts/check.sh`, which must not need the Book checkout; run it before
landing front-end work. A change of the harness's translation that moves
verdicts is a baseline change of its own, made with `baseline` and
explained in its commit.

## Appendix A: every accepted refusal and different output

Grouped by the causes of the tables above. Lines are given per file, with
`(b)` for `bp_vm_only` and `(v)` for `verse_vm_only` cases.

**Accepted: name-limits** (19): `Bugs/FORT-555217-VeryLongIdentifier.versetest` 25(b), 31(b), 37(b); `Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest` 5(b), 11(b), 67(b), 73(b), 79(b), 85(b), 92(b), 98(b), 154(b), 160(b), 166(b), 172(b), 187(b), 193(b), 199(b), 205(b)

**Accepted: type-checks-other** (12): `Attributes/deprecated.versetest` 435; `Bugs/FORT-744399-DefaultTupleFieldsCrashComplier.versetest` 62; `Bugs/SOL-5838-JoinOfClassesWithCommonBaseClassWithInterfaceInheritance.versetest` 13, 22; `Enum.versetest` 171(b); `FunctionTypes.versetest` 191; `Modules/Using2.versetest` 94; `ParametricFunctions.versetest` 431, 438; `QualifiedIdentifier.versetest` 152; `Void.versetest` 246, 260

**Accepted: epic-limits** (11): `Bugs/FORT-592189-MaybeCoerceToTypeCrash.versetest` 4(b); `Bugs/SOL-5477-CrashInGenClassDefinition.versetest` 5(b); `DefaultNamed.versetest` 629(b), 640(b), 741(b), 751(b); `Function.versetest` 238(b), 271(b); `ParametricFunctions.versetest` 276(b), 496; `Tuple.versetest` 456(b)

**Accepted: concrete-classes** (7): `Attributes/concrete.versetest` 38, 76; `Bugs/SOL-3366-MakeClassesConcreteByDefault.versetest` 8, 15, 24; `Bugs/SOL-7781-ConcreteClassDoesntEnforceDefaultValuesForInterfaceFields.versetest` 28, 54

**Accepted: effect-checks** (6): `Effects.versetest` 490, 551, 552, 557(b), 565(b); `SoftwareTransactionalMemory.versetest` 505(b) ([After awaiters inside `Signal`](#after-awaiters-inside-signal): the BPVM's refusal of `spawn` in a `<decides>` function, which the VerseVM's tests contradict)

**Accepted: initializer-effects** (4): `GlobalVariables.versetest` 86(v), 90(v), 97(v), 105(v)

**Accepted: qualified-names** (4): `Bugs/SOL-3564-CallingSuperClassMethodFromOverriddenMethod.versetest` 7, 18, 32, 45

**Accepted: duplicate-definitions** (1): `QualifiedIdentifier.versetest` 315

**Accepted: final-members** (1): `Attributes/final.versetest` 125

**Accepted: persistable** (1): `persistable.versetest` 59

**Different output: int-precision** (87): `Intrinsics/Abs.versetest` 17(v); `Intrinsics/ToDiagnostic.versetest` 36(v), 37(v), 38(v), 39(v), 40(v); `Math/Bitwise.versetest` 62(v), 63(v), 64(v), 65(v), 66(v), 67(v), 73(v), 76(v), 77(v), 78(v), 79(v), 80(v), 83(v), 84(v), 85(v), 86(v), 87(v), 90(v), 91(v), 92(v), 95(v), 96(v), 97(v), 98(v), 204(v), 205(v), 206(v), 207(v), 208(v), 209(v), 210(v), 215(v), 220(v), 221(v), 222(v), 223(v), 224(v), 229(v), 230(v), 231(v), 232(v), 233(v), 234(v), 235(v), 236(v), 237(v), 238(v), 243(v), 244(v), 245(v), 246(v), 248(v), 249(v), 254(v), 255(v), 256(v); `Operators/BinaryAddInt.versetest` 35(v), 36(v), 37(v), 38(v), 65(v), 66(v), 67(v), 68(v); `Operators/BinaryDivInt.versetest` 49(v), 50(v); `Operators/BinaryMulInt.versetest` 49(v), 50(v), 52(v), 53(v); `Operators/BinarySubInt.versetest` 39(v), 40(v), 41(v), 42(v), 44(v), 45(v), 47(v), 48(v); `Operators/Negate.versetest` 14(v); `WhereConstrainedInts.versetest` 224(v), 227(v)

**Different output: empty-values-equal** (4): `Operators/BoolQuery.versetest` 3, 4; `Operators/LogicalAnd.versetest` 29; `Operators/Precedence.versetest` 121

**Different output: compound-set-order** (1): `ArrayAppend.versetest` 12(v)

## Appendix B: totals per file

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| `Any.versetest` | 83 | 78 | 0 | 2 | 0 | 3 | 0 |
| `ArchetypeAccessSpecifiers.versetest` | 11 | 11 | 0 | 0 | 0 | 0 | 0 |
| `Archetypes.versetest` | 41 | 34 | 0 | 0 | 0 | 7 | 0 |
| `Array.versetest` | 22 | 20 | 0 | 2 | 0 | 0 | 0 |
| `ArrayAppend.versetest` | 27 | 11 | 0 | 10 | 1 | 5 | 0 |
| `AssetUsage/IncrementalAssetUsage.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `AssignmentSequencing.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/AccessLevelInheritance.versetest` | 66 | 64 | 0 | 2 | 0 | 0 | 0 |
| `Attributes/AccessSpecifiersDisallowedOnLocalVars.versetest` | 9 | 9 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/Attributes.versetest` | 34 | 30 | 0 | 2 | 0 | 2 | 0 |
| `Attributes/CustomAttributes.versetest` | 47 | 47 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/CustomClassVarAccessors.versetest` | 61 | 29 | 0 | 3 | 0 | 29 | 0 |
| `Attributes/DeepMutabilityForCustomClassVarAccessors.versetest` | 19 | 1 | 0 | 0 | 0 | 18 | 0 |
| `Attributes/FinalSuperAttribute.versetest` | 25 | 25 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/Internal.versetest` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |
| `Attributes/InvalidAttributeLocations.versetest` | 43 | 43 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/abstract.versetest` | 19 | 19 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/allocates.versetest` | 33 | 32 | 0 | 0 | 0 | 1 | 0 |
| `Attributes/available.versetest` | 77 | 18 | 0 | 2 | 0 | 57 | 0 |
| `Attributes/concrete.versetest` | 44 | 41 | 2 | 1 | 0 | 0 | 0 |
| `Attributes/deprecated.versetest` | 111 | 73 | 1 | 0 | 0 | 37 | 0 |
| `Attributes/experimental.versetest` | 47 | 1 | 0 | 0 | 0 | 46 | 0 |
| `Attributes/export_metadata.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Attributes/final.versetest` | 22 | 21 | 1 | 0 | 0 | 0 | 0 |
| `Attributes/intrinsic.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/native.versetest` | 20 | 1 | 0 | 0 | 0 | 19 | 0 |
| `Attributes/override.versetest` | 16 | 16 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/scoped.versetest` | 51 | 33 | 0 | 0 | 0 | 18 | 0 |
| `Attributes/unique.versetest` | 34 | 25 | 0 | 0 | 0 | 9 | 0 |
| `AutoQualification.versetest` | 29 | 0 | 0 | 0 | 0 | 29 | 0 |
| `BigArray.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-16-ForLoopIteratorVarScoping.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-21-CallMethodOnOptionalMember.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-21-DataMemberAttributeUseAfterFree.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-21-PassOptionalMemberAsNonOptional.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-22-ThreeDuplicateDefinitions.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-24-ArrayConcatIntoItself.versetest` | 5 | 4 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/2020-04-24-AssignForIf.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-24-AssignmentOfVariableCrash.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-27-IndexOpPostfixedToMethodCall.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-27-NotAssigningReturnedArray.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-28-CompareEnumMemberToNonMember.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-29-LoopLocalCompositionSize.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-05-11-InferredTypeMisinterpretedAsEnumContext.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-06-10-CallCoroWithinStdMethod.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-06-18-DefaultClassValues.versetest` | 3 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/2020-06-18-DefaultObjectValues.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-06-18-RushReturnValForImmediateCoros.versetest` | 2 | 0 | 0 | 1 | 0 | 1 | 0 |
| `Bugs/2020-06-22-CoroutineInClassImplementingInterface.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/2020-07-31-UnaryTypeSpecOnLeftHandSideOfEquals.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/2020-08-05-NoMethodBody.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-08-05-UnusedArchetypeUseAfterFree.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-08-11-TypeSpecVsComparePrecedence.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-09-01-EmitReturnAssert.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-10-26-DefineLocalWithMutatingAssignment.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-03-23-CoroutineOverrideParameterNameMismatch.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-03-23-InterfaceDefaultCoroutineImplementation.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/2021-04-26-DisjointTypesAllowedInComparisonAndPointerDeref.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-08-18-DisjointResultInNestedIf.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-08-23-struct_in_struct_sol-1986.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-08-26-UsingFunctionAsTypeInItsOwnDefinition.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-08-31-ConcatenatingArraysOfStrings.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-09-03-ConcatEqualsAssertionFailure.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-09-03-OptionalTupleAssertionFailure.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-09-03-UniquePointerInitializerTypeErrorAssertionFailure.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-10-05-AttributeNames.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2022-01-18-TupleCorruption.versetest` | 2 | 1 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/2022-02-24-AssignmentToUnknownIdentifierAssert.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2022-05-09-InfiniteParserLoop.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2022-09-19-PackageScopesSetIncorrectly.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/2022-10-25-EmptyStringAsMapKeyAssert.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2022-11-16-CommentSigIndent.versetest` | 11 | 11 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2022-11-30-ParserFuzzingBugs.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2022-12-08-LocalParametricFunction.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-17-CharLiteralAsOperand.versetest` | 4 | 0 | 0 | 4 | 0 | 0 | 0 |
| `Bugs/2023-01-17-ClassWithAttributeOnRhsOfInvalidDefinition.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-17-ForAsType.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-17-FunctionReturnTypeReferencesSelf.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-17-PointerDereferenceInType.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-18-ArchetypeFieldNameIsNotIdentifier.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-18-ClosedWorldFunctionBodyReferencesItself.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-18-DeeplyNestedPrefixColon.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-18-DefinitionAsMacroName.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-18-FunctionParameterWithoutDomain.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-18-VarTypeReferencesItself.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-19-AmbiguousCallToOverloadedFunctionInReturnType.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-19-ControlKeywordAsPrefixOrPostfixOperand.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-01-19-FunctionDefinitionInFunctionReturnType.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-02-CommentBeforeInfixMultiplicationOperator.versetest` | 28 | 28 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-03-ClauseContainingOnlyComment.versetest` | 12 | 12 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-03-DataDefinitionAsSubexpressionOfErroneousInvocation.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-03-ExponentialTimeRecursionCheck.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-03-PrintingCyclicFlowTypeForError.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-07-InvalidClassInstantiationClauseContainingDataDefinition.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-07-UnusedMapCoercion.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-08-MapMemoryLeak.versetest` | 12 | 11 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/2023-02-20-UseAfterFreeWhenCoercingNestedStructsToDynamicallyTypedValue.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-22-NullDereferenceInResolveIdentifier.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-03-24-OverloadedFunctionMustBeInvoked.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-04-28-IncorrectNameMangling.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2024-12-02-VerseVMPropertyGeneratorGetOrCreateTupleTypeCrash.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2026-01-26-FindFirstAsyncSubExprMissingOverrides.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/ArrayClassOf.versetest` | 2 | 1 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/ArrayOrFailureResult.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/AssignmentToWhile.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/AttributeOnSameLineAsDefinition.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/BPVMOnly/AsyncContextCancellation.versetest` | 8 | 0 | 0 | 0 | 0 | 8 | 0 |
| `Bugs/BPVMOnly/CancelledArmDefers.versetest` | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| `Bugs/BPVMOnly/LeftoverArmDeferTiming.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/BPVMOnly/NestedUpdateStateCorruption.versetest` | 6 | 0 | 0 | 0 | 0 | 6 | 0 |
| `Bugs/BPVMOnly/RaceCompletionTiming.versetest` | 6 | 0 | 0 | 0 | 0 | 6 | 0 |
| `Bugs/BPVMOnly/RefinedMapKeyInterfaceOverride.versetest` | 10 | 7 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/BlockWithAssignmentShouldNotCrash.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/Braces.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/DigestInheritedCallbackParametricSubscribe.versetest` | 5 | 0 | 0 | 0 | 0 | 5 | 0 |
| `Bugs/FORT-1006008-ResolveAmbiguityAwayFromInternalAPI.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-1017224-ReadsEffectAllowedInComputesClassOrInterfaceDefaultExpressions.versetest` | 11 | 0 | 0 | 0 | 0 | 11 | 0 |
| `Bugs/FORT-1033995-ReinstancingCrashInForEachSubobject.versetest` | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| `Bugs/FORT-1042316-GetInstancedSubobjectOverwritesASubobjectWithItself.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-1054384-Void-Any-Meet.versetest` | 3 | 2 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/FORT-1059276.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-1088027-MultipleArmsCompleteDuringSpawn.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-1088027-OldGenerationWakeDuringSpawn.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-1088027-UseOfNullInitializedDynamicallyTypedValue.versetest` | 5 | 3 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-1126351-GenericSignalableDeferredSignalConvertCrash.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-1126351-GenericSignalableReentrantConvertCrash.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-1126351-RaceArmSuspendedAfterResolution.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-1126351-RaceArmsDoNotStartAfterResolution.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-1126351_cross_event_reentrancy_probe.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/FORT-1126351_object_payload_reentrancy_probe.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-1126351_reentrant_signal_probe.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/FORT-1146499-GeneratedAssetNameConflicts.versetest` | 11 | 0 | 0 | 0 | 0 | 11 | 0 |
| `Bugs/FORT-555213-DontSignedInt32OverflowInArrayBytes.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-555217-VeryLongIdentifier.versetest` | 6 | 3 | 3 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-559416-AddExtensionMethodsToForgotUsingMessage.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-571286-CrashMisinterpretingUObjectPointerAsDynamicallyTypedValue.versetest` | 8 | 5 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/FORT-574089-SucceedsConstructorFallibleArgument.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-581999-ErrorNodeInIrGenerator.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-582128-PathLiteralAsValue.versetest` | 12 | 11 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-582129-VariableTypeReferencesVariableName.versetest` | 21 | 21 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-582630-BranchResult.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-583815-SelfCancellation.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-585106-WriteLogicCauseCompilerToAssert.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-586526-PrematureRuntimeTypePurge.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-590869-NamedWithDefaultCoercion.versetest` | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/FORT-592189-MaybeCoerceToTypeCrash.versetest` | 2 | 1 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-623803-STMRollbackAfterReturn.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-635190-AssertIndexingContainerAfterRuntimeError.versetest` | 16 | 0 | 0 | 0 | 0 | 16 | 0 |
| `Bugs/FORT-642876-CollidingCoercedOverrideNames.versetest` | 11 | 0 | 0 | 11 | 0 | 0 | 0 |
| `Bugs/FORT-687100-Mix-comma-and-semicolon-in-archetype-instantiation.versetest` | 9 | 7 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-713493-CaseTypeError.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-713847-RaceCoerce.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-720968-DetectInaccessibleTypesAcrossPackagesWithDifferentUploadedAtVersions.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Bugs/FORT-721882-CallingFunctionWithNullObject.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/FORT-722788-LookupBindingDataOfFunctionInModulePart.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-734038-CrashAfterReportingAnErrorRelatedToNamedParameters.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-741838-SuccessFailureParametricTypes.versetest` | 5 | 0 | 0 | 5 | 0 | 0 | 0 |
| `Bugs/FORT-743839-SetMapWithIfExpr.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-744399-DefaultTupleFieldsCrashComplier.versetest` | 11 | 10 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-746888-CodegenGeneratesDuplicateLocalPropertyNames.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-760026-NonUniquePropertyNamesInSuspendsFunction.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-763813-CrashIfClassInheritFromStruct.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-779650-LocalVarCompoundAssignmentRollbackMemoryCorruption.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-779858-CrashDeltaSerializingAgainstUninitializedDynamicallyTypedValue.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest` | 47 | 14 | 16 | 0 | 0 | 17 | 0 |
| `Bugs/FORT-861412-ImprovedErrorMessage.versetest` | 8 | 2 | 0 | 0 | 0 | 6 | 0 |
| `Bugs/FORT-889314-InterfaceFieldOverriddenWithGetterSetterBroken.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-951162-CantQualifyPropertiesOfParametricClasses.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-976754-GetterSetter.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-987013-MissingUploadedAtFNVersion.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-995029-CrashHashingDynamicallyTypedMapKey.versetest` | 3 | 1 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FunctionWithoutExclamationPoint.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/IteratingOverDataMemberArray.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/LogicalNot.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/ParameterCountCrash.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1729-MakeAttributesForwardCompatible.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1736-AssertionFailuresWithArrayConcatenation.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1758-LoopUsesResultOfLastSubexpression.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1830-LocalVariablesCanEscape.versetest` | 20 | 20 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1924-RaceDeferSynchronization.versetest` | 10 | 0 | 0 | 0 | 0 | 10 | 0 |
| `Bugs/SOL-1928-CallMethodOnResultOfCallToUndefinedFunction.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1957-InterfaceMethodReturningStructAssert.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1987-IfDoesNotDetectNestedConditional.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-2270-ExtensionalFloats.versetest` | 73 | 73 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-2336-LoopReturn.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-2577-ConstructorOverloadAmbiguity.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-2584-AbstractFunctionInModule.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-2620-AssignmentWithoutElement.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-2731-InvocationStructContext.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-2957-NullableObjectLocal.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3059-HeapBufferOverflowBugInArrayConcatenation.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3104-IncorrectFunctionQualificationCrashCompiler.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3250-AssertionFailureWhenOverridingTheSameFunctionTwice.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3293-ConstructingAnInstanceWhileInitializingItsDefaults.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3300-IncorrectCloningOfUniqueObject.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3366-MakeClassesConcreteByDefault.versetest` | 7 | 4 | 3 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3422-CyclicInterfacesAndClasses.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3515-CallingExtensionMethodWithoutSelf.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3563-DontStackOverflowOnCyclicInterfaces.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3564-CallingSuperClassMethodFromOverriddenMethod.versetest` | 16 | 8 | 4 | 4 | 0 | 0 | 0 |
| `Bugs/SOL-3628-SuspendsMethodSuperCall.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3629-SuspendsMethodEffectSubtype.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3662-LineCommentEndsIndentedBlock.versetest` | 7 | 6 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-3729-UnidentifiedIdentInCaseCondition.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3731-CoercionOfParametricFieldOverrides.versetest` | 5 | 2 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/SOL-3732-PartialModuleParametricClassAssert.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-3734-UnicodeCausesCompilerErrors.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3793-StackingSuperQualifiers.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3799-AddToMembersWhileIteratingOverThem.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-3819-DefinitionsInTypeSpecifiers.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3825-IsComparableShouldHandleCycles.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3887-MessageArray.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3911-SuspendsArgumentAsForIterable.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4107-StmWritesPoppedLocalVar.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4137-MemoryLeakCreatingA3dArray.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4170-DefinitionAstNodeUseAfterFree.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4171-CallStackOverflow.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4194-AssertOnMalformedCaseContainingDataDefinition.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4196-ErrCauseEnsureFailure.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4199-BreakFromIf.versetest` | 10 | 9 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-4204-MapPartialWrite.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4208-OverrideWithVar.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4209-SuspendingSubexpressionsOfSpawnedInvocation.versetest` | 6 | 3 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/SOL-4266-RaceContinuationExecution.versetest` | 5 | 0 | 0 | 0 | 0 | 5 | 0 |
| `Bugs/SOL-4284-InfiniteLoopTriggersUObjectLimit.versetest` | 3 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-4289-SyncUninitializedLocalArray.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Bugs/SOL-4332-BranchRace.versetest` | 10 | 0 | 0 | 0 | 0 | 10 | 0 |
| `Bugs/SOL-4339-CallingConstructorsForUStructs.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/SOL-4357-TypeType.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4389-VerseTypeInitializationDoesNotProperlyHandleInitializationOverrides.versetest` | 19 | 0 | 0 | 0 | 0 | 19 | 0 |
| `Bugs/SOL-4527-CoercedInterfaceOverride.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5386-CrashUsingSuperToCallOverrideInParametricClass.versetest` | 5 | 3 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-5452-NullDereferenceAfterRuntimeError.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-5477-CrashInGenClassDefinition.versetest` | 2 | 1 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5496-CaseCodeBlocksWithoutScopes.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5551-UsingTypeAlias.versetest.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5564-PublicOverrideOfDefinitionInNonPublicScope.versetest` | 3 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-5706-CompilerCrashWhenUsingSyncExpressionInCertainCircumstances.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5777-AutoRTFMForLoopCrash.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5838-JoinOfClassesWithCommonBaseClassWithInterfaceInheritance.versetest` | 4 | 2 | 2 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5880-CrashOnArchetypeWithMixedCommasAndSemicolons.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-5951-AssertOnForAsArchetypeConstructionSubexpression.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5982-ConcatEqualsAndTransactions.versetest` | 10 | 10 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5983-TypeSystemEscapeUsingFalse.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-6109-OverloadedFunctionNotUsed.versetest` | 3 | 2 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-6116-DiamondInheritance.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-6137-ConcurrencyMacrosNotIntroducingScope.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-6177-SubtypingIgnoresInheritedMembers.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-6529-WarnAboutAlwaysFailingContainerLookups.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-6739-ParametricTypeMeetAndJoin.versetest` | 25 | 19 | 0 | 6 | 0 | 0 | 0 |
| `Bugs/SOL-6934-OptionTypeIgnoresHashabilityOfValue.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-6945-JoinOfTupleOfNamedElementsAndArray.versetest` | 8 | 6 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-7017-AvailableAttributeOnlyUsesDefinitionPackageVersion.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Bugs/SOL-7079-IllegalQualifiedName.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-7157-CoercingRationalToAny.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-7231-NamedParameterMeet.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-7388-TaskGroupCorruption.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-7459-OverridingAnInterfaceVariableWithANativeVariableIsNotSupported.versetest` | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| `Bugs/SOL-7475-dynamic-casting-through-CTypeVariable.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-7503-ProblemWithQualification.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Bugs/SOL-7523-NoEnsureAfterGlitchForIncorrectDynamicCast.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-7549-QualifiedNamesNeedQualifiedParameterTypes.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-7578-OverrideOfFinalParametricFields.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-7579-LocalQualifierIsAllowedForMethodsInParametricClass.versetest` | 3 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-7778_EnumeratorsAliasingReservedWords.versetest` | 24 | 5 | 0 | 0 | 0 | 19 | 0 |
| `Bugs/SOL-7781-ConcreteClassDoesntEnforceDefaultValuesForInterfaceFields.versetest` | 7 | 4 | 2 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-7849-CannotAccessDataFieldsInParametricInterfaces.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-7898-DisambiguateSuperTypesByAccess.versetest` | 18 | 18 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-8109-ParserStackOverflow.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-8137-AttributeLocalizesIsNotAllowedOnLocalVariables.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/SOL-8267-InterfaceDefaultsAreNotReinstantiated.versetest` | 6 | 2 | 0 | 0 | 0 | 4 | 0 |
| `Bugs/SOL-8302-CastableSubtypeFailsWithInterfaces.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-8380-InterfaceAccessorsNativeFailed.versetest` | 5 | 0 | 0 | 0 | 0 | 5 | 0 |
| `Bugs/SOL-8527-DefaultInitializerGlobalObject.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-8557-InitializeVarMissesDefDest.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-8558-RequireConcreteForNativeSetter.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-8627-concrete_subtype-effects.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-8722-InterfaceConstructionEffectLeak.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-8768-QualificationOfExtensionFields.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-8814-OverrideOfExperimentalDefinitionIsNotUseOfExperimental.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Bugs/SOL-8836-RepeatedInstantiation.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-8891-StringNativeConversion.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-8918-PartialModuleModuleLevelFunctionFailure.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-9061-DocCommentsOnQualifiedIdentifiers.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-9192-DigestSourceOrder.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-9661-ForLoopWithNonGeneratorDomain.versetest` | 9 | 9 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-9691-CaptureSuper.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-9694-ReturnFromLoopInBranch.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-9745-ConcreteClassOverridingInterfaceDataMember.versetest` | 15 | 15 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-9799-CaptureLocalUsing.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/TwoMethodsWithSameName.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/TypeFormerAsExpression.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/TypeSpecOnUnnamedParameter.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/UE-234933-InterfaceIssues.versetest` | 5 | 2 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/UpcastDataMemberAccess.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/VariableShadowing.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Bytecode/Arithmetic.versetest` | 14 | 0 | 0 | 0 | 0 | 14 | 0 |
| `Bytecode/Arrays.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bytecode/Bytecode.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bytecode/Classes.versetest` | 3 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Bytecode/ControlFlow.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bytecode/Functions.versetest` | 2 | 1 | 0 | 0 | 0 | 1 | 0 |
| `Bytecode/Maps.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bytecode/StringsAndTuples.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `CanCallerAccessEpicInternal/Async.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `CanCallerAccessEpicInternal/Basic.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `CanCallerAccessEpicInternal/Native.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `CanCallerAccessEpicInternal/NativeCallback.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `CanCallerAccessEpicInternal/Spawn.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `CanCallerAccessEpicInternal/SpawnRoot.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Cast.versetest` | 65 | 64 | 0 | 1 | 0 | 0 | 0 |
| `Castable.versetest` | 101 | 74 | 0 | 9 | 0 | 18 | 0 |
| `Classes/AccessSpecifiers.versetest` | 61 | 48 | 0 | 0 | 0 | 13 | 0 |
| `Classes/Class.versetest` | 42 | 42 | 0 | 0 | 0 | 0 | 0 |
| `Classes/ClassBlockClause.versetest` | 24 | 17 | 0 | 0 | 0 | 7 | 0 |
| `Classes/Constructor.versetest` | 61 | 16 | 0 | 6 | 0 | 39 | 0 |
| `Classes/DataInheritence.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Classes/IdentifierSuper.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Classes/Inheritance.versetest` | 11 | 10 | 0 | 1 | 0 | 0 | 0 |
| `Classes/MethodInheritance.versetest` | 9 | 1 | 0 | 0 | 0 | 8 | 0 |
| `Classes/QualifiedMethodInheritance.versetest` | 23 | 21 | 0 | 0 | 0 | 2 | 0 |
| `Classes/SelfInheritance.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Classes/Struct.versetest` | 77 | 67 | 0 | 0 | 0 | 10 | 0 |
| `Classes/VarPointingToClass.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `ClassifiableSubset.versetest` | 36 | 9 | 0 | 27 | 0 | 0 | 0 |
| `CoercedOverrides.versetest` | 10 | 3 | 0 | 4 | 0 | 3 | 0 |
| `Comparable.versetest` | 49 | 48 | 0 | 1 | 0 | 0 | 0 |
| `ComparableInterface.versetest` | 17 | 13 | 0 | 4 | 0 | 0 | 0 |
| `CompatibilityConstraints.versetest` | 320 | 0 | 0 | 0 | 0 | 320 | 0 |
| `ComputationLimit.versetest` | 3 | 2 | 0 | 0 | 0 | 1 | 0 |
| `Coroutines/Concurrency.versetest` | 86 | 12 | 0 | 1 | 0 | 73 | 0 |
| `Coroutines/ConcurrencyEscape.versetest` | 49 | 0 | 0 | 0 | 0 | 49 | 0 |
| `Coroutines/Flow.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Coroutines/IteratedPrimitives.versetest` | 6 | 4 | 0 | 0 | 0 | 2 | 0 |
| `Coroutines/Loop.versetest` | 3 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Coroutines/ParamAlignment.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Coroutines/SelfCancel.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Coroutines/SpawnAndTask.versetest` | 77 | 6 | 0 | 1 | 0 | 70 | 0 |
| `CyclicReferences.versetest` | 13 | 13 | 0 | 0 | 0 | 0 | 0 |
| `DataMemberValidation.versetest` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |
| `DebugStackTrace/FrameOrder.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DebugStackTrace/Recursion.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DebugStackTrace/Spawn.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DebugStackTrace/When.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DefaultNamed.versetest` | 142 | 128 | 4 | 0 | 0 | 10 | 0 |
| `Definitions.versetest` | 16 | 15 | 0 | 1 | 0 | 0 | 0 |
| `DigestGeneration.versetest` | 43 | 1 | 0 | 0 | 0 | 42 | 0 |
| `DigestVisibility.versetest` | 47 | 31 | 0 | 0 | 0 | 16 | 0 |
| `Duplication.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `DynamicallyTypedSubobjectInstantiation.versetest` | 16 | 16 | 0 | 0 | 0 | 0 | 0 |
| `Effects.versetest` | 336 | 262 | 5 | 2 | 0 | 67 | 0 |
| `Enum.versetest` | 71 | 66 | 1 | 0 | 0 | 4 | 0 |
| `EnumCompare.versetest` | 12 | 12 | 0 | 0 | 0 | 0 | 0 |
| `Escape.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `EvaluationOrder.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Event.versetest` | 6 | 1 | 0 | 3 | 0 | 2 | 0 |
| `EventShouldBeCallable.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Exercises/BalancedBinaryTree.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/BinaryTreeInorderTraversalRecursive.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/EpicProgrammingAssessmentBinarySearch.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/SameTree.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/TwoSum.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `ExtensionFields.versetest` | 39 | 37 | 0 | 0 | 0 | 2 | 0 |
| `Failure.versetest` | 34 | 31 | 0 | 0 | 0 | 3 | 0 |
| `Features/DefaultValueAssignment.versetest` | 67 | 21 | 0 | 1 | 0 | 45 | 0 |
| `FlowControl/Break.versetest` | 17 | 17 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/Case.versetest` | 71 | 70 | 0 | 0 | 0 | 1 | 0 |
| `FlowControl/Concurrency/branch.versetest` | 10 | 4 | 0 | 1 | 0 | 5 | 0 |
| `FlowControl/Continue.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/If.versetest` | 94 | 94 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/IfDecidesErrors.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/Reachability.versetest` | 25 | 25 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/Return.versetest` | 86 | 84 | 0 | 1 | 0 | 1 | 0 |
| `FlowControl/Yield.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/defer.versetest` | 51 | 13 | 0 | 1 | 0 | 37 | 0 |
| `FlowControl/first.versetest` | 24 | 20 | 0 | 3 | 0 | 1 | 0 |
| `FlowControl/for.versetest` | 94 | 93 | 0 | 1 | 0 | 0 | 0 |
| `Function.versetest` | 81 | 61 | 2 | 1 | 0 | 17 | 0 |
| `FunctionAsType.versetest` | 36 | 17 | 0 | 15 | 0 | 4 | 0 |
| `FunctionTypes.versetest` | 42 | 32 | 1 | 9 | 0 | 0 | 0 |
| `GenerateFunctionForParametricClass.versetest` | 2 | 1 | 0 | 0 | 0 | 1 | 0 |
| `GenerateFunctionForParametricInterface.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `GetCastableFinalSuperClass.versetest` | 94 | 94 | 0 | 0 | 0 | 0 | 0 |
| `GetSecondsSinceEpoch.versetest` | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
| `GlobalVariables.versetest` | 26 | 17 | 4 | 4 | 0 | 1 | 0 |
| `Incremental/01_null_compile.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Incremental/02_leaf_body_change.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Incremental/03_leaf_interface_change.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Incremental/05_shared_dep_interface_change.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Incremental/07_fingerprint_determinism.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Incremental/08_used_assets_stable.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Incremental/09_diagnostics_replayed.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Incremental/10_statistics_replayed.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `IndistinctOverloads.versetest` | 20 | 20 | 0 | 0 | 0 | 0 | 0 |
| `IntAsRational.versetest` | 14 | 14 | 0 | 0 | 0 | 0 | 0 |
| `Interface.versetest` | 109 | 101 | 0 | 5 | 0 | 3 | 0 |
| `InterfaceAccessVisibility.versetest` | 19 | 12 | 0 | 0 | 0 | 7 | 0 |
| `InterfaceDiamond.versetest` | 18 | 18 | 0 | 0 | 0 | 0 | 0 |
| `InterfaceWithAccessors.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `InterfaceWithFields.versetest` | 37 | 29 | 0 | 7 | 0 | 1 | 0 |
| `Interfaces/AccessSpecifiers.versetest` | 41 | 34 | 0 | 0 | 0 | 7 | 0 |
| `Intrinsics/Abs.versetest` | 19 | 16 | 0 | 0 | 1 | 2 | 0 |
| `Intrinsics/ArrayFind.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayInsert.versetest` | 18 | 18 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayLength.versetest` | 14 | 14 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemove.versetest` | 26 | 26 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemoveAllElements.versetest` | 10 | 10 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemoveElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemoveFirstElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceAll.versetest` | 13 | 12 | 0 | 1 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceAllElements.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceFirstElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArraySlice.versetest` | 61 | 61 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/CharConversionExtensionMethods.versetest` | 15 | 15 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/CharToString.versetest` | 10 | 10 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/Concatenate.versetest` | 25 | 25 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ConcatenateMaps.versetest` | 29 | 27 | 0 | 2 | 0 | 0 | 0 |
| `Intrinsics/Err.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/FloatToString.versetest` | 12 | 10 | 0 | 0 | 0 | 2 | 0 |
| `Intrinsics/IntToString.versetest` | 11 | 11 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/MapLength.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/StringLength.versetest` | 16 | 16 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/StringToString.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ToDiagnostic.versetest` | 114 | 62 | 0 | 14 | 5 | 33 | 0 |
| `LengthOptimizationSafety.versetest` | 8 | 5 | 0 | 0 | 0 | 3 | 0 |
| `LenientClassConstruction.versetest` | 8 | 4 | 0 | 0 | 0 | 4 | 0 |
| `Literals/Char.versetest` | 184 | 39 | 0 | 0 | 0 | 145 | 0 |
| `Literals/Float.versetest` | 176 | 142 | 0 | 0 | 0 | 34 | 0 |
| `Literals/Function.versetest` | 22 | 22 | 0 | 0 | 0 | 0 | 0 |
| `Literals/Int.versetest` | 166 | 166 | 0 | 0 | 0 | 0 | 0 |
| `Literals/Logic.versetest` | 36 | 34 | 0 | 2 | 0 | 0 | 0 |
| `Literals/Path.versetest` | 237 | 237 | 0 | 0 | 0 | 0 | 0 |
| `Literals/String.versetest` | 199 | 195 | 0 | 4 | 0 | 0 | 0 |
| `LiveVariables.versetest` | 56 | 12 | 0 | 44 | 0 | 0 | 0 |
| `Localization.versetest` | 40 | 40 | 0 | 0 | 0 | 0 | 0 |
| `LocalizationJoin.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `MacroForms.versetest` | 17 | 17 | 0 | 0 | 0 | 0 | 0 |
| `ManyEmergentTypes.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Map.versetest` | 104 | 100 | 0 | 4 | 0 | 0 | 0 |
| `MapOrder.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Math/Bitwise.versetest` | 174 | 114 | 0 | 0 | 56 | 4 | 0 |
| `Math/Math.versetest` | 77 | 77 | 0 | 0 | 0 | 0 | 0 |
| `Math/MaxFloat.versetest` | 22 | 22 | 0 | 0 | 0 | 0 | 0 |
| `Math/MaxInt.versetest` | 13 | 13 | 0 | 0 | 0 | 0 | 0 |
| `Math/MinFloat.versetest` | 22 | 22 | 0 | 0 | 0 | 0 | 0 |
| `Math/MinInt.versetest` | 13 | 13 | 0 | 0 | 0 | 0 | 0 |
| `MetatypeConcreteSubtype.versetest` | 38 | 35 | 0 | 3 | 0 | 0 | 0 |
| `Modules/AccessSpecifiers.versetest` | 34 | 0 | 0 | 0 | 0 | 34 | 0 |
| `Modules/AssetAccessibility.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Modules/Import.versetest` | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| `Modules/Module.versetest` | 58 | 40 | 0 | 2 | 0 | 16 | 0 |
| `Modules/ModuleDefinitions.versetest` | 62 | 25 | 0 | 1 | 0 | 36 | 0 |
| `Modules/ModuleScopedInstances.versetest` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |
| `Modules/PartialModuleDefinitions.versetest` | 14 | 2 | 0 | 5 | 0 | 7 | 0 |
| `Modules/Using.versetest` | 22 | 1 | 0 | 0 | 0 | 21 | 0 |
| `Modules/Using2.versetest` | 9 | 5 | 1 | 0 | 0 | 3 | 0 |
| `Mutability.versetest` | 55 | 54 | 0 | 1 | 0 | 0 | 0 |
| `NamedParameterOverloads.versetest` | 36 | 36 | 0 | 0 | 0 | 0 | 0 |
| `NamedParamsFromNative.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `NamesReservedForFuture.versetest` | 69 | 69 | 0 | 0 | 0 | 0 | 0 |
| `NativeDeepMutability.versetest` | 19 | 0 | 0 | 0 | 0 | 19 | 0 |
| `NativePropertyRequiresNativeClass.versetest` | 6 | 0 | 0 | 0 | 0 | 6 | 0 |
| `NativePropertyRollback.versetest` | 15 | 1 | 0 | 0 | 0 | 14 | 0 |
| `NativePropertyWriteHook.versetest` | 10 | 0 | 0 | 0 | 0 | 10 | 0 |
| `NestedArrays.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `NestedFunctions.versetest` | 32 | 13 | 0 | 17 | 0 | 2 | 0 |
| `NestedNamedTupleParameters.versetest` | 24 | 9 | 0 | 7 | 0 | 8 | 0 |
| `NestedObjects.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `NestedTupleParameters.versetest` | 16 | 7 | 0 | 0 | 0 | 9 | 0 |
| `ObjectToJson.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Operators/Associativity.versetest` | 16 | 16 | 0 | 0 | 0 | 0 | 0 |
| `Operators/At.versetest` | 15 | 15 | 0 | 0 | 0 | 0 | 0 |
| `Operators/BinaryAddArray.versetest` | 14 | 14 | 0 | 0 | 0 | 0 | 0 |
| `Operators/BinaryAddFloat.versetest` | 36 | 22 | 0 | 0 | 0 | 14 | 0 |
| `Operators/BinaryAddInt.versetest` | 43 | 33 | 0 | 0 | 8 | 2 | 0 |
| `Operators/BinaryAddString.versetest` | 16 | 16 | 0 | 0 | 0 | 0 | 0 |
| `Operators/BinaryArrow.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Operators/BinaryDivFloat.versetest` | 88 | 70 | 0 | 0 | 0 | 18 | 0 |
| `Operators/BinaryDivInt.versetest` | 34 | 32 | 0 | 0 | 2 | 0 | 0 |
| `Operators/BinaryMulFloat.versetest` | 48 | 33 | 0 | 0 | 0 | 15 | 0 |
| `Operators/BinaryMulInt.versetest` | 32 | 28 | 0 | 0 | 4 | 0 | 0 |
| `Operators/BinaryOps.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Operators/BinarySubFloat.versetest` | 26 | 12 | 0 | 0 | 0 | 14 | 0 |
| `Operators/BinarySubInt.versetest` | 28 | 20 | 0 | 0 | 8 | 0 | 0 |
| `Operators/BoolQuery.versetest` | 5 | 3 | 0 | 0 | 2 | 0 | 0 |
| `Operators/CompareArray.versetest` | 30 | 30 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareBool.versetest` | 18 | 18 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareFloat.versetest` | 52 | 50 | 0 | 0 | 0 | 2 | 0 |
| `Operators/CompareInstance.versetest` | 18 | 18 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareInt.versetest` | 36 | 36 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareMap.versetest` | 97 | 97 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareOption.versetest` | 18 | 18 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareRational.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareString.versetest` | 148 | 148 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareStruct.versetest` | 36 | 32 | 0 | 0 | 0 | 4 | 0 |
| `Operators/CompareTuple.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Operators/CompareTypeChecking.versetest` | 39 | 39 | 0 | 0 | 0 | 0 | 0 |
| `Operators/DisallowedOperatorDefinitions.versetest` | 30 | 30 | 0 | 0 | 0 | 0 | 0 |
| `Operators/LogicalAnd.versetest` | 9 | 8 | 0 | 0 | 1 | 0 | 0 |
| `Operators/LogicalNot.versetest` | 11 | 11 | 0 | 0 | 0 | 0 | 0 |
| `Operators/LogicalOr.versetest` | 90 | 90 | 0 | 0 | 0 | 0 | 0 |
| `Operators/Negate.versetest` | 6 | 5 | 0 | 0 | 1 | 0 | 0 |
| `Operators/Of.versetest` | 15 | 15 | 0 | 0 | 0 | 0 | 0 |
| `Operators/PostAt.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Operators/PostfixCallArray.versetest` | 16 | 14 | 0 | 0 | 0 | 2 | 0 |
| `Operators/PostfixCallMap.versetest` | 31 | 31 | 0 | 0 | 0 | 0 | 0 |
| `Operators/PostfixCallString.versetest` | 22 | 22 | 0 | 0 | 0 | 0 | 0 |
| `Operators/Precedence.versetest` | 68 | 67 | 0 | 0 | 1 | 0 | 0 |
| `Operators/PrefixStar.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Option.versetest` | 63 | 63 | 0 | 0 | 0 | 0 | 0 |
| `OutOfScopeOverloads.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Overloading.versetest` | 79 | 64 | 0 | 9 | 0 | 6 | 0 |
| `PackageCycles.versetest` | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| `ParametricCastingIsDisallowed.versetest` | 11 | 10 | 0 | 1 | 0 | 0 | 0 |
| `ParametricFunctions.versetest` | 106 | 82 | 4 | 16 | 0 | 4 | 0 |
| `ParametricTypes.versetest` | 274 | 207 | 0 | 40 | 0 | 27 | 0 |
| `Parentheses.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `Path.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `PersistentJson.versetest` | 103 | 1 | 0 | 0 | 0 | 102 | 0 |
| `PersistentJsonSnapshot.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `PersistentJsonSnapshotMacro.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `PersonaJson.versetest` | 102 | 0 | 0 | 0 | 0 | 102 | 0 |
| `Placeholder.versetest` | 9 | 9 | 0 | 0 | 0 | 0 | 0 |
| `Pointers.versetest` | 66 | 64 | 0 | 2 | 0 | 0 | 0 |
| `PrintScriptCallstack.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `QualifiedIdentifier.versetest` | 88 | 54 | 2 | 0 | 0 | 32 | 0 |
| `Range.versetest` | 39 | 39 | 0 | 0 | 0 | 0 | 0 |
| `Rational.versetest` | 49 | 48 | 0 | 0 | 0 | 1 | 0 |
| `Recursion.versetest` | 47 | 47 | 0 | 0 | 0 | 0 | 0 |
| `ReentrantExceptions.versetest` | 3 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Reference.versetest` | 4 | 1 | 0 | 0 | 0 | 3 | 0 |
| `ReserveDotSpace.versetest` | 14 | 14 | 0 | 0 | 0 | 0 | 0 |
| `ResolvingIdentifiers.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `RetryTransactionUnderAutoRTFM.versetest` | 12 | 0 | 0 | 0 | 0 | 12 | 0 |
| `RollbackMutablity.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `RollbackTortureTest.versetest` | 15 | 13 | 0 | 0 | 0 | 2 | 0 |
| `Roundtrip/Comments.versetest` | 96 | 90 | 0 | 5 | 0 | 1 | 0 |
| `Roundtrip/Definitions.versetest` | 13 | 13 | 0 | 0 | 0 | 0 | 0 |
| `Roundtrip/For.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Roundtrip/IfElse.versetest` | 24 | 24 | 0 | 0 | 0 | 0 | 0 |
| `Roundtrip/KnownBugs.versetest` | 23 | 19 | 0 | 3 | 0 | 1 | 0 |
| `Roundtrip/Literals.versetest` | 48 | 48 | 0 | 0 | 0 | 0 | 0 |
| `Roundtrip/Newlines.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Roundtrip/Operators.versetest` | 43 | 43 | 0 | 0 | 0 | 0 | 0 |
| `RuntimeErrorCallstack.versetest` | 3 | 2 | 0 | 0 | 0 | 1 | 0 |
| `RuntimeErrors.versetest` | 13 | 5 | 0 | 0 | 0 | 8 | 0 |
| `RuntimeErrorsAutoRTFMCascadingAbort.versetest` | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| `RuntimeErrorsAutoRTFMLanguageAbort.versetest` | 11 | 0 | 0 | 0 | 0 | 11 | 0 |
| `RuntimeErrorsAutoRTFMRuntimeAbort.versetest` | 8 | 0 | 0 | 0 | 0 | 8 | 0 |
| `RuntimeWarningCallstack.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `SamplingProfiler.versetest` | 2 | 1 | 0 | 0 | 0 | 1 | 0 |
| `Self.versetest` | 17 | 17 | 0 | 0 | 0 | 0 | 0 |
| `SelfClass.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `SemicolonsVsCommas.versetest` | 56 | 53 | 0 | 1 | 0 | 2 | 0 |
| `Serialization/Array.versetest` | 193 | 0 | 0 | 0 | 0 | 193 | 0 |
| `Serialization/Comparable.versetest` | 75 | 0 | 0 | 0 | 0 | 75 | 0 |
| `Serialization/Function.versetest` | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| `Serialization/Map.versetest` | 236 | 0 | 0 | 0 | 0 | 236 | 0 |
| `Serialization/Option.versetest` | 168 | 0 | 0 | 0 | 0 | 168 | 0 |
| `Serialization/Scalar.versetest` | 203 | 0 | 0 | 0 | 0 | 203 | 0 |
| `Serialization/Struct.versetest` | 53 | 0 | 0 | 0 | 0 | 53 | 0 |
| `Serialization/Tuple.versetest` | 56 | 0 | 0 | 0 | 0 | 56 | 0 |
| `ShadowDefinition.versetest` | 65 | 38 | 0 | 5 | 0 | 22 | 0 |
| `SingleParamArray.versetest` | 16 | 15 | 0 | 1 | 0 | 0 | 0 |
| `SingleParamTuple.versetest` | 7 | 6 | 0 | 0 | 0 | 1 | 0 |
| `SoftwareTransactionalMemory.versetest` | 31 | 30 | 1 | 0 | 0 | 0 | 0 |
| `StmCallbackErrors.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `StringInterpolationPlus.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Subtype.versetest` | 106 | 97 | 0 | 8 | 0 | 1 | 0 |
| `Super.versetest` | 32 | 26 | 0 | 1 | 0 | 5 | 0 |
| `TestSubobjectRenaming.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `TimSyntax.versetest` | 282 | 238 | 0 | 44 | 0 | 0 | 0 |
| `TransactionalTaskScope.versetest` | 7 | 0 | 0 | 7 | 0 | 0 | 0 |
| `Tuple.versetest` | 70 | 57 | 1 | 0 | 0 | 12 | 0 |
| `Type.versetest` | 37 | 34 | 0 | 3 | 0 | 0 | 0 |
| `TypeAlias.versetest` | 79 | 63 | 0 | 2 | 0 | 14 | 0 |
| `TypeChecking.versetest` | 53 | 53 | 0 | 0 | 0 | 0 | 0 |
| `TypeParam.versetest` | 15 | 6 | 0 | 9 | 0 | 0 | 0 |
| `TypeSpec.versetest` | 5 | 4 | 0 | 1 | 0 | 0 | 0 |
| `TypeValue.versetest` | 12 | 2 | 0 | 0 | 0 | 10 | 0 |
| `Union.versetest` | 252 | 107 | 0 | 138 | 0 | 7 | 0 |
| `UnsupportedNativeConstructor.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `VarAccessSpecifiers.versetest` | 25 | 12 | 0 | 0 | 0 | 13 | 0 |
| `VarSet.versetest` | 31 | 30 | 0 | 0 | 0 | 1 | 0 |
| `Versions/FN29.30/FN29.30-FinalSpecifierFixes.versetest` | 18 | 0 | 0 | 0 | 0 | 18 | 0 |
| `Versions/FN29.30/FN29.30-NamedParametersInLocalize.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Versions/FN30.00/FN30.00-StricterTestForDefaultValuesInConcreteClasses.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Versions/FN31.00/FN31.00-ConcurrentMacrosIntroduceScopes.versetest` | 12 | 0 | 0 | 0 | 0 | 12 | 0 |
| `Versions/FN33.00/FN33.00-EnforceCorrectQualifiedNames.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Versions/FN33.00/FN33.00-StrictConstructorFunctionInvocation.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Versions/FN34.10/FN34.10-DisallowInstanceInAttributeExpression.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Versions/FN36.00/FN36.00-DetectInaccessibleTypesInParametricTypeArguments.versetest` | 6 | 0 | 0 | 0 | 0 | 6 | 0 |
| `Versions/FN37.00/FN37.00-EnforceCastableTag.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Versions/FN37.30/FN37.30-DefaultInitializers.versetest` | 6 | 0 | 0 | 0 | 0 | 6 | 0 |
| `Versions/FN40.00/FN40.00-DisallowGlobalInstancesOfInterfaceVars.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Versions/FN40.00/FN40.00-EnforceEffectChecks.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Versions/FN40.00/FN40.00-EnforceInterfaceConstructionEffects.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Versions/FN40.00/FN40.00-EnforceInterfaceDataMustBeInitializedOrAccessible.versetest` | 18 | 0 | 0 | 0 | 0 | 18 | 0 |
| `Versions/FN40.00/FN40.00-FixOverrideOfParametricFinalFields.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Versions/FN41.00/FN41.00-DisableMutableFieldsInParametricInterfaces.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Versions/FN41.00/FN41.00-FirstAdded.versetest` | 5 | 0 | 0 | 0 | 0 | 5 | 0 |
| `Versions/FN42.10/FN42.10-InheritedFieldsConstrainSubtyping.versetest` | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| `Versions/FN42.20/FN42.20-EnforceCastableAIError.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Versions/VerseVersions.versetest` | 8 | 0 | 0 | 0 | 0 | 8 | 0 |
| `Versions/v1/v1-Local-Qualifiers.versetest` | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| `Versions/v1/v1-MapLiteralKeysHandleIterationAndFailure.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Versions/v1/v1-Mix-comma-and-semicolon-in-archetype-instantiation.versetest` | 31 | 2 | 0 | 0 | 0 | 29 | 0 |
| `Versions/v1/v1-PublicStructFields.versetest` | 18 | 2 | 0 | 0 | 0 | 16 | 0 |
| `Versions/v1/v1-SetMutatesFailure.versetest` | 28 | 0 | 0 | 0 | 0 | 28 | 0 |
| `Versions/v1/v1-UniqueAttributeRequiresAllocatesEffect.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Versions/v2/v2-CommentsAreIncludedInStringContents.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Versions/v2/v2-NoOctalLiterals.versetest` | 70 | 1 | 0 | 0 | 0 | 69 | 0 |
| `Void.versetest` | 60 | 47 | 2 | 11 | 0 | 0 | 0 |
| `WebDataSyncService.versetest` | 5 | 1 | 0 | 2 | 0 | 2 | 0 |
| `Where.versetest` | 6 | 5 | 0 | 1 | 0 | 0 | 0 |
| `WhereConstrainedFloats.versetest` | 27 | 24 | 0 | 3 | 0 | 0 | 0 |
| `WhereConstrainedInts.versetest` | 53 | 42 | 0 | 9 | 2 | 0 | 0 |
| `await-regalloc-transactional-unification-variables.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `await.versetest` | 41 | 7 | 0 | 1 | 0 | 33 | 0 |
| `closed.versetest` | 5 | 4 | 0 | 1 | 0 | 0 | 0 |
| `generators.versetest` | 67 | 11 | 0 | 2 | 0 | 54 | 0 |
| `persistable.versetest` | 23 | 18 | 1 | 1 | 0 | 3 | 0 |
| `profile_simple.versetest` | 36 | 21 | 0 | 0 | 0 | 15 | 0 |
| `return-should-be-trailed.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `upon.versetest` | 13 | 5 | 0 | 8 | 0 | 0 | 0 |
| `using-local_scope.versetest` | 21 | 12 | 0 | 0 | 0 | 9 | 0 |
| `weak_map.versetest` | 96 | 38 | 0 | 5 | 0 | 53 | 0 |
| `when.versetest` | 22 | 7 | 0 | 15 | 0 | 0 | 0 |
