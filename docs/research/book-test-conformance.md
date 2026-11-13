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
the readings of [After the readings audit](#after-the-readings-audit)
and the access specifiers of [After access specifiers](#after-access-specifiers),
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
- **3,721 are not translatable** (28%): virtual packages and modules
  (1,264); the compiler's test runner, its natives and classes (1,207), its
  coroutine controls `CoroUtils` (552) and its other modules (187); engine
  APIs (persistence, JSON, natives; 345); compiler tooling such as bytecode
  and digests (128); VM-conditional code inside a definition (37) and one
  file that defines `Main` itself (1).
- Of the **9,783 translatable cases**, openverse **agrees on 7,535 (77%)**,
  refuses 2,028 valid programs, **accepts 170 refused ones**, gives a
  **different result in 50** and hits **no internal error**. On test cases
  alone (without `:decls`) it agrees on 7,388 of 9,567. (When the survey was
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
  specifiers](#after-access-specifiers).)
- An agreement on an expected error is weak evidence: 2,906 expected errors
  agree, but only 1,195 of them are refused by a check of a language rule;
  1,236 are refused by the parser (the lexer's and parser's own checks
  included) and 475 for a missing feature.
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
  of a float (the C runtime), the rollback of a `for` iteration and
  `return`/`break` out of a failure context (load-bearing) are designed
  there and left, and comparison chains are where the Book disagrees with
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
  parser tests and other syntax (192); bitwise functions (159, pinned, not
  implemented), free `ToChar` and `ToChar32` the API reference does not
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
| `assert_semantic_error`, `assert_link_error`, `assert_ir_error` | as `assert_valid` | refused (exit 4); the error codes are recorded, not compared |
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
  failure context for `spawn`, which openverse refuses there: the 17 cases
  of *spawn in a failure context* below are exposed by this wrapping.
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
| all test cases (assertions and files without one) | 13197 | 7388 | 170 | 1959 | 50 | 3630 | 0 |
| shared definitions of a file (`:decls`) | 307 | 147 | 0 | 69 | 0 | 91 | 0 |
| **total** | 13504 | 7535 | 170 | 2028 | 50 | 3721 | 0 |

### By form

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| `assert` | 6671 | 3110 | 0 | 1372 | 50 | 2139 | 0 |
| `assert_semantic_error` | 3460 | 2584 | 133 | 0 | 0 | 743 | 0 |
| `assert_valid` | 1637 | 722 | 0 | 396 | 0 | 519 | 0 |
| `assert_valid_syntax` | 439 | 330 | 0 | 109 | 0 | 0 | 0 |
| `decls` | 307 | 147 | 0 | 69 | 0 | 91 | 0 |
| `assert_roundtrip` | 304 | 267 | 0 | 35 | 0 | 2 | 0 |
| `assert_syntax_error` | 303 | 300 | 3 | 0 | 0 | 0 | 0 |
| `assert_runtime_error` | 140 | 30 | 0 | 43 | 0 | 67 | 0 |
| `assert_link_error` | 55 | 10 | 24 | 0 | 0 | 21 | 0 |
| `assert_digest_generated` | 53 | 0 | 0 | 0 | 0 | 53 | 0 |
| `assert_auto_qualification` | 29 | 0 | 0 | 0 | 0 | 29 | 0 |
| `assert_bytecode` | 25 | 0 | 0 | 0 | 0 | 25 | 0 |
| `assert_ir_error` | 24 | 12 | 10 | 0 | 0 | 2 | 0 |
| `assert_link_valid` | 22 | 18 | 0 | 1 | 0 | 3 | 0 |
| `file` | 13 | 4 | 0 | 3 | 0 | 6 | 0 |
| `incremental_compilation` | 12 | 0 | 0 | 0 | 0 | 12 | 0 |
| `assert_fingerprint_determinism` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `assert_persistence_snapshot` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `assert_used_assets` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `assert_success_or_runtime_error` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |

### By VM tag

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| no VM restriction | 12208 | 7257 | 132 | 1538 | 23 | 3258 | 0 |
| `verse_vm_only` | 702 | 203 | 5 | 365 | 27 | 102 | 0 |
| `bp_vm_only` | 366 | 67 | 33 | 14 | 0 | 252 | 0 |
| `verse_vm_todo` (BPVM only; a known VerseVM failure) | 219 | 8 | 0 | 111 | 0 | 100 | 0 |
| `auto_qualify_todo` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |

### By directory

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| (top level) | 5575 | 3126 | 77 | 1121 | 9 | 1242 | 0 |
| Operators/ | 1203 | 1022 | 4 | 76 | 28 | 73 | 0 |
| Bugs/ | 1185 | 717 | 42 | 177 | 0 | 249 | 0 |
| Literals/ | 1020 | 815 | 0 | 171 | 0 | 34 | 0 |
| Serialization/ | 991 | 0 | 0 | 0 | 0 | 991 | 0 |
| Attributes/ | 795 | 421 | 3 | 125 | 0 | 246 | 0 |
| FlowControl/ | 484 | 362 | 33 | 39 | 5 | 45 | 0 |
| Intrinsics/ | 437 | 297 | 0 | 107 | 8 | 25 | 0 |
| Math/ | 321 | 157 | 0 | 160 | 0 | 4 | 0 |
| Classes/ | 317 | 227 | 3 | 10 | 0 | 77 | 0 |
| Versions/ | 289 | 4 | 0 | 2 | 0 | 283 | 0 |
| Roundtrip/ | 255 | 229 | 0 | 24 | 0 | 2 | 0 |
| Coroutines/ | 229 | 21 | 1 | 3 | 0 | 204 | 0 |
| Modules/ | 219 | 69 | 4 | 9 | 0 | 137 | 0 |
| Features/ | 67 | 18 | 3 | 1 | 0 | 45 | 0 |
| Interfaces/ | 41 | 34 | 0 | 0 | 0 | 7 | 0 |
| Bytecode/ | 27 | 2 | 0 | 0 | 0 | 25 | 0 |
| Exercises/ | 17 | 14 | 0 | 3 | 0 | 0 | 0 |
| Incremental/ | 16 | 0 | 0 | 0 | 0 | 16 | 0 |
| DebugStackTrace/ | 8 | 0 | 0 | 0 | 0 | 8 | 0 |
| CanCallerAccessEpicInternal/ | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| AssetUsage/ | 1 | 0 | 0 | 0 | 0 | 1 | 0 |

Of the 2,906 expected errors openverse agrees with, the refusal came from
the parser in 1,236 (most semantic-error snippets among them use a form
openverse does not parse, such as `@attribute`; the lexer's and parser's
own checks, of comments, float literals, specifiers and an extension
method's receiver, count here), from a diagnostic that says openverse
lacks a feature or a name in 475, and from a rule check in 1,195. Only these 1,195 show
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

50 cases (58 before [the readings audit](#after-the-readings-audit), 85 before [the empty value](#after-the-empty-value); 85 with the parser forms too: two comments inside strings agree now, and two internal errors compare now as below) run in openverse and give another result than the assertion
expects (in every one the assertion fails or a runtime error is raised; no
case prints differently, since the tests check values, not output).

| Cause | Cases | Example | openverse | The test | Marked | openverse documents it | Size |
|---|---:|---|---|---|---|---|---|
| empty values are one value | 30 → 32 → 4 ([After the empty value](#after-the-empty-value): 28 agree) | `Tests/Operators/BoolQuery.versetest:3`: `assert{true?=false}` | `true?` is `true`, so the comparison fails | succeeds: `true?` and `(true? and true?)` are the empty value | none; the operators chapter: "`IsReady?` is equivalent to comparing against true" | yes: Readings, "`X?` of a logic" | front-end: the value of `X?` of a logic ([empty-values.md](empty-values.md), 3.1) |
| `int` precision | 26 | `Tests/Operators/BinarySubInt.versetest:40`: `assert{0 - -9223372036854775808 = 9223372036854775807+1}` | `error: overflow` | succeeds | all `verse_vm_only`; their `bp_vm_only` twins expect the runtime error and agree | yes: the BPVM reading of the `int` range ([Readings](../LANGUAGE.md#readings-openverse-takes)) | Core and runtime (unbounded integers); keep as a reading |
| rollback of a `for` iteration | 8 → 10 (`for.versetest` 317, 344, refused for `array{} = for(…)` before) → 7 (317 and `SoftwareTransactionalMemory.versetest` 74, 81 agree: a failing range bound gives no iterations, [the readings audit](#after-the-readings-audit)) | `Tests/Range.versetest:140`: `for (J:(set X = array{666}); I := GetLower()..GetUpper())` with an empty range, then `X = array{42}` | keeps what a source or a range bound did before a later clause failed (`X` stays `array{666}`; in `Tests/FlowControl/for.versetest:362` `Y.Inc()` in an inner range bound is kept for the rejected `I = 2`) | undone with the iteration | none | in part: Readings, "Code before a choice" (#208, #283) | front-end feature: one transaction per iteration, sources included |
| `ToString` of a float | 7 | `Tests/Intrinsics/FloatToString.versetest:18`: `TestSignedFloatToString[1.0, "1.000000"]` | `1.0` | `1.000000`: six decimals, every digit of a large value | none; the Book's prose example is `98.5`, so prose and tests disagree | yes: Readings, `ToString` of a float | a message-sized change in both formatters; an owner decision |
| commas and semicolons in blocks | 4 | `Tests/Option.versetest:44`: `assert{option{1,2}?=(1,2)}` | `option{1,2}` holds `2`; `for(…){C,I}` yields `I` | commas in braces make a tuple (the Book's ch. 1, "Semicolons vs Commas": `Comma := { A, B, C }` is a tuple) | none | no | parser form, and an owner decision: today commas separate statements |
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
| unreachable code | 39 → 30 | `Tests/FlowControl/Reachability.versetest:12`: `F():int={if(return 0=1) {0} else {1}; 1+2}` | accepted | errors 2000, 2002, 2302, 3535, 3616: code after `return`, `break` or a `case` that always returns, unreachable or repeated `case` arms | none | no | front-end: a reachability pass |
| failure where it is not allowed | 35 → 30 → 29 (`LogicalOr.versetest:143`: the left of `or` must be able to fail, the readings audit) | `Tests/Effects.versetest:537`: `c:=class{X:int=option{0}?}` | accepted | error 3512: a failable field default, a failable default of a named parameter (16 in `DefaultNamed.versetest`), a `loop` as an `if` condition; 3513: `not` of an expression that cannot fail | 3 `bp_vm_only`, 1 `verse_vm_only` | in part: a default "is evaluated at the call, its effects counting as the caller's" ([Supported](../LANGUAGE.md#supported), Functions) | a message |
| misplaced specifiers | 32 → 0 | `Tests/Attributes/FinalSuperAttribute.versetest:56`: `i<final_super>:int = 42` | accepted | error 3596: `<abstract>` on a method, `<concrete>` or `<final>` on an interface, `<castable>` or `<final_super>` on a name; 3680: a class below a `<final_super_base>` class must be `<final_super>` | none | no (openverse refuses `<final_super>` classes, #11) | a message |
| other type rules | 31 → 28 | `Tests/Bugs/2023-01-18-FunctionParameterWithoutDomain.versetest:12`: `F(X:int=0):void={}` | accepted | a default on a positional parameter (3625); a named argument before a positional one (`DefaultNamed.versetest:122`); `var` in a struct (`Classes/Struct.versetest:31`, 3607); `set S.M = 1` on a field that is no `var` (`Mutability.versetest:426`); `X:tuple() = if (false?) then (1, 2) else false` (`Void.versetest:223`, refused now that `tuple()` is a type of its own); joins of classes through a shared interface (`SOL-5838`); polymorphic and mutual recursion of parametric classes, which the test comments call "not yet supported" (`ParametricTypes.versetest:263-269`); `using` of a path to a class | 1 `bp_vm_only` | no | messages, one each |
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
| bitwise functions | 159 | `Tests/Math/Bitwise.versetest:36`: `assert{BitNot(0) = -1}` | `unknown function 'BitNot'` | 62 `verse_vm_only` (unbounded ints), 13 `bp_vm_only` (runtime errors for shifts) | no; the Book's ch. 4, "Bitwise Operations" | Core and runtime: six `int` primitives, their Lean seams and C |
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
| class effect specifiers | 23 | `Tests/Attributes/allocates.versetest:6`: `c := class<computes><allocates> { Value:int = 0 }` | `<computes> excludes the heap effects … that class/interface also has` | none | yes: construction effects (#508) | a message |
| other library functions | 23 | `Tests/GetCastableFinalSuperClass.versetest:60` | `unknown function 'GetCastableFinalSuperClass'` (15), `FitsInPlayerMap` (3, persistence), `signalable(t)` and `awaitable(t)` (3), `GetSecondsSinceEpoch` (2, a clock) | none | [the library note](book-library-functions.md) | features: #11, persistence, the concurrency interfaces, a time source |
| `weak_map` | 22 | `Tests/weak_map.versetest:32` | `unknown function 'weak_map'` | 1 `verse_vm_only` | yes: [Not supported in v1](../LANGUAGE.md#not-supported-in-v1), #491 | front-end and Core |
| module constants of mutable classes | 21 | `Tests/Bugs/FORT-721882-CallingFunctionWithNullObject.versetest:14` | `the constant NullTestObject would hold an object with var fields …: make it a function` | 17 `verse_vm_todo` | yes, in the message | front-end and Core (module state) |
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
| bitwise functions (159) | pinned, not implemented | 0 | 159 |

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
9. **Bitwise functions (159 refusals; Core and runtime, or Verse Core's
   operations).** `BitAnd`, `BitOr`, `BitXor`, `BitNot`, `BitShiftLeft`,
   `BitShiftRight` on `int`, pinned in [the library
   note](book-library-functions.md#bitwise-functions-not-implemented):
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

Next in line: unreachable code (39 accepted refusals; a reachability pass),
the `ToDiagnostic` printer (93), and `of`/`at` calls (27, a parser form the
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

**Accepted: access specifiers** (0): all 107 agree now ([After access specifiers](#after-access-specifiers)).

**Accepted: failure where it is not allowed** (29): `Bugs/SOL-1987-IfDoesNotDetectNestedConditional.versetest` 22; `Bugs/SOL-4199-BreakFromIf.versetest` 80; `DefaultNamed.versetest` 820, 824, 844, 852, 853, 854, 859, 861, 862, 867, 868, 870, 875, 876, 877, 878; `Effects.versetest` 490, 537, 551, 552, 557(b), 558(b), 565(b), 573(v); `FlowControl/Case.versetest` 291; `FlowControl/for.versetest` 223; `ParametricTypes.versetest` 465

**Accepted: unreachable code** (30): `Bugs/SOL-4194-AssertOnMalformedCaseContainingDataDefinition.versetest` 20; `Bugs/SOL-4199-BreakFromIf.versetest` 87; `Enum.versetest` 356; `FlowControl/Case.versetest` 154, 272, 280; `FlowControl/Reachability.versetest` 5, 11, 12, 13, 14, 15, 23, 39, 57, 76, 91, 99, 100, 107, 108; `FlowControl/Return.versetest` 115, 118, 148, 158, 159, 161, 162, 163, 179

**Accepted: other type rules** (28): `Bugs/2023-01-18-FunctionParameterWithoutDomain.versetest` 12; `Bugs/FORT-744399-DefaultTupleFieldsCrashComplier.versetest` 62; `Bugs/SOL-4199-BreakFromIf.versetest` 4, 15, 51, 60; `Bugs/SOL-5838-JoinOfClassesWithCommonBaseClassWithInterfaceInheritance.versetest` 13, 22; `Classes/Constructor.versetest` 528; `Classes/Struct.versetest` 31; `DefaultNamed.versetest` 122; `Enum.versetest` 171(b); `FunctionTypes.versetest` 191; `Modules/Using2.versetest` 94; `Mutability.versetest` 426; `Option.versetest` 94; `ParametricFunctions.versetest` 348, 356, 361, 374, 431, 438; `ParametricTypes.versetest` 263, 265, 269; `QualifiedIdentifier.versetest` 152; `Void.versetest` 246, 260

**Accepted: limits of Epic's compiler** (23): `Bugs/FORT-592189-MaybeCoerceToTypeCrash.versetest` 4(b); `Bugs/SOL-5477-CrashInGenClassDefinition.versetest` 5(b); `DefaultNamed.versetest` 629(b), 640(b), 741(b), 751(b); `Function.versetest` 238(b), 271(b); `Map.versetest` 45, 46, 223, 224, 249; `Operators/CompareMap.versetest` 58, 59, 71, 72; `ParametricFunctions.versetest` 276(b), 366, 496; `Tuple.versetest` 456(b); `WhereConstrainedInts.versetest` 97, 100

**Accepted: name limits of the BPVM** (19): `Bugs/FORT-555217-VeryLongIdentifier.versetest` 25(b), 31(b), 37(b); `Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest` 5(b), 11(b), 67(b), 73(b), 79(b), 85(b), 92(b), 98(b), 154(b), 160(b), 166(b), 172(b), 187(b), 193(b), 199(b), 205(b)

**Accepted: duplicate definitions** (1): `QualifiedIdentifier.versetest` 315

**Accepted: effects of initializers** (8): `Features/DefaultValueAssignment.versetest` 200, 215, 225; `GlobalVariables.versetest` 86(v), 90(v), 97(v), 105(v); `Modules/ModuleDefinitions.versetest` 279

**Accepted: `<concrete>` classes** (7): `Attributes/concrete.versetest` 38, 76; `Bugs/SOL-3366-MakeClassesConcreteByDefault.versetest` 8, 15, 24; `Bugs/SOL-7781-ConcreteClassDoesntEnforceDefaultValuesForInterfaceFields.versetest` 28, 54

**Accepted: control forms** (7): `Coroutines/Concurrency.versetest` 832; `FlowControl/Break.versetest` 118, 161; `FlowControl/Return.versetest` 114, 117; `Modules/Using2.versetest` 86, 90

**Accepted: interface inheritance** (7): `Interface.versetest` 33, 40, 92, 194, 199; `InterfaceDiamond.versetest` 74, 89

**Accepted: qualifiers** (6): `Bugs/SOL-3564-CallingSuperClassMethodFromOverriddenMethod.versetest` 7, 18, 32, 45; `Super.versetest` 183, 238

**Accepted: other syntax** (3): `Classes/ClassBlockClause.versetest` 19; `ReserveDotSpace.versetest` 5, 6

**Accepted: `<final>` members** (1): `Attributes/final.versetest` 125

**Accepted: `<persistable>` structs** (1): `persistable.versetest` 59

**Different output: empty values are one value** (4): `Operators/BoolQuery.versetest` 3, 4; `Operators/LogicalAnd.versetest` 29; `Operators/Precedence.versetest` 121

**Different output: `int` precision** (26): `Intrinsics/Abs.versetest` 17(v); `Operators/BinaryAddInt.versetest` 35(v), 36(v), 37(v), 38(v), 65(v), 66(v), 67(v), 68(v); `Operators/BinaryDivInt.versetest` 49(v), 50(v); `Operators/BinaryMulInt.versetest` 49(v), 50(v), 52(v), 53(v); `Operators/BinarySubInt.versetest` 39(v), 40(v), 41(v), 42(v), 44(v), 45(v), 47(v), 48(v); `Operators/Negate.versetest` 14(v); `WhereConstrainedInts.versetest` 224(v), 227(v)

**Different output: rollback of a `for` iteration** (7): `FlowControl/for.versetest` 344, 362, 371, 392; `Range.versetest` 140, 159; `SoftwareTransactionalMemory.versetest` 88

**Different output: `ToString` of a float** (7): `Intrinsics/FloatToString.versetest` 15, 18, 19, 21, 22, 23, 24

**Different output: order of `set X op= e`** (1): `ArrayAppend.versetest` 12(v)

**Different output: commas and semicolons in blocks** (4): `FlowControl/for.versetest` 293; `Option.versetest` 44; `SemicolonsVsCommas.versetest` 95, 100

**Different output: comparison chains** (1): `Operators/Associativity.versetest` 9


## Appendix B: totals per file

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| `Any.versetest` | 83 | 62 | 0 | 18 | 0 | 3 | 0 |
| `ArchetypeAccessSpecifiers.versetest` | 11 | 11 | 0 | 0 | 0 | 0 | 0 |
| `Archetypes.versetest` | 41 | 34 | 0 | 0 | 0 | 7 | 0 |
| `Array.versetest` | 22 | 17 | 0 | 5 | 0 | 0 | 0 |
| `ArrayAppend.versetest` | 27 | 11 | 0 | 10 | 1 | 5 | 0 |
| `AssetUsage/IncrementalAssetUsage.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `AssignmentSequencing.versetest` | 7 | 3 | 0 | 4 | 0 | 0 | 0 |
| `Attributes/AccessLevelInheritance.versetest` | 66 | 60 | 0 | 6 | 0 | 0 | 0 |
| `Attributes/AccessSpecifiersDisallowedOnLocalVars.versetest` | 9 | 9 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/Attributes.versetest` | 34 | 21 | 0 | 11 | 0 | 2 | 0 |
| `Attributes/CustomAttributes.versetest` | 47 | 36 | 0 | 11 | 0 | 0 | 0 |
| `Attributes/CustomClassVarAccessors.versetest` | 61 | 15 | 0 | 17 | 0 | 29 | 0 |
| `Attributes/DeepMutabilityForCustomClassVarAccessors.versetest` | 19 | 0 | 0 | 1 | 0 | 18 | 0 |
| `Attributes/FinalSuperAttribute.versetest` | 25 | 18 | 0 | 7 | 0 | 0 | 0 |
| `Attributes/Internal.versetest` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |
| `Attributes/InvalidAttributeLocations.versetest` | 43 | 43 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/abstract.versetest` | 19 | 19 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/allocates.versetest` | 33 | 27 | 0 | 5 | 0 | 1 | 0 |
| `Attributes/available.versetest` | 77 | 7 | 0 | 13 | 0 | 57 | 0 |
| `Attributes/concrete.versetest` | 44 | 38 | 2 | 4 | 0 | 0 | 0 |
| `Attributes/deprecated.versetest` | 111 | 38 | 0 | 36 | 0 | 37 | 0 |
| `Attributes/experimental.versetest` | 47 | 1 | 0 | 0 | 0 | 46 | 0 |
| `Attributes/export_metadata.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Attributes/final.versetest` | 22 | 21 | 1 | 0 | 0 | 0 | 0 |
| `Attributes/intrinsic.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/native.versetest` | 20 | 1 | 0 | 0 | 0 | 19 | 0 |
| `Attributes/override.versetest` | 16 | 12 | 0 | 4 | 0 | 0 | 0 |
| `Attributes/scoped.versetest` | 51 | 33 | 0 | 0 | 0 | 18 | 0 |
| `Attributes/unique.versetest` | 34 | 15 | 0 | 10 | 0 | 9 | 0 |
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
| `Bugs/2020-06-18-DefaultClassValues.versetest` | 3 | 0 | 0 | 1 | 0 | 2 | 0 |
| `Bugs/2020-06-18-DefaultObjectValues.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-06-18-RushReturnValForImmediateCoros.versetest` | 2 | 0 | 0 | 1 | 0 | 1 | 0 |
| `Bugs/2020-06-22-CoroutineInClassImplementingInterface.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/2020-07-31-UnaryTypeSpecOnLeftHandSideOfEquals.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/2020-08-05-NoMethodBody.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-08-05-UnusedArchetypeUseAfterFree.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-08-11-TypeSpecVsComparePrecedence.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-09-01-EmitReturnAssert.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-10-26-DefineLocalWithMutatingAssignment.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-03-23-CoroutineOverrideParameterNameMismatch.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/2021-03-23-InterfaceDefaultCoroutineImplementation.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/2021-04-26-DisjointTypesAllowedInComparisonAndPointerDeref.versetest` | 3 | 1 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/2021-08-18-DisjointResultInNestedIf.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-08-23-struct_in_struct_sol-1986.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-08-26-UsingFunctionAsTypeInItsOwnDefinition.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-08-31-ConcatenatingArraysOfStrings.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-09-03-ConcatEqualsAssertionFailure.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-09-03-OptionalTupleAssertionFailure.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/2021-09-03-UniquePointerInitializerTypeErrorAssertionFailure.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2021-10-05-AttributeNames.versetest` | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
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
| `Bugs/2023-01-18-FunctionParameterWithoutDomain.versetest` | 4 | 3 | 1 | 0 | 0 | 0 | 0 |
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
| `Bugs/2023-04-28-IncorrectNameMangling.versetest` | 3 | 2 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/2024-12-02-VerseVMPropertyGeneratorGetOrCreateTupleTypeCrash.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2026-01-26-FindFirstAsyncSubExprMissingOverrides.versetest` | 4 | 1 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/ArrayClassOf.versetest` | 2 | 1 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/ArrayOrFailureResult.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/AssignmentToWhile.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/AttributeOnSameLineAsDefinition.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/BPVMOnly/AsyncContextCancellation.versetest` | 8 | 0 | 0 | 0 | 0 | 8 | 0 |
| `Bugs/BPVMOnly/CancelledArmDefers.versetest` | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| `Bugs/BPVMOnly/LeftoverArmDeferTiming.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/BPVMOnly/NestedUpdateStateCorruption.versetest` | 6 | 0 | 0 | 0 | 0 | 6 | 0 |
| `Bugs/BPVMOnly/RaceCompletionTiming.versetest` | 6 | 0 | 0 | 0 | 0 | 6 | 0 |
| `Bugs/BPVMOnly/RefinedMapKeyInterfaceOverride.versetest` | 10 | 0 | 0 | 10 | 0 | 0 | 0 |
| `Bugs/BlockWithAssignmentShouldNotCrash.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/Braces.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/DigestInheritedCallbackParametricSubscribe.versetest` | 5 | 0 | 0 | 0 | 0 | 5 | 0 |
| `Bugs/FORT-1006008-ResolveAmbiguityAwayFromInternalAPI.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-1017224-ReadsEffectAllowedInComputesClassOrInterfaceDefaultExpressions.versetest` | 11 | 0 | 0 | 0 | 0 | 11 | 0 |
| `Bugs/FORT-1033995-ReinstancingCrashInForEachSubobject.versetest` | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| `Bugs/FORT-1042316-GetInstancedSubobjectOverwritesASubobjectWithItself.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-1054384-Void-Any-Meet.versetest` | 3 | 0 | 0 | 2 | 0 | 1 | 0 |
| `Bugs/FORT-1059276.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-1088027-MultipleArmsCompleteDuringSpawn.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-1088027-OldGenerationWakeDuringSpawn.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-1088027-UseOfNullInitializedDynamicallyTypedValue.versetest` | 5 | 0 | 0 | 3 | 0 | 2 | 0 |
| `Bugs/FORT-1126351-GenericSignalableDeferredSignalConvertCrash.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-1126351-GenericSignalableReentrantConvertCrash.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-1126351-RaceArmSuspendedAfterResolution.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-1126351-RaceArmsDoNotStartAfterResolution.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-1126351_cross_event_reentrancy_probe.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/FORT-1126351_object_payload_reentrancy_probe.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-1126351_reentrant_signal_probe.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/FORT-1146499-GeneratedAssetNameConflicts.versetest` | 11 | 0 | 0 | 0 | 0 | 11 | 0 |
| `Bugs/FORT-555213-DontSignedInt32OverflowInArrayBytes.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-555217-VeryLongIdentifier.versetest` | 6 | 3 | 3 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-559416-AddExtensionMethodsToForgotUsingMessage.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-571286-CrashMisinterpretingUObjectPointerAsDynamicallyTypedValue.versetest` | 8 | 4 | 0 | 4 | 0 | 0 | 0 |
| `Bugs/FORT-574089-SucceedsConstructorFallibleArgument.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-581999-ErrorNodeInIrGenerator.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-582128-PathLiteralAsValue.versetest` | 12 | 11 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-582129-VariableTypeReferencesVariableName.versetest` | 21 | 21 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-582630-BranchResult.versetest` | 3 | 2 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-583815-SelfCancellation.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-585106-WriteLogicCauseCompilerToAssert.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-586526-PrematureRuntimeTypePurge.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-590869-NamedWithDefaultCoercion.versetest` | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/FORT-592189-MaybeCoerceToTypeCrash.versetest` | 2 | 1 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-623803-STMRollbackAfterReturn.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-635190-AssertIndexingContainerAfterRuntimeError.versetest` | 16 | 0 | 0 | 16 | 0 | 0 | 0 |
| `Bugs/FORT-642876-CollidingCoercedOverrideNames.versetest` | 11 | 0 | 0 | 11 | 0 | 0 | 0 |
| `Bugs/FORT-687100-Mix-comma-and-semicolon-in-archetype-instantiation.versetest` | 9 | 7 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-713493-CaseTypeError.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-713847-RaceCoerce.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-720968-DetectInaccessibleTypesAcrossPackagesWithDifferentUploadedAtVersions.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Bugs/FORT-721882-CallingFunctionWithNullObject.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-722788-LookupBindingDataOfFunctionInModulePart.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-734038-CrashAfterReportingAnErrorRelatedToNamedParameters.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-741838-SuccessFailureParametricTypes.versetest` | 5 | 0 | 0 | 5 | 0 | 0 | 0 |
| `Bugs/FORT-743839-SetMapWithIfExpr.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-744399-DefaultTupleFieldsCrashComplier.versetest` | 11 | 10 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-746888-CodegenGeneratesDuplicateLocalPropertyNames.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-760026-NonUniquePropertyNamesInSuspendsFunction.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/FORT-763813-CrashIfClassInheritFromStruct.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-779650-LocalVarCompoundAssignmentRollbackMemoryCorruption.versetest` | 6 | 4 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-779858-CrashDeltaSerializingAgainstUninitializedDynamicallyTypedValue.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest` | 47 | 14 | 16 | 0 | 0 | 17 | 0 |
| `Bugs/FORT-861412-ImprovedErrorMessage.versetest` | 8 | 2 | 0 | 0 | 0 | 6 | 0 |
| `Bugs/FORT-889314-InterfaceFieldOverriddenWithGetterSetterBroken.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-951162-CantQualifyPropertiesOfParametricClasses.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-976754-GetterSetter.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-987013-MissingUploadedAtFNVersion.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-995029-CrashHashingDynamicallyTypedMapKey.versetest` | 3 | 1 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FunctionWithoutExclamationPoint.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/IteratingOverDataMemberArray.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/LogicalNot.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/ParameterCountCrash.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1729-MakeAttributesForwardCompatible.versetest` | 6 | 5 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-1736-AssertionFailuresWithArrayConcatenation.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1758-LoopUsesResultOfLastSubexpression.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1830-LocalVariablesCanEscape.versetest` | 20 | 20 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1924-RaceDeferSynchronization.versetest` | 10 | 0 | 0 | 0 | 0 | 10 | 0 |
| `Bugs/SOL-1928-CallMethodOnResultOfCallToUndefinedFunction.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1957-InterfaceMethodReturningStructAssert.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-1987-IfDoesNotDetectNestedConditional.versetest` | 3 | 2 | 1 | 0 | 0 | 0 | 0 |
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
| `Bugs/SOL-3366-MakeClassesConcreteByDefault.versetest` | 7 | 3 | 3 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-3422-CyclicInterfacesAndClasses.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3515-CallingExtensionMethodWithoutSelf.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3563-DontStackOverflowOnCyclicInterfaces.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3564-CallingSuperClassMethodFromOverriddenMethod.versetest` | 16 | 8 | 4 | 4 | 0 | 0 | 0 |
| `Bugs/SOL-3628-SuspendsMethodSuperCall.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-3629-SuspendsMethodEffectSubtype.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-3662-LineCommentEndsIndentedBlock.versetest` | 7 | 6 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-3729-UnidentifiedIdentInCaseCondition.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3731-CoercionOfParametricFieldOverrides.versetest` | 5 | 2 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/SOL-3732-PartialModuleParametricClassAssert.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-3734-UnicodeCausesCompilerErrors.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-3793-StackingSuperQualifiers.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3799-AddToMembersWhileIteratingOverThem.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-3819-DefinitionsInTypeSpecifiers.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3825-IsComparableShouldHandleCycles.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3887-MessageArray.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-3911-SuspendsArgumentAsForIterable.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-4107-StmWritesPoppedLocalVar.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4137-MemoryLeakCreatingA3dArray.versetest` | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/SOL-4170-DefinitionAstNodeUseAfterFree.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4171-CallStackOverflow.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4194-AssertOnMalformedCaseContainingDataDefinition.versetest` | 3 | 2 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4196-ErrCauseEnsureFailure.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4199-BreakFromIf.versetest` | 10 | 3 | 6 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-4204-MapPartialWrite.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4208-OverrideWithVar.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4209-SuspendingSubexpressionsOfSpawnedInvocation.versetest` | 6 | 3 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/SOL-4266-RaceContinuationExecution.versetest` | 5 | 0 | 0 | 0 | 0 | 5 | 0 |
| `Bugs/SOL-4284-InfiniteLoopTriggersUObjectLimit.versetest` | 3 | 0 | 0 | 1 | 0 | 2 | 0 |
| `Bugs/SOL-4289-SyncUninitializedLocalArray.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Bugs/SOL-4332-BranchRace.versetest` | 10 | 0 | 0 | 0 | 0 | 10 | 0 |
| `Bugs/SOL-4339-CallingConstructorsForUStructs.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/SOL-4357-TypeType.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4389-VerseTypeInitializationDoesNotProperlyHandleInitializationOverrides.versetest` | 19 | 0 | 0 | 0 | 0 | 19 | 0 |
| `Bugs/SOL-4527-CoercedInterfaceOverride.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5386-CrashUsingSuperToCallOverrideInParametricClass.versetest` | 5 | 3 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-5452-NullDereferenceAfterRuntimeError.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-5477-CrashInGenClassDefinition.versetest` | 2 | 1 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5496-CaseCodeBlocksWithoutScopes.versetest` | 8 | 1 | 0 | 7 | 0 | 0 | 0 |
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
| `Bugs/SOL-6529-WarnAboutAlwaysFailingContainerLookups.versetest` | 6 | 5 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-6739-ParametricTypeMeetAndJoin.versetest` | 25 | 10 | 0 | 15 | 0 | 0 | 0 |
| `Bugs/SOL-6934-OptionTypeIgnoresHashabilityOfValue.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-6945-JoinOfTupleOfNamedElementsAndArray.versetest` | 8 | 6 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-7017-AvailableAttributeOnlyUsesDefinitionPackageVersion.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Bugs/SOL-7079-IllegalQualifiedName.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-7157-CoercingRationalToAny.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-7231-NamedParameterMeet.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-7388-TaskGroupCorruption.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-7459-OverridingAnInterfaceVariableWithANativeVariableIsNotSupported.versetest` | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| `Bugs/SOL-7475-dynamic-casting-through-CTypeVariable.versetest` | 6 | 2 | 0 | 4 | 0 | 0 | 0 |
| `Bugs/SOL-7503-ProblemWithQualification.versetest` | 4 | 0 | 0 | 4 | 0 | 0 | 0 |
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
| `Bugs/SOL-8267-InterfaceDefaultsAreNotReinstantiated.versetest` | 6 | 2 | 0 | 3 | 0 | 1 | 0 |
| `Bugs/SOL-8302-CastableSubtypeFailsWithInterfaces.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-8380-InterfaceAccessorsNativeFailed.versetest` | 5 | 0 | 0 | 0 | 0 | 5 | 0 |
| `Bugs/SOL-8527-DefaultInitializerGlobalObject.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-8557-InitializeVarMissesDefDest.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-8558-RequireConcreteForNativeSetter.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-8627-concrete_subtype-effects.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-8722-InterfaceConstructionEffectLeak.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-8768-QualificationOfExtensionFields.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-8814-OverrideOfExperimentalDefinitionIsNotUseOfExperimental.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Bugs/SOL-8836-RepeatedInstantiation.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-8891-StringNativeConversion.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-8918-PartialModuleModuleLevelFunctionFailure.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-9061-DocCommentsOnQualifiedIdentifiers.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-9192-DigestSourceOrder.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-9661-ForLoopWithNonGeneratorDomain.versetest` | 9 | 9 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-9691-CaptureSuper.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
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
| `Cast.versetest` | 65 | 47 | 0 | 18 | 0 | 0 | 0 |
| `Castable.versetest` | 101 | 44 | 0 | 39 | 0 | 18 | 0 |
| `Classes/AccessSpecifiers.versetest` | 61 | 48 | 0 | 0 | 0 | 13 | 0 |
| `Classes/Class.versetest` | 42 | 42 | 0 | 0 | 0 | 0 | 0 |
| `Classes/ClassBlockClause.versetest` | 24 | 16 | 1 | 0 | 0 | 7 | 0 |
| `Classes/Constructor.versetest` | 61 | 15 | 1 | 6 | 0 | 39 | 0 |
| `Classes/DataInheritence.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Classes/IdentifierSuper.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Classes/Inheritance.versetest` | 11 | 10 | 0 | 1 | 0 | 0 | 0 |
| `Classes/MethodInheritance.versetest` | 9 | 1 | 0 | 0 | 0 | 8 | 0 |
| `Classes/QualifiedMethodInheritance.versetest` | 23 | 21 | 0 | 2 | 0 | 0 | 0 |
| `Classes/SelfInheritance.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Classes/Struct.versetest` | 77 | 66 | 1 | 0 | 0 | 10 | 0 |
| `Classes/VarPointingToClass.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `ClassifiableSubset.versetest` | 36 | 9 | 0 | 27 | 0 | 0 | 0 |
| `CoercedOverrides.versetest` | 10 | 3 | 0 | 4 | 0 | 3 | 0 |
| `Comparable.versetest` | 49 | 7 | 0 | 42 | 0 | 0 | 0 |
| `ComparableInterface.versetest` | 17 | 12 | 0 | 5 | 0 | 0 | 0 |
| `CompatibilityConstraints.versetest` | 320 | 0 | 0 | 0 | 0 | 320 | 0 |
| `ComputationLimit.versetest` | 3 | 2 | 0 | 0 | 0 | 1 | 0 |
| `Coroutines/Concurrency.versetest` | 86 | 11 | 1 | 1 | 0 | 73 | 0 |
| `Coroutines/ConcurrencyEscape.versetest` | 49 | 0 | 0 | 0 | 0 | 49 | 0 |
| `Coroutines/Flow.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Coroutines/IteratedPrimitives.versetest` | 6 | 4 | 0 | 0 | 0 | 2 | 0 |
| `Coroutines/Loop.versetest` | 3 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Coroutines/ParamAlignment.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Coroutines/SelfCancel.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Coroutines/SpawnAndTask.versetest` | 77 | 5 | 0 | 2 | 0 | 70 | 0 |
| `CyclicReferences.versetest` | 13 | 13 | 0 | 0 | 0 | 0 | 0 |
| `DataMemberValidation.versetest` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |
| `DebugStackTrace/FrameOrder.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DebugStackTrace/Recursion.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DebugStackTrace/Spawn.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DebugStackTrace/When.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DefaultNamed.versetest` | 142 | 110 | 21 | 1 | 0 | 10 | 0 |
| `Definitions.versetest` | 16 | 15 | 0 | 1 | 0 | 0 | 0 |
| `DigestGeneration.versetest` | 43 | 1 | 0 | 0 | 0 | 42 | 0 |
| `DigestVisibility.versetest` | 47 | 31 | 0 | 0 | 0 | 16 | 0 |
| `Duplication.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `DynamicallyTypedSubobjectInstantiation.versetest` | 16 | 16 | 0 | 0 | 0 | 0 | 0 |
| `Effects.versetest` | 336 | 256 | 8 | 5 | 0 | 67 | 0 |
| `Enum.versetest` | 71 | 59 | 2 | 6 | 0 | 4 | 0 |
| `EnumCompare.versetest` | 12 | 0 | 0 | 12 | 0 | 0 | 0 |
| `Escape.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `EvaluationOrder.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Event.versetest` | 6 | 0 | 0 | 4 | 0 | 2 | 0 |
| `EventShouldBeCallable.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Exercises/BalancedBinaryTree.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/BinaryTreeInorderTraversalRecursive.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/EpicProgrammingAssessmentBinarySearch.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/SameTree.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/TwoSum.versetest` | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
| `ExtensionFields.versetest` | 39 | 37 | 0 | 0 | 0 | 2 | 0 |
| `Failure.versetest` | 34 | 31 | 0 | 0 | 0 | 3 | 0 |
| `Features/DefaultValueAssignment.versetest` | 67 | 18 | 3 | 1 | 0 | 45 | 0 |
| `FlowControl/Break.versetest` | 17 | 15 | 2 | 0 | 0 | 0 | 0 |
| `FlowControl/Case.versetest` | 71 | 65 | 4 | 1 | 0 | 1 | 0 |
| `FlowControl/Concurrency/branch.versetest` | 10 | 4 | 0 | 1 | 0 | 5 | 0 |
| `FlowControl/Continue.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/If.versetest` | 94 | 94 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/IfDecidesErrors.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/Reachability.versetest` | 25 | 9 | 15 | 1 | 0 | 0 | 0 |
| `FlowControl/Return.versetest` | 86 | 63 | 11 | 11 | 0 | 1 | 0 |
| `FlowControl/Yield.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/defer.versetest` | 51 | 13 | 0 | 1 | 0 | 37 | 0 |
| `FlowControl/first.versetest` | 24 | 3 | 0 | 20 | 0 | 1 | 0 |
| `FlowControl/for.versetest` | 94 | 84 | 1 | 4 | 5 | 0 | 0 |
| `Function.versetest` | 81 | 61 | 2 | 1 | 0 | 17 | 0 |
| `FunctionAsType.versetest` | 36 | 17 | 0 | 18 | 0 | 1 | 0 |
| `FunctionTypes.versetest` | 42 | 26 | 1 | 15 | 0 | 0 | 0 |
| `GenerateFunctionForParametricClass.versetest` | 2 | 1 | 0 | 0 | 0 | 1 | 0 |
| `GenerateFunctionForParametricInterface.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `GetCastableFinalSuperClass.versetest` | 94 | 7 | 0 | 87 | 0 | 0 | 0 |
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
| `Interface.versetest` | 109 | 96 | 5 | 5 | 0 | 3 | 0 |
| `InterfaceAccessVisibility.versetest` | 19 | 12 | 0 | 0 | 0 | 7 | 0 |
| `InterfaceDiamond.versetest` | 18 | 16 | 2 | 0 | 0 | 0 | 0 |
| `InterfaceWithAccessors.versetest` | 6 | 3 | 0 | 3 | 0 | 0 | 0 |
| `InterfaceWithFields.versetest` | 37 | 25 | 0 | 11 | 0 | 1 | 0 |
| `Interfaces/AccessSpecifiers.versetest` | 41 | 34 | 0 | 0 | 0 | 7 | 0 |
| `Intrinsics/Abs.versetest` | 19 | 16 | 0 | 0 | 1 | 2 | 0 |
| `Intrinsics/ArrayFind.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayInsert.versetest` | 18 | 18 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayLength.versetest` | 14 | 14 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemove.versetest` | 26 | 24 | 0 | 2 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemoveAllElements.versetest` | 10 | 10 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemoveElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemoveFirstElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceAll.versetest` | 13 | 10 | 0 | 3 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceAllElements.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceFirstElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArraySlice.versetest` | 61 | 61 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/CharConversionExtensionMethods.versetest` | 15 | 15 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/CharToString.versetest` | 10 | 10 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/Concatenate.versetest` | 25 | 19 | 0 | 6 | 0 | 0 | 0 |
| `Intrinsics/ConcatenateMaps.versetest` | 29 | 26 | 0 | 3 | 0 | 0 | 0 |
| `Intrinsics/Err.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/FloatToString.versetest` | 12 | 3 | 0 | 0 | 7 | 2 | 0 |
| `Intrinsics/IntToString.versetest` | 11 | 11 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/MapLength.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/StringLength.versetest` | 16 | 16 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/StringToString.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ToDiagnostic.versetest` | 114 | 0 | 0 | 93 | 0 | 21 | 0 |
| `LengthOptimizationSafety.versetest` | 8 | 1 | 0 | 4 | 0 | 3 | 0 |
| `LenientClassConstruction.versetest` | 8 | 4 | 0 | 0 | 0 | 4 | 0 |
| `Literals/Char.versetest` | 184 | 39 | 0 | 145 | 0 | 0 | 0 |
| `Literals/Float.versetest` | 176 | 142 | 0 | 0 | 0 | 34 | 0 |
| `Literals/Function.versetest` | 22 | 3 | 0 | 19 | 0 | 0 | 0 |
| `Literals/Int.versetest` | 166 | 166 | 0 | 0 | 0 | 0 | 0 |
| `Literals/Logic.versetest` | 36 | 34 | 0 | 2 | 0 | 0 | 0 |
| `Literals/Path.versetest` | 237 | 237 | 0 | 0 | 0 | 0 | 0 |
| `Literals/String.versetest` | 199 | 194 | 0 | 5 | 0 | 0 | 0 |
| `LiveVariables.versetest` | 56 | 12 | 0 | 44 | 0 | 0 | 0 |
| `Localization.versetest` | 40 | 12 | 0 | 28 | 0 | 0 | 0 |
| `LocalizationJoin.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `MacroForms.versetest` | 17 | 17 | 0 | 0 | 0 | 0 | 0 |
| `ManyEmergentTypes.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Map.versetest` | 104 | 81 | 5 | 18 | 0 | 0 | 0 |
| `MapOrder.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Math/Bitwise.versetest` | 174 | 11 | 0 | 159 | 0 | 4 | 0 |
| `Math/Math.versetest` | 77 | 76 | 0 | 1 | 0 | 0 | 0 |
| `Math/MaxFloat.versetest` | 22 | 22 | 0 | 0 | 0 | 0 | 0 |
| `Math/MaxInt.versetest` | 13 | 13 | 0 | 0 | 0 | 0 | 0 |
| `Math/MinFloat.versetest` | 22 | 22 | 0 | 0 | 0 | 0 | 0 |
| `Math/MinInt.versetest` | 13 | 13 | 0 | 0 | 0 | 0 | 0 |
| `MetatypeConcreteSubtype.versetest` | 38 | 12 | 0 | 26 | 0 | 0 | 0 |
| `Modules/AccessSpecifiers.versetest` | 34 | 0 | 0 | 0 | 0 | 34 | 0 |
| `Modules/AssetAccessibility.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Modules/Import.versetest` | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| `Modules/Module.versetest` | 58 | 39 | 0 | 3 | 0 | 16 | 0 |
| `Modules/ModuleDefinitions.versetest` | 62 | 24 | 1 | 1 | 0 | 36 | 0 |
| `Modules/ModuleScopedInstances.versetest` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |
| `Modules/PartialModuleDefinitions.versetest` | 14 | 2 | 0 | 5 | 0 | 7 | 0 |
| `Modules/Using.versetest` | 22 | 1 | 0 | 0 | 0 | 21 | 0 |
| `Modules/Using2.versetest` | 9 | 3 | 3 | 0 | 0 | 3 | 0 |
| `Mutability.versetest` | 55 | 53 | 1 | 1 | 0 | 0 | 0 |
| `NamedParameterOverloads.versetest` | 36 | 35 | 0 | 1 | 0 | 0 | 0 |
| `NamedParamsFromNative.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `NamesReservedForFuture.versetest` | 69 | 69 | 0 | 0 | 0 | 0 | 0 |
| `NativeDeepMutability.versetest` | 19 | 0 | 0 | 0 | 0 | 19 | 0 |
| `NativePropertyRequiresNativeClass.versetest` | 6 | 0 | 0 | 0 | 0 | 6 | 0 |
| `NativePropertyRollback.versetest` | 15 | 1 | 0 | 13 | 0 | 1 | 0 |
| `NativePropertyWriteHook.versetest` | 10 | 0 | 0 | 0 | 0 | 10 | 0 |
| `NestedArrays.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `NestedFunctions.versetest` | 32 | 13 | 0 | 17 | 0 | 2 | 0 |
| `NestedNamedTupleParameters.versetest` | 24 | 9 | 0 | 7 | 0 | 8 | 0 |
| `NestedObjects.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `NestedTupleParameters.versetest` | 16 | 7 | 0 | 6 | 0 | 3 | 0 |
| `ObjectToJson.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Operators/Associativity.versetest` | 16 | 15 | 0 | 0 | 1 | 0 | 0 |
| `Operators/At.versetest` | 15 | 3 | 0 | 12 | 0 | 0 | 0 |
| `Operators/BinaryAddArray.versetest` | 14 | 9 | 0 | 5 | 0 | 0 | 0 |
| `Operators/BinaryAddFloat.versetest` | 36 | 22 | 0 | 0 | 0 | 14 | 0 |
| `Operators/BinaryAddInt.versetest` | 43 | 32 | 0 | 1 | 8 | 2 | 0 |
| `Operators/BinaryAddString.versetest` | 16 | 14 | 0 | 2 | 0 | 0 | 0 |
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
| `Operators/CompareMap.versetest` | 97 | 84 | 4 | 9 | 0 | 0 | 0 |
| `Operators/CompareOption.versetest` | 18 | 18 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareRational.versetest` | 4 | 3 | 0 | 1 | 0 | 0 | 0 |
| `Operators/CompareString.versetest` | 148 | 126 | 0 | 22 | 0 | 0 | 0 |
| `Operators/CompareStruct.versetest` | 36 | 32 | 0 | 0 | 0 | 4 | 0 |
| `Operators/CompareTuple.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Operators/CompareTypeChecking.versetest` | 39 | 39 | 0 | 0 | 0 | 0 | 0 |
| `Operators/DisallowedOperatorDefinitions.versetest` | 30 | 30 | 0 | 0 | 0 | 0 | 0 |
| `Operators/LogicalAnd.versetest` | 9 | 8 | 0 | 0 | 1 | 0 | 0 |
| `Operators/LogicalNot.versetest` | 11 | 11 | 0 | 0 | 0 | 0 | 0 |
| `Operators/LogicalOr.versetest` | 90 | 80 | 0 | 10 | 0 | 0 | 0 |
| `Operators/Negate.versetest` | 6 | 5 | 0 | 0 | 1 | 0 | 0 |
| `Operators/Of.versetest` | 15 | 1 | 0 | 14 | 0 | 0 | 0 |
| `Operators/PostAt.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Operators/PostfixCallArray.versetest` | 16 | 14 | 0 | 0 | 0 | 2 | 0 |
| `Operators/PostfixCallMap.versetest` | 31 | 31 | 0 | 0 | 0 | 0 | 0 |
| `Operators/PostfixCallString.versetest` | 22 | 22 | 0 | 0 | 0 | 0 | 0 |
| `Operators/Precedence.versetest` | 68 | 67 | 0 | 0 | 1 | 0 | 0 |
| `Operators/PrefixStar.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Option.versetest` | 63 | 61 | 1 | 0 | 1 | 0 | 0 |
| `OutOfScopeOverloads.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Overloading.versetest` | 79 | 64 | 0 | 9 | 0 | 6 | 0 |
| `PackageCycles.versetest` | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| `ParametricCastingIsDisallowed.versetest` | 11 | 10 | 0 | 1 | 0 | 0 | 0 |
| `ParametricFunctions.versetest` | 106 | 46 | 9 | 47 | 0 | 4 | 0 |
| `ParametricTypes.versetest` | 274 | 149 | 4 | 98 | 0 | 23 | 0 |
| `Parentheses.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `Path.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `PersistentJson.versetest` | 103 | 1 | 0 | 0 | 0 | 102 | 0 |
| `PersistentJsonSnapshot.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `PersistentJsonSnapshotMacro.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `PersonaJson.versetest` | 102 | 0 | 0 | 0 | 0 | 102 | 0 |
| `Placeholder.versetest` | 9 | 9 | 0 | 0 | 0 | 0 | 0 |
| `Pointers.versetest` | 66 | 62 | 0 | 4 | 0 | 0 | 0 |
| `PrintScriptCallstack.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `QualifiedIdentifier.versetest` | 88 | 54 | 2 | 16 | 0 | 16 | 0 |
| `Range.versetest` | 39 | 37 | 0 | 0 | 2 | 0 | 0 |
| `Rational.versetest` | 49 | 48 | 0 | 0 | 0 | 1 | 0 |
| `Recursion.versetest` | 47 | 47 | 0 | 0 | 0 | 0 | 0 |
| `ReentrantExceptions.versetest` | 3 | 0 | 0 | 1 | 0 | 2 | 0 |
| `Reference.versetest` | 4 | 1 | 0 | 0 | 0 | 3 | 0 |
| `ReserveDotSpace.versetest` | 14 | 12 | 2 | 0 | 0 | 0 | 0 |
| `ResolvingIdentifiers.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `RetryTransactionUnderAutoRTFM.versetest` | 12 | 0 | 0 | 0 | 0 | 12 | 0 |
| `RollbackMutablity.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `RollbackTortureTest.versetest` | 15 | 3 | 0 | 10 | 0 | 2 | 0 |
| `Roundtrip/Comments.versetest` | 96 | 81 | 0 | 14 | 0 | 1 | 0 |
| `Roundtrip/Definitions.versetest` | 13 | 13 | 0 | 0 | 0 | 0 | 0 |
| `Roundtrip/For.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Roundtrip/IfElse.versetest` | 24 | 24 | 0 | 0 | 0 | 0 | 0 |
| `Roundtrip/KnownBugs.versetest` | 23 | 18 | 0 | 4 | 0 | 1 | 0 |
| `Roundtrip/Literals.versetest` | 48 | 48 | 0 | 0 | 0 | 0 | 0 |
| `Roundtrip/Newlines.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Roundtrip/Operators.versetest` | 43 | 39 | 0 | 4 | 0 | 0 | 0 |
| `RuntimeErrorCallstack.versetest` | 3 | 2 | 0 | 0 | 0 | 1 | 0 |
| `RuntimeErrors.versetest` | 13 | 2 | 0 | 3 | 0 | 8 | 0 |
| `RuntimeErrorsAutoRTFMCascadingAbort.versetest` | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| `RuntimeErrorsAutoRTFMLanguageAbort.versetest` | 11 | 0 | 0 | 0 | 0 | 11 | 0 |
| `RuntimeErrorsAutoRTFMRuntimeAbort.versetest` | 8 | 0 | 0 | 0 | 0 | 8 | 0 |
| `RuntimeWarningCallstack.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `SamplingProfiler.versetest` | 2 | 0 | 0 | 1 | 0 | 1 | 0 |
| `Self.versetest` | 17 | 17 | 0 | 0 | 0 | 0 | 0 |
| `SelfClass.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `SemicolonsVsCommas.versetest` | 56 | 44 | 0 | 8 | 2 | 2 | 0 |
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
| `SingleParamTuple.versetest` | 7 | 6 | 0 | 1 | 0 | 0 | 0 |
| `SoftwareTransactionalMemory.versetest` | 31 | 30 | 0 | 0 | 1 | 0 | 0 |
| `StmCallbackErrors.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `StringInterpolationPlus.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Subtype.versetest` | 106 | 51 | 0 | 54 | 0 | 1 | 0 |
| `Super.versetest` | 32 | 24 | 2 | 1 | 0 | 5 | 0 |
| `TestSubobjectRenaming.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `TimSyntax.versetest` | 282 | 213 | 0 | 69 | 0 | 0 | 0 |
| `TransactionalTaskScope.versetest` | 7 | 0 | 0 | 7 | 0 | 0 | 0 |
| `Tuple.versetest` | 70 | 55 | 1 | 2 | 0 | 12 | 0 |
| `Type.versetest` | 37 | 34 | 0 | 3 | 0 | 0 | 0 |
| `TypeAlias.versetest` | 79 | 63 | 0 | 2 | 0 | 14 | 0 |
| `TypeChecking.versetest` | 53 | 53 | 0 | 0 | 0 | 0 | 0 |
| `TypeParam.versetest` | 15 | 1 | 0 | 14 | 0 | 0 | 0 |
| `TypeSpec.versetest` | 5 | 4 | 0 | 1 | 0 | 0 | 0 |
| `TypeValue.versetest` | 12 | 1 | 0 | 1 | 0 | 10 | 0 |
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
| `Versions/v1/v1-Mix-comma-and-semicolon-in-archetype-instantiation.versetest` | 31 | 0 | 0 | 2 | 0 | 29 | 0 |
| `Versions/v1/v1-PublicStructFields.versetest` | 18 | 2 | 0 | 0 | 0 | 16 | 0 |
| `Versions/v1/v1-SetMutatesFailure.versetest` | 28 | 0 | 0 | 0 | 0 | 28 | 0 |
| `Versions/v1/v1-UniqueAttributeRequiresAllocatesEffect.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Versions/v2/v2-CommentsAreIncludedInStringContents.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Versions/v2/v2-NoOctalLiterals.versetest` | 70 | 1 | 0 | 0 | 0 | 69 | 0 |
| `Void.versetest` | 60 | 37 | 2 | 21 | 0 | 0 | 0 |
| `WebDataSyncService.versetest` | 5 | 1 | 0 | 2 | 0 | 2 | 0 |
| `Where.versetest` | 6 | 5 | 0 | 1 | 0 | 0 | 0 |
| `WhereConstrainedFloats.versetest` | 27 | 24 | 0 | 3 | 0 | 0 | 0 |
| `WhereConstrainedInts.versetest` | 53 | 40 | 2 | 9 | 2 | 0 | 0 |
| `await-regalloc-transactional-unification-variables.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `await.versetest` | 41 | 7 | 0 | 1 | 0 | 33 | 0 |
| `closed.versetest` | 5 | 4 | 0 | 1 | 0 | 0 | 0 |
| `generators.versetest` | 67 | 11 | 0 | 2 | 0 | 54 | 0 |
| `persistable.versetest` | 23 | 18 | 1 | 1 | 0 | 3 | 0 |
| `profile_simple.versetest` | 36 | 9 | 0 | 12 | 0 | 15 | 0 |
| `return-should-be-trailed.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `upon.versetest` | 13 | 5 | 0 | 8 | 0 | 0 | 0 |
| `using-local_scope.versetest` | 21 | 12 | 0 | 0 | 0 | 9 | 0 |
| `weak_map.versetest` | 96 | 18 | 0 | 27 | 0 | 51 | 0 |
| `when.versetest` | 22 | 7 | 0 | 15 | 0 | 0 | 0 |
