# Book of Verse test conformance

This survey runs openverse on every test case of the Book of Verse's own test
suite and records, case by case, whether openverse agrees. It measures
openverse at `0e69cfb862d8e6888a944049cf79bedd8404aa31` (main, 2026-11-13)
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
- **3,706 are not translatable** (27%): virtual packages and modules
  (1,264); the compiler's test runner, its natives and classes (1,204), its
  coroutine controls `CoroUtils` (552) and its other modules (175); engine
  APIs (persistence, JSON, natives; 345); compiler tooling such as bytecode
  and digests (128); VM-conditional code inside a definition (37) and one
  file that defines `Main` itself (1).
- Of the **9,798 translatable cases**, openverse **agrees on 6,409 (65%)**,
  refuses 2,817 valid programs, **accepts 482 refused ones**, gives a
  **different result in 86** and hits an **internal error in 4**. On test
  cases alone (without `:decls`) it agrees on 6,300 of 9,582.
- An agreement on an expected error is weak evidence: 2,593 expected errors
  agree, but only 689 of them are refused by a check of a language rule;
  1,472 are refused by the parser and 432 for a missing feature.
- **Internal errors**: three programs fail `Prog.checkTypes` (`X:int =
  return`, `() = ""`, a `void` parameter compared with `""`), and Lean
  answers an out-of-memory with a panic and exit 1 where C gives
  `limit: memory` and exit 3.
- **Dangerous**: openverse accepts duplicate class, struct and enum
  definitions and silently keeps the first; accepts `X:int = X` and then
  stops on the recursion limit; accepts the 65 names the tests reserve and
  `_`; does not strip comments inside string literals, which the Book's
  chapter 1 requires; and compares `false`, `()`, `""`, `array{}`,
  `map{}` and an empty option as different values, which the Book's
  chapter 2 calls one value. Four documented readings contradict the tests:
  the order of `set X += e`, the key order of `ConcatenateMaps`, the
  format of `ToString` of a float and comparison chains; the BPVM `int`
  reading gives the 26 VerseVM-only overflow differences.
- **Most refusals are syntax**: path literals (213, nearly all parse-only
  tests), empty class and function bodies (160), unnamed parameters (123),
  attributes (131), qualified names (102); and missing library functions:
  bitwise (159), character conversions (140), `ToDiagnostic` (93). The
  largest semantic gaps are types as values (166), `comparable` as a type
  (102) and VerseVM-only union types (137).

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
| `assert`, `assert_runtime_error`, `assert_success_or_runtime_error` | the file's `using`s and the shared definitions the body needs, then `Main()<decides>:void = BODY` (braced bodies stay braced, indented ones indented) | `assert`: `Main` succeeds (exit 0); `assert_runtime_error`: a runtime error (exit 2) or resource limit (exit 3); `…_or_runtime_error`: exit 0, 2 or 3 |
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
| the test runner's natives and classes | 1204 |
| the test runner's `CoroUtils` | 552 |
| engine API `FromJson` | 153 |
| the test runner's `TestUtils` | 113 |
| `<native>` definitions | 93 |
| engine API `Persistence` | 63 |
| the test runner's `FloatConstants` | 57 |
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
| all test cases (assertions and files without one) | 13197 | 6300 | 482 | 2710 | 86 | 3615 | 4 |
| shared definitions of a file (`:decls`) | 307 | 109 | 0 | 107 | 0 | 91 | 0 |
| **total** | 13504 | 6409 | 482 | 2817 | 86 | 3706 | 4 |

### By form

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| `assert` | 6671 | 2725 | 0 | 1734 | 86 | 2124 | 2 |
| `assert_semantic_error` | 3460 | 2274 | 442 | 0 | 0 | 743 | 1 |
| `assert_valid` | 1637 | 567 | 0 | 551 | 0 | 519 | 0 |
| `assert_valid_syntax` | 439 | 112 | 0 | 327 | 0 | 0 | 0 |
| `decls` | 307 | 109 | 0 | 107 | 0 | 91 | 0 |
| `assert_roundtrip` | 304 | 253 | 0 | 49 | 0 | 2 | 0 |
| `assert_syntax_error` | 303 | 294 | 9 | 0 | 0 | 0 | 0 |
| `assert_runtime_error` | 140 | 29 | 0 | 44 | 0 | 67 | 0 |
| `assert_link_error` | 55 | 10 | 24 | 0 | 0 | 21 | 0 |
| `assert_digest_generated` | 53 | 0 | 0 | 0 | 0 | 53 | 0 |
| `assert_auto_qualification` | 29 | 0 | 0 | 0 | 0 | 29 | 0 |
| `assert_bytecode` | 25 | 0 | 0 | 0 | 0 | 25 | 0 |
| `assert_ir_error` | 24 | 15 | 7 | 0 | 0 | 2 | 0 |
| `assert_link_valid` | 22 | 18 | 0 | 1 | 0 | 3 | 0 |
| `file` | 13 | 3 | 0 | 4 | 0 | 6 | 0 |
| `incremental_compilation` | 12 | 0 | 0 | 0 | 0 | 12 | 0 |
| `assert_fingerprint_determinism` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `assert_persistence_snapshot` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `assert_used_assets` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `assert_success_or_runtime_error` | 1 | 0 | 0 | 0 | 0 | 0 | 1 |

### By VM tag

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| no VM restriction | 12208 | 6143 | 445 | 2315 | 58 | 3243 | 4 |
| `verse_vm_only` | 702 | 188 | 7 | 377 | 28 | 102 | 0 |
| `bp_vm_only` | 366 | 70 | 30 | 14 | 0 | 252 | 0 |
| `verse_vm_todo` (BPVM only; a known VerseVM failure) | 219 | 8 | 0 | 111 | 0 | 100 | 0 |
| `auto_qualify_todo` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |

### By directory

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| (top level) | 5575 | 2687 | 229 | 1401 | 18 | 1239 | 1 |
| Operators/ | 1203 | 949 | 9 | 131 | 52 | 61 | 1 |
| Bugs/ | 1185 | 645 | 49 | 241 | 0 | 249 | 1 |
| Literals/ | 1020 | 592 | 12 | 381 | 1 | 34 | 0 |
| Serialization/ | 991 | 0 | 0 | 0 | 0 | 991 | 0 |
| Attributes/ | 795 | 308 | 67 | 174 | 0 | 246 | 0 |
| FlowControl/ | 484 | 308 | 48 | 78 | 4 | 45 | 1 |
| Intrinsics/ | 437 | 279 | 0 | 123 | 10 | 25 | 0 |
| Math/ | 321 | 110 | 0 | 207 | 0 | 4 | 0 |
| Classes/ | 317 | 194 | 33 | 13 | 0 | 77 | 0 |
| Versions/ | 289 | 3 | 0 | 2 | 1 | 283 | 0 |
| Roundtrip/ | 255 | 216 | 0 | 37 | 0 | 2 | 0 |
| Coroutines/ | 229 | 20 | 1 | 4 | 0 | 204 | 0 |
| Modules/ | 219 | 53 | 10 | 19 | 0 | 137 | 0 |
| Features/ | 67 | 16 | 5 | 1 | 0 | 45 | 0 |
| Interfaces/ | 41 | 15 | 19 | 0 | 0 | 7 | 0 |
| Bytecode/ | 27 | 2 | 0 | 0 | 0 | 25 | 0 |
| Exercises/ | 17 | 12 | 0 | 5 | 0 | 0 | 0 |
| Incremental/ | 16 | 0 | 0 | 0 | 0 | 16 | 0 |
| DebugStackTrace/ | 8 | 0 | 0 | 0 | 0 | 8 | 0 |
| CanCallerAccessEpicInternal/ | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| AssetUsage/ | 1 | 0 | 0 | 0 | 0 | 1 | 0 |

Of the 2,593 expected errors openverse agrees with, the refusal came from
the parser in 1,472 (1,167 semantic-error snippets: most use a form
openverse does not parse, such as `@attribute` or `(X:int).Method()`), from
a diagnostic that says openverse lacks a feature or a name in 432, and from
a rule check in 689. Only these 689 show openverse checking the rule the
test is about, and even they are not compared by code. Of the 294 agreeing
syntax errors, 8 parse once wrapped in a function body, so openverse refuses
them only because its top level takes definitions alone.

The full per-file table is in [Appendix B](#appendix-b-totals-per-file).

## Internal errors

Four cases. Each is a bug whatever the Book says. The programs below are
complete reproducers, reduced by hand from the cases.

| Case | Minimal program | openverse |
|---|---|---|
| `Tests/FlowControl/Return.versetest:11` (expects error 3548) | `X:int = return` and `Main():void = {}` | `internal error: the elaborated program does not pass Prog.checkTypes (in X)`. `X:void = return` is accepted; `F():int = return` is refused properly. |
| `Tests/Operators/CompareString.versetest:122` (expects success) | `Main()<decides>:void = { () = "" }` | `internal error: … Prog.checkTypes (in Main)`. `"" = ()` and `() = S` with `S:[]char` compile (and fail at run time, see [empty values](#different-output)). |
| `Tests/Void.versetest:300` (expects success) | `F(X:void)<decides>:void = { X = "" }` and `Main():void = {}` | `internal error: … Prog.checkTypes (in F)`; `X = 1` and `X = array{1}` compile. |
| `Tests/Bugs/FORT-555213-DontSignedInt32OverflowInArrayBytes.versetest:16` (expects success or a runtime error) | the test's `Foo(28)`, doubling an array 28 times, run under the 4 GB address-space cap `scripts/check.sh` uses | Lean: `INTERNAL PANIC: out of memory`, **exit 1** (the protocol's "`Main` failed"); C: `limit: memory`, exit 3. Lean and C disagree, and Lean breaks the exit protocol of [`FORMAT.md`](../FORMAT.md). |

The first three come from `=` (or a constant's value) whose operand types the
elaborator lets through and `Prog.checkTypes` then rejects: a message is
missing before lowering. Apart from the out-of-memory case, Lean and C
agreed byte for byte (output, status and diagnostics) on every program
both ran, and no accepted program raised a `type`, `slot`, `call` or
`control` error.

## Dangerous: accepted where the tests refuse, or different output

These are the cases where an openverse user would get a program the Book's
compiler refuses, or a different result. Every one is listed in
[Appendix A](#appendix-a-every-accepted-refusal-and-different-output).

### Different output

86 cases run in openverse and give another result than the assertion
expects (in every one the assertion fails or a runtime error is raised; no
case prints differently, since the tests check values, not output).

| Cause | Cases | Example | openverse | The test | Marked | openverse documents it | Size |
|---|---:|---|---|---|---|---|---|
| empty values are one value | 30 | `Tests/Operators/CompareString.versetest:139`: `assert{""=()}` | compiles; the comparison fails | succeeds: `false`, `()`, a `void` value, `""`, `array{}`, `map{}` and an empty option are equal; `true?` and `(true? and true?)` are that value | none; the Book (ch. 2, "void, true, tuple() and false"): "Verse has a single … value. It can be written `false` or `()`, and the types `void`, `true` and `tuple()` all describe it" | no | Core: one representation, or equality that relates them; an owner decision |
| `int` precision | 26 | `Tests/Operators/BinarySubInt.versetest:40`: `assert{0 - -9223372036854775808 = 9223372036854775807+1}` | `error: overflow` | succeeds | all `verse_vm_only`; their `bp_vm_only` twins expect the runtime error and agree | yes: the BPVM reading of the `int` range ([Readings](../LANGUAGE.md#readings-openverse-takes)) | Core and runtime (unbounded integers); keep as a reading |
| rollback of a `for` iteration | 8 | `Tests/Range.versetest:140`: `for (J:(set X = array{666}); I := GetLower()..GetUpper())` with an empty range, then `X = array{42}` | keeps what a source or a range bound did before a later clause failed (`X` stays `array{666}`; in `Tests/FlowControl/for.versetest:362` `Y.Inc()` in an inner range bound is kept for the rejected `I = 2`) | undone with the iteration | none | in part: Readings, "Code before a choice" (#208, #283) | front-end feature: one transaction per iteration, sources included |
| `ToString` of a float | 7 | `Tests/Intrinsics/FloatToString.versetest:18`: `TestSignedFloatToString[1.0, "1.000000"]` | `1.0` | `1.000000`: six decimals, every digit of a large value | none; the Book's prose example is `98.5`, so prose and tests disagree | yes: Readings, `ToString` of a float | a message-sized change in both formatters; an owner decision |
| commas and semicolons in blocks | 5 | `Tests/Option.versetest:44`: `assert{option{1,2}?=(1,2)}` | `option{1,2}` holds `2`; `Value :=` and an indented `1; 2; 3` binds `1`; `for(…){C,I}` yields `I` | commas in braces make a tuple; an indented block is one value (`3`) | none | no | parser form |
| order of `set X op= e` | 4 | `Tests/ArrayAppend.versetest:140`: `set S.X += if (set S.X = array{0}; 0=0) { array{42} } else { array{42} }`, then `S.X = array{0, 42}` | reads the old value first, giving `array{1, 2, 3, 42}` | evaluates `e` first | 2 `verse_vm_only` | yes: the Mutation row of [Supported](../LANGUAGE.md#supported) | front-end (evaluation order); an owner decision |
| comments inside strings | 2 | `Tests/Literals/String.versetest:234`: `assert{"abc<#def#>ghi" = "abcghi"}` | the string keeps `<#def#>` | the comment is removed | none; the Book's ch. 1 example and [the digest](book-of-verse-digest.md) §1.1 say the same | no | lexer, small |
| key order of `ConcatenateMaps` | 2 | `Tests/Intrinsics/ConcatenateMaps.versetest:21`: `ConcatenateMaps(map{"0"=>0,"1"=>1},map{"1"=>0,"0"=>1}) = map{"1"=>0,"0"=>1}` | a key keeps its first position | the later map's order | none | yes: the Maps row of [Supported](../LANGUAGE.md#supported) | front-end/library, small; an owner decision |
| comparison chains | 1 | `Tests/Operators/Associativity.versetest:9`: `assert{not 1 <> 2 <> 1}` | every adjacent pair is checked, so `1 <> 2 <> 1` succeeds | `(1 <> 2) <> 1` compares the left result `1` with `1` and fails | none | yes: Readings, associativity of comparisons | parser/front-end, small; an owner decision |
| a parametric struct compared across instances | 1 | `Tests/Operators/CompareStruct.versetest:43`: `parametric_comparable_struct([]int){X:=array{1,2}} = parametric_comparable_struct(tuple(int,int)){X:=(1,2)}` | compiles; fails | succeeds (an array equals a tuple of its elements) | none | in part: an array compares with a tuple ([Supported](../LANGUAGE.md#supported), Types) | front-end, small |

### Accepted where the tests expect an error

482 cases. The causes, by the error code the test expects:

| Cause | Cases | Example | openverse | The test | Marked | openverse documents it | Size |
|---|---:|---|---|---|---|---|---|
| access specifiers | 87 | `Tests/ArchetypeAccessSpecifiers.versetest:43`: `my_struct<public> := struct<protected>{x<public>:int}` | accepted | errors 3593, 3594, 3543, 3650, 3642: a `<private>`, `<protected>` or `<internal>` member used outside its scope, a specifier where none is allowed or two of them, access narrowed by an override | none | yes: Readings, "accepted and not enforced" | front-end: visibility per specifier, extending module visibility |
| reserved names | 83 | `Tests/NamesReservedForFuture.versetest:137`: `_:int = 42` | accepted | error 3514: 65 names reserved for the future (`as`, `bag`, `element`, `find`, `first`, `repeat`, …), `_`, and the built-in names `subtype`, `castable_subtype`, `Self` and `local` as definitions; 3547: `while := 42` and two others | none; the Book (ch. 1): "The single underscore `_` is reserved"; the digest notes the Book gives no list | no | a message |
| unreachable code | 38 | `Tests/FlowControl/Reachability.versetest:12`: `F():int={if(return 0=1) {0} else {1}; 1+2}` | accepted | errors 2000, 2002, 2302, 3535, 3616: code after `return`, `break` or a `case` that always returns, unreachable or repeated `case` arms | none | no | front-end: a reachability pass |
| failure where it is not allowed | 35 | `Tests/Effects.versetest:537`: `c:=class{X:int=option{0}?}` | accepted | error 3512: a failable field default, a failable default of a named parameter (16 in `DefaultNamed.versetest`), a `loop` as an `if` condition; 3513: `not` of an expression that cannot fail | 3 `bp_vm_only`, 1 `verse_vm_only` | in part: a default "is evaluated at the call, its effects counting as the caller's" ([Supported](../LANGUAGE.md#supported), Functions) | a message |
| misplaced specifiers | 30 | `Tests/Attributes/FinalSuperAttribute.versetest:56`: `i<final_super>:int = 42` | accepted | error 3596: `<abstract>` on a method, `<concrete>` or `<final>` on an interface, `<castable>` or `<final_super>` on a name; 3680: a class below a `<final_super_base>` class must be `<final_super>` | none | no (openverse refuses `<final_super>` classes, #11) | a message |
| duplicate definitions | 24 | `Tests/Bugs/2020-04-22-ThreeDuplicateDefinitions.versetest:17`: `C := class {}` three times | accepted, **the first kept silently** (two classes `C` with fields `X` and `Y`: `C{}.X` runs); also two structs or enums of one name, a class and a function of one name; a module function shadowed by a method (`ShadowDefinition.versetest`, 15) | error 3532 | none | no; constants and functions defined twice are refused | a message |
| limits of Epic's compiler | 22 | `Tests/Map.versetest:45`: `V12:[[]int]void = map{}` | accepted | error 3502: arrays and maps as map keys, joins of function types with different effects (7 `bp_vm_only` IR errors whose `verse_vm_only` twins expect valid), a refinement bound out of range | the Book (ch. 3): arrays as keys are rejected with "Use of `[]int` as a map key is not yet implemented"; 7 `bp_vm_only` | no | none needed: openverse is more general here |
| name limits of the BPVM | 19 | `Tests/Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest:92`: `Function():int` and `FUNCTION():int` in one module | accepted | link errors 9200, 9000, 9002, 3655: names equal but for case, identifiers too long for Unreal names | all `bp_vm_only` | no | none needed (an engine limit) |
| other type rules | 19 | `Tests/Bugs/2023-01-18-FunctionParameterWithoutDomain.versetest:12`: `F(X:int=0):void={}` | accepted | a default on a positional parameter (3625); a named argument before a positional one (`DefaultNamed.versetest:122`); `var` in a struct (`Classes/Struct.versetest:31`, 3607); `set S.M = 1` on a field that is no `var` (`Mutability.versetest:426`); `X:tuple() = if (false?) then (1, 2) else false` (`Void.versetest:223`); joins of classes through a shared interface (`SOL-5838`); polymorphic and mutual recursion of parametric classes, which the test comments call "not yet supported" (`ParametricTypes.versetest:263-269`); `using` of a path to a class | 1 `bp_vm_only` | no | messages, one each |
| `<concrete>` classes | 17 | `Tests/Attributes/concrete.versetest:21`: `class1 := class<concrete>:` with `Property:int` | accepted | error 3519: a concrete class needs a default for every field, also for interface fields | none | no | a message |
| control forms | 17 | `Tests/FlowControl/for.versetest:193`: `NotAnIterable:[]int= for(1) { 1 }` | accepted | `for` over what is no iterable or a range of an array (3524), `for(){}` (3544), a `loop` with no `break` (3579), `return` in a field default (3548) or a `for` body (3534), a non-suspending arm of `race` (3538), `using{/localhost}` | none | no | messages |
| float literal out of range | 12 | `Tests/Literals/Float.versetest:248`: `F():float=+2.0e+308` | accepted (infinity) | error 3554 | none | no: literals are "the nearest double" | a message |
| `<final>` members | 11 | `Tests/Attributes/final.versetest:64`: `c := class{X<final>:int=0}` and `c{X:=1}` | accepted | errors 3568, 3673, 3674, 3591: a `<final>` field set in an archetype or without a value, `<final>` on a module function, a final method that does not satisfy an interface | none | no | messages |
| redundant effects | 9 | `Tests/Effects.versetest:229`: `F()<transacts><reads>:void={}` | accepted | error 3565: an effect implied by another, on functions and on classes, interfaces and structs | none | no ([effect conformance](effect-conformance.md) refuses contradictory ones) | a message |
| effects of initializers | 8 | `Tests/GlobalVariables.versetest:86`: `c0 := class<allocates>{block{var X:int = 0}}` and `C0:c0 = c0{}` | accepted | 3582: a module constant whose initializer writes; link error 9003 (4 `verse_vm_only`) | 4 `verse_vm_only` | in part (#511) | a message |
| qualifiers | 8 | `Tests/QualifiedIdentifier.versetest:78`: `using{(A:)B}` | accepted | `(a:)F()` in an override where `(super:)` is meant (2003, 2004), `(c:)F()` recursion in an override (3506), a qualified `using` (3612) | none | no | messages |
| `<castable>` and parametric types | 7 | `Tests/Castable.versetest:54`: `class1(t:type) := class<castable> {}` | accepted | error 3678 | none | no | a message |
| interface inheritance | 7 | `Tests/Interface.versetest:92`: `C := class(T, T) {}` | accepted | 3592: an interface inherited twice directly; 3523: `<override>` in an interface | none | no | a message |
| comment lexing | 6 | `Tests/TimSyntax.versetest:45`: `#>` | accepted (a `#` comment) | a syntax error: `#>` with no `<#`, an unclosed `<#` after `<#>` | none | no | a message in the lexer |
| `<persistable>` structs | 6 | `Tests/persistable.versetest:43`: `struct1 := struct<persistable>:` with `X:any` | accepted | error 3662: a field type that cannot persist | none | no (persistable classes are refused) | a message |
| `defer` as a block's value | 5 | `Tests/FlowControl/defer.versetest:928`: a `defer:` ending a function body | accepted | error 3567 | none | no | a message |
| constructor-like functions | 5 | `Tests/Bugs/SOL-2577-ConstructorOverloadAmbiguity.versetest:3`: `c := class{}` and `c(I:int):c=c{}` | accepted | 3588/3532: a function named like a class, a local shadowing an overloaded function | none | no | a message |
| cyclic initializers | 4 | `Tests/CyclicReferences.versetest:11`: `X:int = X` | accepted; a `Main` that prints `X` stops with `limit: recursion depth` (exit 3) | error 3502; also `i:int = j` with `j:int = i`, and a module constant using one defined after it | none | no | a message: a dependency order over constants |
| other syntax | 3 | `Tests/Classes/ClassBlockClause.versetest:19`: `c:=class{x:int block{}}` | accepted | a syntax error (also `ReserveDotSpace.versetest:5, 6`) | none | no | parser messages |

## Refused where the tests expect a valid program

2,817 cases (2,710 test cases and 107 `:decls`). The cause is that of
openverse's first refusal: a case can hit several, so a count is the number
of cases a fix would get past their first obstacle, an upper bound on the
cases it would turn into agreements.

| Cause | Cases | Example | openverse | Marked | openverse documents it | Size |
|---|---:|---|---|---|---|---|
| path literals | 213 | `Tests/Literals/Path.versetest:24`: `"/a/b1"` (valid syntax) | parse error at `/` | none | no: `using{/Verse.org/…}` is accepted and ignored, paths elsewhere are not mentioned | parser form; 199 are parse-only tests |
| other syntax | 205 | `Tests/TimSyntax.versetest:301`: `"a;"` | parse errors of many kinds: Tim Sweeney's parser tests (59), comments between the tokens of a definition (`Roundtrip/Comments.versetest`, 14), `;` in argument lists, `of` and `at` calls, `case(Bar; Baz)`, `return(Self);` | 4 `verse_vm_only` | no | parser forms, many small ones |
| types as values | 166 | `Tests/Cast.versetest:69`: `assert{void(0)}` | `unknown function 'void'` | 10 `verse_vm_only` | in part: `t:subtype(…)` bounds of type parameters are supported, source upper bounds refused (#502) | front-end feature, and Core for `type` values: `subtype(t)`, `castable_subtype(t)`, `concrete_subtype(t)`, conversions `int(0)`, classes as values |
| empty and next-line bodies | 160 | `Tests/Bugs/FunctionWithoutExclamationPoint.versetest:1`: `C := class:` with only a comment in it | `expected the indented body of class C` (also `class<concrete>:` with nothing, `{` of a body on the next line) | none | no | parser form |
| bitwise functions | 159 | `Tests/Math/Bitwise.versetest:36`: `assert{BitNot(0) = -1}` | `unknown function 'BitNot'` | 62 `verse_vm_only` (unbounded ints), 13 `bp_vm_only` (runtime errors for shifts) | no; the Book's ch. 4, "Bitwise Operations" | Core and runtime: six `int` primitives, their Lean seams and C |
| character conversions | 140 | `Tests/Intrinsics/CharConversionExtensionMethods.versetest:21`: `0u00041.ToCodePoint() = 65` | `char32 has no method 'ToCodePoint'`; `unknown function 'ToChar'` | 2 `verse_vm_only` | no; the Runtime API reference documents `ToChar`, `ToChar32`, `ToCodeUnit`, `ToCodePoint` | built-in functions over existing values |
| union types | 137 | `Tests/Union.versetest:21`: `u:=union{U:u}` | parse error | all `verse_vm_only`; not in the Book's chapters | no | front-end and Core; low priority |
| attributes | 131 | `Tests/Attributes/Attributes.versetest:16`: an `@attribute` before a definition (valid syntax) | `unexpected character '@'` | 1 `verse_vm_only` | no; the Book's ch. 12 and 18 | parser form for built-in attributes; custom attributes (`class(attribute)`) a front-end feature |
| unnamed parameters | 123 | `Tests/Void.versetest:104`: `VoidInput(:void):int = 19` | `expected an identifier, found ':'` | 15 `verse_vm_only` | no; supported in function types (`type{_(:int):int}`), and the Book writes `F(:int):void = {}` (ch. 6) | parser form: a fresh name |
| qualified names | 102 | `Tests/Pointers.versetest:53`: `var (local:)result:int` | `expected an identifier, found '('` | none | in part: `(M:)F` and `(i:)M<override>` are supported ([Modules](../LANGUAGE.md#modules), [Overloading](../LANGUAGE.md#overloading)); `(local:)`, path qualifiers and qualified definitions are not | parser form and scoping |
| `comparable` as a type | 102 | `Tests/Comparable.versetest:3`: `Equal(X:t, Y:comparable)` | `unknown type 'comparable'` | 1 `verse_vm_only` | in part: only as a bound, `t:subtype(comparable)` | front-end and Core: a type of comparable values, as `any` is |
| other library functions | 94 | `Tests/Math/Math.versetest:188`: `assert{Clamp(1, -2, 2)=1}` | `unknown function 'Clamp'`; math functions as values (`CheckSpecials[Sin, NaN, NaN]`, 47 cases); `Sgn`, `GetCastableFinalSuperClass` (15), `GetSecondsSinceEpoch` | 15 `verse_vm_todo`, 4 `verse_vm_only` | in part: [the float API inventory](../LANGUAGE.md#scalar-math-api-inventory-490) (#490) | built-ins, and built-ins as function values |
| `ToDiagnostic` | 93 | `Tests/Intrinsics/ToDiagnostic.versetest:22` | `unknown function 'ToDiagnostic'` | 7 `verse_vm_only` | no | front-end and runtime: a `diagnostic` printer of every value |
| class and function specifiers | 83 | `Tests/Effects.versetest:304`: `c:=class<abstract>{F()<converges>:void}` | `<converges> is unsupported` (#494); `<castable>`, `<final_super>` (#11), `<persistable>`, `<native_callable>` | 71 `verse_vm_todo` (`GetCastableFinalSuperClass.versetest`) | yes: [effect contracts](../LANGUAGE.md#effect-contracts), #11 | front-end features, one each |
| other type rules | 66 | `Tests/Bugs/2021-09-03-OptionalTupleAssertionFailure.versetest:3`: `X:?tuple(int,int)=option{1,2}` | `expected ?tuple(int, int), found ?int` (see commas, above); also the `message` type, an overloaded function as a value, `Concatenate()` with no arguments, map keys of a sibling class, … | 8 `verse_vm_only` | no | each small |
| extension methods | 53 | `Tests/ExtensionFields.versetest:6`: `(I:int).Method()<computes>:int=I` | `expected an identifier, found '('` | none | no; the Book's ch. 6, "Extension Methods" | front-end feature |
| block forms | 51 | `Tests/TimSyntax.versetest:29`: `array:` and an indented `1,2` | parse errors: `spawn:`, `for:`, `option:`, `array:`, `map:` with indented blocks, `if{…}` with an empty `then {}` | 6 `verse_vm_only` | no | parser forms |
| comparisons of different types | 50 | `Tests/Operators/CompareString.versetest:14`: `assert{""<>array{0}}` | `'<>' compares values of different types, string and []int` | none | yes: Readings, "`=` between different types" | front-end: compare at the join type |
| live variables | 49 | `Tests/upon.versetest:7`: `upon(1){2}` | parse error | all `verse_vm_only`; the Book's ch. 15 is marked "Unreleased Feature" | no | front-end, Core and runtime |
| nested functions and lambdas | 47 | `Tests/NestedFunctions.versetest:41`: `G():int = X` inside `F` | `a definition in a module must start at the module body's column` | 25 `verse_vm_only`; the Book's ch. 6 marks nested functions "Unreleased Feature" | yes: [Not supported in v1](../LANGUAGE.md#not-supported-in-v1), [closure design](closure-design.md), #492 | front-end and Core (closures) |
| empty parentheses | 42 | `Tests/ClassifiableSubset.versetest:19`: `class<castable>()` | `expected a type, found ')'` | none | no | parser form |
| `if` without `then` | 41 | `Tests/FlowControl/If.versetest:111`: `if:` and an indented condition, no `then` | `expected 'then'` | 10 `verse_vm_only` | no | parser form |
| type aliases | 38 | `Tests/TypeAlias.versetest:206`: `a := int` and `b := ?a` | `unexpected '?'` | none | no; the Book's ch. 16 | front-end feature |
| nested tuple parameters | 37 | `Tests/NestedTupleParameters.versetest:8`: `F(A:int, (B:int, C:int), D:int)` | `expected an identifier, found '('` | none | noted as not covered in the [overloading audit](overloading-conformance.md) | parser form, lowered to tuple parameters |
| variance of parametric classes | 36 | `Tests/ParametricTypes.versetest:72`: a covariant `bivariant_class(sub_class)` passed as `bivariant_class(super_class)` | `expected bivariant_class(super_class), found bivariant_class(sub_class)` | none | no | front-end: variance from the positions of a parameter |
| `set` forms | 32 | `Tests/LiveVariables.versetest:122` | `expected '=' or a compound assignment in set`; `set` through a tuple element | 26 `verse_vm_only` | yes: the Mutation row | front-end |
| `. expression` forms | 31 | `Tests/Roundtrip/IfElse.versetest:21`: `if (a < b). c` | `expected ':' or '{', found '.'` | none | no | parser form |
| localization | 31 | `Tests/Bugs/SOL-3887-MessageArray.versetest:decls`: `SOL3887Message<localizes>(S:string) : message = "--{S}--"` | `unsupported function specifier <localizes>` (#494) | none | yes: [effect contracts](../LANGUAGE.md#effect-contracts) | front-end and runtime (`message` values) |
| archetype blocks | 29 | `Tests/Classes/Constructor.versetest:38`: `X := class1:` and indented fields | `a top-level definition must start at column 0` | 6 `verse_vm_only` | no | parser form |
| empty containers | 28 | `Tests/Operators/CompareString.versetest:29`: `assert{array{}=""}` | `the type of an empty array{} must be given` | none | yes: call packing needs "an inferable element type" | front-end: an element type from context, or a bottom element |
| overrides of fields | 24 | `Tests/Attributes/override.versetest:33` | `A<override> must give a new default`; a field narrowed by an override (`Data<override>:int` over `any`) | none | no | front-end |
| module constants of mutable classes | 21 | `Tests/Bugs/FORT-721882-CallingFunctionWithNullObject.versetest:14` | `the constant NullTestObject would hold an object with var fields …: make it a function` | 17 `verse_vm_todo` | yes, in the message | front-end and Core (module state) |
| joins | 19 | `Tests/Bugs/2021-04-26-DisjointTypesAllowedInComparisonAndPointerDeref.versetest:4`: `0=(false? or 0)` | `the branches have different types: logic and int` (also `?int` and `?float`) | none | in part: unrelated types join at `any` ([any](../LANGUAGE.md#any)), not inside options or `or` | front-end |
| class effect specifiers | 18 | `Tests/Attributes/allocates.versetest:6`: `c := class<computes><allocates> { Value:int = 0 }` | `<computes> excludes the heap effects … that class/interface also has` | none | yes: construction effects (#508) | a message |
| `spawn` in a failure context | 17 | `Tests/Bugs/FORT-582630-BranchResult.versetest:16` | `spawn cannot be in a failure context` (#156) | 1 `verse_vm_todo` | yes (#156) | exposed by the harness's `<decides>` wrapping; front-end |
| `weak_map` | 16 | `Tests/weak_map.versetest:32` | `unknown function 'weak_map'` | 1 `verse_vm_only` | yes: [Not supported in v1](../LANGUAGE.md#not-supported-in-v1), #491 | front-end and Core |
| non-ASCII char literals | 15 | `Tests/Roundtrip/Literals.versetest:63`: `'好'` | `a char literal must be ASCII: write U+597D as the char32 literal 0u597D` | none | yes: [Supported](../LANGUAGE.md#supported), Literals | lexer: such a literal is a `char32` |
| float literal suffixes | 14 | `Tests/Literals/Float.versetest:220`: `1.234f64` | `a float literal is digits, a point and digits, …` | none | no; the Book §1.4: `12.34f64`, "Explicit bit-depth suffix" | lexer |
| `var` specifiers and accessors | 14 | `Tests/Attributes/AccessLevelInheritance.versetest:444`: `var<private> Field<public>:int = 42` | `expected an identifier, found '<'` | none | no | parser and front-end |
| `true` and `false` as types | 12 | `Tests/Subtype.versetest:113`: `m0:subtype(true)` | `unknown type 'true'` | none | no; the Book's ch. 2 | front-end |
| `first` with generators | 11 | `Tests/FlowControl/first.versetest:202`: `first{I->X:array{10,20,30}; X > 15}` | parse error at `->` | none | in part: `first{c}`, `first(c){b}` ([Mutation, macros, tooling](../LANGUAGE.md#mutation-macros-tooling)) | parser form |
| operator definitions | 14 | `Tests/Bugs/2023-01-17-CharLiteralAsOperand.versetest:6`: `prefix'-'(Operand:char):char=Operand` used by `assert{-'a'}` | `expected '(', ':' or ':=' after 'prefix'` | none | no | parser and front-end (overloads exist) |
| ranges as values | 11 | `Tests/FlowControl/for.versetest:17`: `for(X:int=2 .. 3)` | `a range a..b can only be the source of a for clause` | none | no | front-end |
| subtyping into `any` | 9 | `Tests/Any.versetest:60`: `MapCount(Map)` with `Map:[int]string` for `[t]any` | `expected [t]any, found [int]string` | none | no | front-end |
| partial modules | 6 | `Tests/Modules/PartialModuleDefinitions.versetest:157`: `A<public> := module:` twice | `module A is defined twice` | none | no; the Book's ch. 16 | front-end |
| other brace forms | 6 | `Tests/Bugs/FORT-687100-Mix-comma-and-semicolon-in-archetype-instantiation.versetest:18`: archetype fields separated by both `,` and new lines | `expected ',' or '}'` | none | no | parser form |
| casts openverse proves impossible | 6 | `Tests/Cast.versetest:18`: `not i0[c0{}]` | `no class is below both c0 and i0, so i0[…] would always fail` | none | no | a message becomes a warning: the test expects a cast that fails |
| `<closed>` functions | 4 | `Tests/closed.versetest:16` | `unsupported function specifier <closed>` | 3 `verse_vm_only` | yes (#494) | front-end |
| comparable interfaces | 4 | `Tests/ComparableInterface.versetest:5`: `interface<unique>` compared | `… Interface is a class (only <unique> classes are comparable …)` | none | in part: [Classes](../LANGUAGE.md#classes), `<unique>` | front-end, small |
| named tuple elements | 3 | `Tests/Bugs/FORT-590869-NamedWithDefaultCoercion.versetest:9`: `Apply(G, (2, ?Y := 3))` | `unexpected '?'` | all `verse_vm_todo` | no | parser and front-end |
| type conversions | 3 | `Tests/Cast.versetest:59`: `logic(false)=false` | `expected '{', found '('` | none | no | parser form |
| function parameters of functions | 1 | `Tests/Function.versetest:144`: `f10(g(h(i:int, f:float):string):string)` | `expected ':', found 'h'` | none | no | parser form |

Sizes: *a message* is a check in the elaborator with information it already
has; *a parser form* is new syntax lowered to something the elaborator
already handles; *a front-end feature* needs new elaboration; *Core or
runtime* needs new Verse Core or C runtime operations.

## Ten causes to remove first

Ranked by cases moved per unit of risk. A count is the upper bound above;
"dangerous" marks a cause whose cases are accepted refusals or different
output, which matter more than their number.

1. **Reserved names (83 accepted refusals; a message).** Refuse as
   definition names the 65 names of `Tests/NamesReservedForFuture.versetest`,
   `_` (which the Book itself reserves), `subtype`, `castable_subtype`,
   `Self` and `local`, in the check that already reports "'X' is defined
   twice". Eight of openverse's own test programs define `first` or
   `repeat` (`tests/verse/clause_macros.verse`, …) and would be renamed.
   Dangerous, and the cheapest item here.
2. **One-line checks for the other dangerous acceptances (101 accepted
   refusals and 2 different outputs; messages).** Extend "defined twice"
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
3. **Path literals (213 refusals; a parser form).** Lex `/label@domain/…`
   as a path token in expression and qualifier position. `using{/…}`
   already takes paths; qualifiers such as `(/Verse.org/Verse:)int` can
   resolve to openverse's own names, and a path as a value can stay a
   refusal with its own message. 199 of the cases are parse-only tests,
   which need the parser change alone.
4. **Empty bodies and empty parentheses (202 refusals; parser forms).**
   Accept a class, struct, interface or module body of comments only (or
   nothing), a body brace on the next line, and `()` as an empty parent or
   type-parameter list. The elaborator already handles empty braced bodies
   (`class{}`), so these only reach it.
5. **Unnamed parameters (123 refusals; a parser form).** `F(:t)` binds a
   fresh name nobody can write. Function types already take unnamed
   parameters (`type{_(:int):int}`), and overload admission already
   compares positional domains, so `F(:int)` against `F(:void)` (the Book's
   own example) needs nothing new there.
6. **Character conversions (140 refusals; built-ins).** `ToChar`,
   `ToChar32` (failable), `ToCodeUnit`, `ToCodePoint`, `ToAsciiChar32`, in
   the table of built-ins that holds `ToString` and `Floor`, with the
   method-call form the array methods (`A.Find[x]`) already use.
7. **Block and dot forms (163 refusals; parser forms).** `if:` with a
   condition block and no `then` (41), `. expression` bodies (31),
   `spawn:`/`for:`/`option:`/`array:`/`map:` blocks (51), archetype blocks
   `X := c:` (29), generators in `first{…}` (11). Each desugars to a braced
   form the elaborator handles.
8. **Access specifiers (87 accepted refusals; a front-end feature).**
   Enforce `<private>`, `<protected>` and `<internal>` on members, fields
   and archetypes and refuse contradictory or misplaced ones, extending the
   module visibility check of [Modules](../LANGUAGE.md#modules). This
   retires a documented reading (Readings, access specifiers), so it is an
   owner decision; the tests give 87 exact oracles.
9. **Bitwise functions (159 refusals; Core and runtime).** `BitAnd`,
   `BitOr`, `BitXor`, `BitNot`, `BitShiftLeft`, `BitShiftRight` on `int`:
   new primitives next to the nine whose C is proved by QuickProof's
   `arith_exact` and whose Lean seams are in `Core/Seams.lean`. 84 untagged
   and 13 `bp_vm_only` cases could agree; the 62 `verse_vm_only` ones assume
   unbounded integers and would not under the BPVM reading.
10. **Attributes (131 refusals; a parser form, then a front-end feature).**
    Parse `@name` and `@name{…}` before a definition and accept the
    built-in ones (`@editable`, `@deprecated`, `@experimental`,
    `@available`) without meaning; custom attributes (`class(attribute)`)
    and their scopes come after.

Next in line: unreachable code (38 accepted refusals; a reachability pass),
extension methods (53; the Book's ch. 6), type aliases (38), nested tuple
parameters (37), the `ToDiagnostic` printer (93). The larger semantic
items, types as values (166) and `comparable` as a type (102), need Core
work and an owner's design; union types (137) and live variables (49) are
VerseVM-only or unreleased. The empty-values equality (30 different
outputs) is dangerous but changes Core equality: it needs an owner
decision first, as do the four documented readings the tests contradict.

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
  makes openverse read the next top-level definition as part of the class,
  and it reports "the program has no Main() function".

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

**Accepted: access specifiers** (87): `ArchetypeAccessSpecifiers.versetest` 15, 22, 36, 43, 45, 49; `Attributes/AccessLevelInheritance.versetest` 13, 23, 33, 43, 55, 67, 130, 676, 711, 751, 761, 787, 799, 811, 823, 835; `Attributes/intrinsic.versetest` 4, 5, 9; `Attributes/scoped.versetest` 91; `Bugs/SOL-5564-PublicOverrideOfDefinitionInNonPublicScope.versetest` 3; `Classes/AccessSpecifiers.versetest` 51, 62, 73, 85, 109, 132, 205, 212, 350, 355, 360, 364, 412, 413, 414, 415, 419, 420, 425, 426, 427, 438, 447, 451, 455, 458, 461, 464, 467; `InterfaceAccessVisibility.versetest` 9, 36, 37, 38; `Interfaces/AccessSpecifiers.versetest` 51, 62, 73, 85, 109, 132, 256, 261, 285, 286, 287, 288, 292, 293, 297, 298, 304, 305, 306; `Modules/Module.versetest` 36; `Modules/ModuleDefinitions.versetest` 129, 130, 315, 316; `ParametricTypes.versetest` 478, 1260, 1272

**Accepted: reserved names** (83): `Bugs/AssignmentToWhile.versetest` 3, 6; `NamesReservedForFuture.versetest` 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63, 65, 67, 69, 71, 73, 75, 77, 85, 87, 89, 91, 93, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 119, 121, 123, 125, 127, 129, 131, 133, 135, 137; `QualifiedIdentifier.versetest` 270; `Self.versetest` 22, 23; `Subtype.versetest` 230, 231, 232, 233, 234, 237, 238, 239, 240, 241, 242; `Union.versetest` 23(v), 290(v)

**Accepted: unreachable code** (38): `Bugs/SOL-4194-AssertOnMalformedCaseContainingDataDefinition.versetest` 20; `Enum.versetest` 356, 416, 436, 446, 466, 476, 496; `FlowControl/Case.versetest` 41, 154, 163, 172, 272, 280; `FlowControl/Reachability.versetest` 5, 11, 12, 13, 14, 15, 23, 39, 57, 76, 91, 99, 100, 107, 108; `FlowControl/Return.versetest` 115, 118, 148, 158, 159, 161, 162, 163, 179

**Accepted: failure where it is not allowed** (35): `Bugs/LogicalNot.versetest` 7; `Bugs/SOL-1987-IfDoesNotDetectNestedConditional.versetest` 22; `Bugs/SOL-4199-BreakFromIf.versetest` 80; `DefaultNamed.versetest` 820, 824, 844, 852, 853, 854, 859, 861, 862, 867, 868, 870, 875, 876, 877, 878; `Effects.versetest` 490, 537, 551, 552, 557(b), 558(b), 565(b), 573(v); `FlowControl/Case.versetest` 291; `FlowControl/for.versetest` 223; `Operators/LogicalNot.versetest` 13, 14, 15, 16; `Operators/LogicalOr.versetest` 143; `ParametricTypes.versetest` 465

**Accepted: misplaced specifiers** (30): `Attributes/FinalSuperAttribute.versetest` 38, 42, 46, 56, 58, 60, 64, 72, 74, 76, 78; `Attributes/abstract.versetest` 23, 44, 47, 57, 60, 63, 66, 69, 75, 78; `Attributes/concrete.versetest` 132, 137; `Attributes/final.versetest` 71, 114; `Castable.versetest` 12, 15, 24, 32, 35

**Accepted: duplicate definitions** (24): `Bugs/2020-04-22-ThreeDuplicateDefinitions.versetest` 17; `Classes/Class.versetest` 28; `Enum.versetest` 54, 121; `Interface.versetest` 74, 186, 187; `QualifiedIdentifier.versetest` 310, 315; `ShadowDefinition.versetest` 4, 271, 276, 281, 286, 291, 296, 328, 329, 331, 332, 336, 337, 340, 341

**Accepted: limits of Epic's compiler** (22): `Bugs/FORT-592189-MaybeCoerceToTypeCrash.versetest` 4(b); `Bugs/SOL-5477-CrashInGenClassDefinition.versetest` 5(b); `DefaultNamed.versetest` 629(b), 640(b); `Function.versetest` 238(b), 271(b); `Map.versetest` 45, 46, 223, 224, 249; `Operators/CompareMap.versetest` 58, 59, 71, 72; `ParametricFunctions.versetest` 496; `ParametricTypes.versetest` 324; `Tuple.versetest` 456(b); `WhereConstrainedInts.versetest` 97, 100; `persistable.versetest` 79, 91

**Accepted: other type rules** (19): `Attributes/InvalidAttributeLocations.versetest` 23; `Bugs/2023-01-18-FunctionParameterWithoutDomain.versetest` 12; `Bugs/FORT-744399-DefaultTupleFieldsCrashComplier.versetest` 62; `Bugs/SOL-5838-JoinOfClassesWithCommonBaseClassWithInterfaceInheritance.versetest` 13, 22; `Classes/Struct.versetest` 31; `DefaultNamed.versetest` 122; `Enum.versetest` 171(b); `FunctionTypes.versetest` 191; `Modules/Using2.versetest` 94; `Mutability.versetest` 426; `Option.versetest` 94; `ParametricFunctions.versetest` 348, 438; `ParametricTypes.versetest` 263, 265, 269; `QualifiedIdentifier.versetest` 152; `Void.versetest` 223

**Accepted: name limits of the BPVM** (19): `Bugs/FORT-555217-VeryLongIdentifier.versetest` 25(b), 31(b), 37(b); `Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest` 5(b), 11(b), 67(b), 73(b), 79(b), 85(b), 92(b), 98(b), 154(b), 160(b), 166(b), 172(b), 187(b), 193(b), 199(b), 205(b)

**Accepted: `<concrete>` classes** (17): `Attributes/concrete.versetest` 21, 25, 76, 84, 92, 214; `Bugs/SOL-3366-MakeClassesConcreteByDefault.versetest` 8, 15, 24, 33; `Bugs/SOL-7781-ConcreteClassDoesntEnforceDefaultValuesForInterfaceFields.versetest` 6, 16, 28, 41, 54; `Bugs/SOL-9745-ConcreteClassOverridingInterfaceDataMember.versetest` 28, 88

**Accepted: control forms** (17): `Coroutines/Concurrency.versetest` 832; `FlowControl/Break.versetest` 118, 161; `FlowControl/Return.versetest` 12, 114, 117; `FlowControl/for.versetest` 187, 193, 196, 202, 205, 208; `MacroForms.versetest` 20, 22, 23; `Modules/Using2.versetest` 86, 90

**Accepted: float literal out of range** (12): `Literals/Float.versetest` 246, 247, 248, 249, 250, 251, 252, 253, 255, 256, 257, 258

**Accepted: `<final>` members** (11): `Attributes/final.versetest` 11, 60, 61, 64, 80, 93, 94, 97, 105, 121, 125

**Accepted: redundant effects** (9): `Attributes/allocates.versetest` 10, 17, 24, 31; `Effects.versetest` 203, 229, 230, 231, 256

**Accepted: qualifiers** (8): `Bugs/SOL-3564-CallingSuperClassMethodFromOverriddenMethod.versetest` 7, 18, 32, 176; `QualifiedIdentifier.versetest` 78, 297; `Super.versetest` 183, 238

**Accepted: effects of initializers** (8): `Features/DefaultValueAssignment.versetest` 200, 215, 225; `GlobalVariables.versetest` 86(v), 90(v), 97(v), 105(v); `Modules/ModuleDefinitions.versetest` 279

**Accepted: `<castable>` and parametric types** (7): `Castable.versetest` 54, 57, 61, 72, 75, 79, 84

**Accepted: interface inheritance** (7): `Interface.versetest` 33, 40, 92, 194, 199; `InterfaceDiamond.versetest` 74, 89

**Accepted: comment lexing** (6): `TimSyntax.versetest` 45, 46, 47, 51, 52, 53

**Accepted: `<persistable>` structs** (6): `persistable.versetest` 43, 55, 59, 65, 70, 75

**Accepted: constructor-like functions** (5): `Bugs/SOL-2577-ConstructorOverloadAmbiguity.versetest` 3; `Classes/Constructor.versetest` 681; `Overloading.versetest` 166, 171, 252

**Accepted: `defer` as a block's value** (5): `FlowControl/defer.versetest` 928, 970, 981, 992, 1004

**Accepted: cyclic initializers** (4): `CyclicReferences.versetest` 11; `Features/DefaultValueAssignment.versetest` 102, 128; `Modules/ModuleDefinitions.versetest` 290

**Accepted: other syntax** (3): `Classes/ClassBlockClause.versetest` 19; `ReserveDotSpace.versetest` 5, 6

**Internal errors** (4): `Bugs/FORT-555213-DontSignedInt32OverflowInArrayBytes.versetest` 16; `FlowControl/Return.versetest` 11; `Operators/CompareString.versetest` 122; `Void.versetest` 300

**Different output: empty values are one value** (30): `Operators/BoolQuery.versetest` 3, 4; `Operators/CompareArray.versetest` 53, 54, 55, 56; `Operators/CompareBool.versetest` 13, 14, 15, 16, 17, 18; `Operators/CompareMap.versetest` 174, 175, 176, 177; `Operators/CompareOption.versetest` 17, 18, 19, 20; `Operators/CompareString.versetest` 139, 185, 186, 187, 188; `Operators/LogicalAnd.versetest` 29; `Operators/Precedence.versetest` 121; `Void.versetest` 199, 203, 285

**Different output: `int` precision** (26): `Intrinsics/Abs.versetest` 17(v); `Operators/BinaryAddInt.versetest` 35(v), 36(v), 37(v), 38(v), 65(v), 66(v), 67(v), 68(v); `Operators/BinaryDivInt.versetest` 49(v), 50(v); `Operators/BinaryMulInt.versetest` 49(v), 50(v), 52(v), 53(v); `Operators/BinarySubInt.versetest` 39(v), 40(v), 41(v), 42(v), 44(v), 45(v), 47(v), 48(v); `Operators/Negate.versetest` 14(v); `WhereConstrainedInts.versetest` 224(v), 227(v)

**Different output: rollback of a `for` iteration** (8): `FlowControl/for.versetest` 362, 371, 392; `Range.versetest` 140, 159; `SoftwareTransactionalMemory.versetest` 74, 81, 88

**Different output: `ToString` of a float** (7): `Intrinsics/FloatToString.versetest` 15, 18, 19, 21, 22, 23, 24

**Different output: commas and semicolons in blocks** (5): `FlowControl/for.versetest` 293; `Option.versetest` 44; `SemicolonsVsCommas.versetest` 76, 95, 100

**Different output: order of `set X op= e`** (4): `ArrayAppend.versetest` 7(v), 12(v), 140, 183

**Different output: key order of `ConcatenateMaps`** (2): `Intrinsics/ConcatenateMaps.versetest` 21, 33

**Different output: comments inside strings** (2): `Literals/String.versetest` 234; `Versions/v2/v2-CommentsAreIncludedInStringContents.versetest` 5

**Different output: comparison chains** (1): `Operators/Associativity.versetest` 9

**Different output: a parametric struct compared across instances** (1): `Operators/CompareStruct.versetest` 43

## Appendix B: totals per file

| | cases | agrees | disagrees-accepts | disagrees-refuses | wrong output | not translatable | internal error |
|---|---:|---:|---:|---:|---:|---:|---:|
| `Any.versetest` | 83 | 57 | 0 | 23 | 0 | 3 | 0 |
| `ArchetypeAccessSpecifiers.versetest` | 11 | 5 | 6 | 0 | 0 | 0 | 0 |
| `Archetypes.versetest` | 41 | 34 | 0 | 0 | 0 | 7 | 0 |
| `Array.versetest` | 22 | 12 | 0 | 10 | 0 | 0 | 0 |
| `ArrayAppend.versetest` | 27 | 8 | 0 | 10 | 4 | 5 | 0 |
| `AssetUsage/IncrementalAssetUsage.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `AssignmentSequencing.versetest` | 7 | 3 | 0 | 4 | 0 | 0 | 0 |
| `Attributes/AccessLevelInheritance.versetest` | 66 | 32 | 16 | 18 | 0 | 0 | 0 |
| `Attributes/AccessSpecifiersDisallowedOnLocalVars.versetest` | 9 | 9 | 0 | 0 | 0 | 0 | 0 |
| `Attributes/Attributes.versetest` | 34 | 21 | 0 | 11 | 0 | 2 | 0 |
| `Attributes/CustomAttributes.versetest` | 47 | 36 | 0 | 11 | 0 | 0 | 0 |
| `Attributes/CustomClassVarAccessors.versetest` | 61 | 14 | 0 | 18 | 0 | 29 | 0 |
| `Attributes/DeepMutabilityForCustomClassVarAccessors.versetest` | 19 | 0 | 0 | 1 | 0 | 18 | 0 |
| `Attributes/FinalSuperAttribute.versetest` | 25 | 7 | 11 | 7 | 0 | 0 | 0 |
| `Attributes/Internal.versetest` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |
| `Attributes/InvalidAttributeLocations.versetest` | 43 | 42 | 1 | 0 | 0 | 0 | 0 |
| `Attributes/abstract.versetest` | 19 | 8 | 10 | 1 | 0 | 0 | 0 |
| `Attributes/allocates.versetest` | 33 | 23 | 4 | 5 | 0 | 1 | 0 |
| `Attributes/available.versetest` | 77 | 7 | 0 | 13 | 0 | 57 | 0 |
| `Attributes/concrete.versetest` | 44 | 16 | 8 | 20 | 0 | 0 | 0 |
| `Attributes/deprecated.versetest` | 111 | 38 | 0 | 36 | 0 | 37 | 0 |
| `Attributes/experimental.versetest` | 47 | 1 | 0 | 0 | 0 | 46 | 0 |
| `Attributes/export_metadata.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Attributes/final.versetest` | 22 | 8 | 13 | 1 | 0 | 0 | 0 |
| `Attributes/intrinsic.versetest` | 7 | 4 | 3 | 0 | 0 | 0 | 0 |
| `Attributes/native.versetest` | 20 | 1 | 0 | 0 | 0 | 19 | 0 |
| `Attributes/override.versetest` | 16 | 12 | 0 | 4 | 0 | 0 | 0 |
| `Attributes/scoped.versetest` | 51 | 20 | 1 | 12 | 0 | 18 | 0 |
| `Attributes/unique.versetest` | 34 | 9 | 0 | 16 | 0 | 9 | 0 |
| `AutoQualification.versetest` | 29 | 0 | 0 | 0 | 0 | 29 | 0 |
| `BigArray.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-16-ForLoopIteratorVarScoping.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-21-CallMethodOnOptionalMember.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-21-DataMemberAttributeUseAfterFree.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-21-PassOptionalMemberAsNonOptional.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-22-ThreeDuplicateDefinitions.versetest` | 3 | 2 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-24-ArrayConcatIntoItself.versetest` | 5 | 2 | 0 | 2 | 0 | 1 | 0 |
| `Bugs/2020-04-24-AssignForIf.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-24-AssignmentOfVariableCrash.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2020-04-27-IndexOpPostfixedToMethodCall.versetest` | 5 | 1 | 0 | 4 | 0 | 0 | 0 |
| `Bugs/2020-04-27-NotAssigningReturnedArray.versetest` | 3 | 1 | 0 | 2 | 0 | 0 | 0 |
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
| `Bugs/2021-08-23-struct_in_struct_sol-1986.versetest` | 6 | 2 | 0 | 4 | 0 | 0 | 0 |
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
| `Bugs/2023-02-03-ClauseContainingOnlyComment.versetest` | 12 | 9 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/2023-02-03-DataDefinitionAsSubexpressionOfErroneousInvocation.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-03-ExponentialTimeRecursionCheck.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-03-PrintingCyclicFlowTypeForError.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-07-InvalidClassInstantiationClauseContainingDataDefinition.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-07-UnusedMapCoercion.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-08-MapMemoryLeak.versetest` | 12 | 0 | 0 | 12 | 0 | 0 | 0 |
| `Bugs/2023-02-20-UseAfterFreeWhenCoercingNestedStructsToDynamicallyTypedValue.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-02-22-NullDereferenceInResolveIdentifier.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-03-24-OverloadedFunctionMustBeInvoked.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2023-04-28-IncorrectNameMangling.versetest` | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/2024-12-02-VerseVMPropertyGeneratorGetOrCreateTupleTypeCrash.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/2026-01-26-FindFirstAsyncSubExprMissingOverrides.versetest` | 4 | 1 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/ArrayClassOf.versetest` | 2 | 1 | 0 | 0 | 0 | 1 | 0 |
| `Bugs/ArrayOrFailureResult.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/AssignmentToWhile.versetest` | 3 | 1 | 2 | 0 | 0 | 0 | 0 |
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
| `Bugs/FORT-555213-DontSignedInt32OverflowInArrayBytes.versetest` | 2 | 1 | 0 | 0 | 0 | 0 | 1 |
| `Bugs/FORT-555217-VeryLongIdentifier.versetest` | 6 | 3 | 3 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-559416-AddExtensionMethodsToForgotUsingMessage.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/FORT-571286-CrashMisinterpretingUObjectPointerAsDynamicallyTypedValue.versetest` | 8 | 3 | 0 | 5 | 0 | 0 | 0 |
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
| `Bugs/FORT-623803-STMRollbackAfterReturn.versetest` | 4 | 0 | 0 | 4 | 0 | 0 | 0 |
| `Bugs/FORT-635190-AssertIndexingContainerAfterRuntimeError.versetest` | 16 | 0 | 0 | 16 | 0 | 0 | 0 |
| `Bugs/FORT-642876-CollidingCoercedOverrideNames.versetest` | 11 | 0 | 0 | 11 | 0 | 0 | 0 |
| `Bugs/FORT-687100-Mix-comma-and-semicolon-in-archetype-instantiation.versetest` | 9 | 6 | 0 | 3 | 0 | 0 | 0 |
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
| `Bugs/FORT-951162-CantQualifyPropertiesOfParametricClasses.versetest` | 3 | 1 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-976754-GetterSetter.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/FORT-987013-MissingUploadedAtFNVersion.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/FORT-995029-CrashHashingDynamicallyTypedMapKey.versetest` | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/FunctionWithoutExclamationPoint.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/IteratingOverDataMemberArray.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/LogicalNot.versetest` | 2 | 1 | 1 | 0 | 0 | 0 | 0 |
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
| `Bugs/SOL-2577-ConstructorOverloadAmbiguity.versetest` | 1 | 0 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-2584-AbstractFunctionInModule.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-2620-AssignmentWithoutElement.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-2731-InvocationStructContext.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-2957-NullableObjectLocal.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3059-HeapBufferOverflowBugInArrayConcatenation.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3104-IncorrectFunctionQualificationCrashCompiler.versetest` | 4 | 3 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-3250-AssertionFailureWhenOverridingTheSameFunctionTwice.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3293-ConstructingAnInstanceWhileInitializingItsDefaults.versetest` | 4 | 3 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-3300-IncorrectCloningOfUniqueObject.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3366-MakeClassesConcreteByDefault.versetest` | 7 | 2 | 4 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-3422-CyclicInterfacesAndClasses.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-3515-CallingExtensionMethodWithoutSelf.versetest` | 3 | 1 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-3563-DontStackOverflowOnCyclicInterfaces.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
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
| `Bugs/SOL-3911-SuspendsArgumentAsForIterable.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-4107-StmWritesPoppedLocalVar.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4137-MemoryLeakCreatingA3dArray.versetest` | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/SOL-4170-DefinitionAstNodeUseAfterFree.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4171-CallStackOverflow.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4194-AssertOnMalformedCaseContainingDataDefinition.versetest` | 3 | 2 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4196-ErrCauseEnsureFailure.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-4199-BreakFromIf.versetest` | 10 | 8 | 1 | 1 | 0 | 0 | 0 |
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
| `Bugs/SOL-4527-CoercedInterfaceOverride.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-5386-CrashUsingSuperToCallOverrideInParametricClass.versetest` | 5 | 3 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-5452-NullDereferenceAfterRuntimeError.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-5477-CrashInGenClassDefinition.versetest` | 2 | 1 | 1 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5496-CaseCodeBlocksWithoutScopes.versetest` | 8 | 1 | 0 | 7 | 0 | 0 | 0 |
| `Bugs/SOL-5551-UsingTypeAlias.versetest.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5564-PublicOverrideOfDefinitionInNonPublicScope.versetest` | 3 | 0 | 1 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-5706-CompilerCrashWhenUsingSyncExpressionInCertainCircumstances.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5777-AutoRTFMForLoopCrash.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-5838-JoinOfClassesWithCommonBaseClassWithInterfaceInheritance.versetest` | 4 | 2 | 2 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5880-CrashOnArchetypeWithMixedCommasAndSemicolons.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/SOL-5951-AssertOnForAsArchetypeConstructionSubexpression.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5982-ConcatEqualsAndTransactions.versetest` | 10 | 10 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-5983-TypeSystemEscapeUsingFalse.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-6109-OverloadedFunctionNotUsed.versetest` | 3 | 2 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-6116-DiamondInheritance.versetest` | 2 | 1 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-6137-ConcurrencyMacrosNotIntroducingScope.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-6177-SubtypingIgnoresInheritedMembers.versetest` | 7 | 7 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-6529-WarnAboutAlwaysFailingContainerLookups.versetest` | 6 | 5 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-6739-ParametricTypeMeetAndJoin.versetest` | 25 | 9 | 0 | 16 | 0 | 0 | 0 |
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
| `Bugs/SOL-7579-LocalQualifierIsAllowedForMethodsInParametricClass.versetest` | 3 | 0 | 0 | 1 | 0 | 2 | 0 |
| `Bugs/SOL-7778_EnumeratorsAliasingReservedWords.versetest` | 24 | 1 | 0 | 4 | 0 | 19 | 0 |
| `Bugs/SOL-7781-ConcreteClassDoesntEnforceDefaultValuesForInterfaceFields.versetest` | 7 | 1 | 5 | 0 | 0 | 1 | 0 |
| `Bugs/SOL-7849-CannotAccessDataFieldsInParametricInterfaces.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Bugs/SOL-7898-DisambiguateSuperTypesByAccess.versetest` | 18 | 15 | 0 | 3 | 0 | 0 | 0 |
| `Bugs/SOL-8109-ParserStackOverflow.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-8137-AttributeLocalizesIsNotAllowedOnLocalVariables.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Bugs/SOL-8267-InterfaceDefaultsAreNotReinstantiated.versetest` | 6 | 0 | 0 | 5 | 0 | 1 | 0 |
| `Bugs/SOL-8302-CastableSubtypeFailsWithInterfaces.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Bugs/SOL-8380-InterfaceAccessorsNativeFailed.versetest` | 5 | 0 | 0 | 0 | 0 | 5 | 0 |
| `Bugs/SOL-8527-DefaultInitializerGlobalObject.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
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
| `Bugs/SOL-9745-ConcreteClassOverridingInterfaceDataMember.versetest` | 15 | 13 | 2 | 0 | 0 | 0 | 0 |
| `Bugs/SOL-9799-CaptureLocalUsing.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Bugs/TwoMethodsWithSameName.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/TypeFormerAsExpression.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Bugs/TypeSpecOnUnnamedParameter.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
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
| `Cast.versetest` | 65 | 46 | 0 | 19 | 0 | 0 | 0 |
| `Castable.versetest` | 101 | 32 | 12 | 39 | 0 | 18 | 0 |
| `Classes/AccessSpecifiers.versetest` | 61 | 19 | 29 | 0 | 0 | 13 | 0 |
| `Classes/Class.versetest` | 42 | 41 | 1 | 0 | 0 | 0 | 0 |
| `Classes/ClassBlockClause.versetest` | 24 | 16 | 1 | 0 | 0 | 7 | 0 |
| `Classes/Constructor.versetest` | 61 | 15 | 1 | 6 | 0 | 39 | 0 |
| `Classes/DataInheritence.versetest` | 3 | 1 | 0 | 2 | 0 | 0 | 0 |
| `Classes/IdentifierSuper.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `Classes/Inheritance.versetest` | 11 | 10 | 0 | 1 | 0 | 0 | 0 |
| `Classes/MethodInheritance.versetest` | 9 | 1 | 0 | 0 | 0 | 8 | 0 |
| `Classes/QualifiedMethodInheritance.versetest` | 23 | 20 | 0 | 3 | 0 | 0 | 0 |
| `Classes/SelfInheritance.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Classes/Struct.versetest` | 77 | 66 | 1 | 0 | 0 | 10 | 0 |
| `Classes/VarPointingToClass.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `ClassifiableSubset.versetest` | 36 | 8 | 0 | 28 | 0 | 0 | 0 |
| `CoercedOverrides.versetest` | 10 | 3 | 0 | 4 | 0 | 3 | 0 |
| `Comparable.versetest` | 49 | 7 | 0 | 42 | 0 | 0 | 0 |
| `ComparableInterface.versetest` | 17 | 12 | 0 | 5 | 0 | 0 | 0 |
| `CompatibilityConstraints.versetest` | 320 | 0 | 0 | 0 | 0 | 320 | 0 |
| `ComputationLimit.versetest` | 3 | 2 | 0 | 0 | 0 | 1 | 0 |
| `Coroutines/Concurrency.versetest` | 86 | 11 | 1 | 1 | 0 | 73 | 0 |
| `Coroutines/ConcurrencyEscape.versetest` | 49 | 0 | 0 | 0 | 0 | 49 | 0 |
| `Coroutines/Flow.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Coroutines/IteratedPrimitives.versetest` | 6 | 3 | 0 | 1 | 0 | 2 | 0 |
| `Coroutines/Loop.versetest` | 3 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Coroutines/ParamAlignment.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Coroutines/SelfCancel.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Coroutines/SpawnAndTask.versetest` | 77 | 5 | 0 | 2 | 0 | 70 | 0 |
| `CyclicReferences.versetest` | 13 | 12 | 1 | 0 | 0 | 0 | 0 |
| `DataMemberValidation.versetest` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |
| `DebugStackTrace/FrameOrder.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DebugStackTrace/Recursion.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DebugStackTrace/Spawn.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DebugStackTrace/When.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `DefaultNamed.versetest` | 142 | 106 | 19 | 7 | 0 | 10 | 0 |
| `Definitions.versetest` | 16 | 15 | 0 | 1 | 0 | 0 | 0 |
| `DigestGeneration.versetest` | 43 | 1 | 0 | 0 | 0 | 42 | 0 |
| `DigestVisibility.versetest` | 47 | 15 | 0 | 16 | 0 | 16 | 0 |
| `Duplication.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `DynamicallyTypedSubobjectInstantiation.versetest` | 16 | 16 | 0 | 0 | 0 | 0 | 0 |
| `Effects.versetest` | 336 | 245 | 13 | 11 | 0 | 67 | 0 |
| `Enum.versetest` | 71 | 50 | 10 | 7 | 0 | 4 | 0 |
| `EnumCompare.versetest` | 12 | 0 | 0 | 12 | 0 | 0 | 0 |
| `Escape.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `EvaluationOrder.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `Event.versetest` | 6 | 0 | 0 | 4 | 0 | 2 | 0 |
| `EventShouldBeCallable.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `Exercises/BalancedBinaryTree.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/BinaryTreeInorderTraversalRecursive.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/EpicProgrammingAssessmentBinarySearch.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Exercises/SameTree.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Exercises/TwoSum.versetest` | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
| `ExtensionFields.versetest` | 39 | 20 | 0 | 19 | 0 | 0 | 0 |
| `Failure.versetest` | 34 | 31 | 0 | 0 | 0 | 3 | 0 |
| `Features/DefaultValueAssignment.versetest` | 67 | 16 | 5 | 1 | 0 | 45 | 0 |
| `FlowControl/Break.versetest` | 17 | 15 | 2 | 0 | 0 | 0 | 0 |
| `FlowControl/Case.versetest` | 71 | 59 | 7 | 4 | 0 | 1 | 0 |
| `FlowControl/Concurrency/branch.versetest` | 10 | 4 | 0 | 1 | 0 | 5 | 0 |
| `FlowControl/Continue.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/If.versetest` | 94 | 62 | 0 | 32 | 0 | 0 | 0 |
| `FlowControl/IfDecidesErrors.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/Reachability.versetest` | 25 | 9 | 15 | 1 | 0 | 0 | 0 |
| `FlowControl/Return.versetest` | 86 | 61 | 12 | 11 | 0 | 1 | 1 |
| `FlowControl/Yield.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `FlowControl/defer.versetest` | 51 | 8 | 5 | 1 | 0 | 37 | 0 |
| `FlowControl/first.versetest` | 24 | 3 | 0 | 20 | 0 | 1 | 0 |
| `FlowControl/for.versetest` | 94 | 75 | 7 | 8 | 4 | 0 | 0 |
| `Function.versetest` | 81 | 59 | 2 | 3 | 0 | 17 | 0 |
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
| `IndistinctOverloads.versetest` | 20 | 17 | 0 | 3 | 0 | 0 | 0 |
| `IntAsRational.versetest` | 14 | 14 | 0 | 0 | 0 | 0 | 0 |
| `Interface.versetest` | 109 | 87 | 8 | 11 | 0 | 3 | 0 |
| `InterfaceAccessVisibility.versetest` | 19 | 8 | 4 | 0 | 0 | 7 | 0 |
| `InterfaceDiamond.versetest` | 18 | 16 | 2 | 0 | 0 | 0 | 0 |
| `InterfaceWithAccessors.versetest` | 6 | 3 | 0 | 3 | 0 | 0 | 0 |
| `InterfaceWithFields.versetest` | 37 | 13 | 0 | 23 | 0 | 1 | 0 |
| `Interfaces/AccessSpecifiers.versetest` | 41 | 15 | 19 | 0 | 0 | 7 | 0 |
| `Intrinsics/Abs.versetest` | 19 | 16 | 0 | 0 | 1 | 2 | 0 |
| `Intrinsics/ArrayFind.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayInsert.versetest` | 18 | 18 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayLength.versetest` | 14 | 10 | 0 | 4 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemove.versetest` | 26 | 24 | 0 | 2 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemoveAllElements.versetest` | 10 | 10 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemoveElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayRemoveFirstElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceAll.versetest` | 13 | 10 | 0 | 3 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceAllElements.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArrayReplaceFirstElement.versetest` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/ArraySlice.versetest` | 61 | 58 | 0 | 3 | 0 | 0 | 0 |
| `Intrinsics/CharConversionExtensionMethods.versetest` | 15 | 6 | 0 | 9 | 0 | 0 | 0 |
| `Intrinsics/CharToString.versetest` | 10 | 10 | 0 | 0 | 0 | 0 | 0 |
| `Intrinsics/Concatenate.versetest` | 25 | 19 | 0 | 6 | 0 | 0 | 0 |
| `Intrinsics/ConcatenateMaps.versetest` | 29 | 24 | 0 | 3 | 2 | 0 | 0 |
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
| `Literals/Float.versetest` | 176 | 116 | 12 | 14 | 0 | 34 | 0 |
| `Literals/Function.versetest` | 22 | 3 | 0 | 19 | 0 | 0 | 0 |
| `Literals/Int.versetest` | 166 | 166 | 0 | 0 | 0 | 0 | 0 |
| `Literals/Logic.versetest` | 36 | 34 | 0 | 2 | 0 | 0 | 0 |
| `Literals/Path.versetest` | 237 | 41 | 0 | 196 | 0 | 0 | 0 |
| `Literals/String.versetest` | 199 | 193 | 0 | 5 | 1 | 0 | 0 |
| `LiveVariables.versetest` | 56 | 12 | 0 | 44 | 0 | 0 | 0 |
| `Localization.versetest` | 40 | 12 | 0 | 28 | 0 | 0 | 0 |
| `LocalizationJoin.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `MacroForms.versetest` | 17 | 11 | 3 | 3 | 0 | 0 | 0 |
| `ManyEmergentTypes.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Map.versetest` | 104 | 80 | 5 | 19 | 0 | 0 | 0 |
| `MapOrder.versetest` | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| `Math/Bitwise.versetest` | 174 | 11 | 0 | 159 | 0 | 4 | 0 |
| `Math/Math.versetest` | 77 | 29 | 0 | 48 | 0 | 0 | 0 |
| `Math/MaxFloat.versetest` | 22 | 22 | 0 | 0 | 0 | 0 | 0 |
| `Math/MaxInt.versetest` | 13 | 13 | 0 | 0 | 0 | 0 | 0 |
| `Math/MinFloat.versetest` | 22 | 22 | 0 | 0 | 0 | 0 | 0 |
| `Math/MinInt.versetest` | 13 | 13 | 0 | 0 | 0 | 0 | 0 |
| `MetatypeConcreteSubtype.versetest` | 38 | 12 | 0 | 26 | 0 | 0 | 0 |
| `Modules/AccessSpecifiers.versetest` | 34 | 0 | 0 | 0 | 0 | 34 | 0 |
| `Modules/AssetAccessibility.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Modules/Import.versetest` | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| `Modules/Module.versetest` | 58 | 30 | 1 | 11 | 0 | 16 | 0 |
| `Modules/ModuleDefinitions.versetest` | 62 | 17 | 6 | 3 | 0 | 36 | 0 |
| `Modules/ModuleScopedInstances.versetest` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |
| `Modules/PartialModuleDefinitions.versetest` | 14 | 2 | 0 | 5 | 0 | 7 | 0 |
| `Modules/Using.versetest` | 22 | 1 | 0 | 0 | 0 | 21 | 0 |
| `Modules/Using2.versetest` | 9 | 3 | 3 | 0 | 0 | 3 | 0 |
| `Mutability.versetest` | 55 | 52 | 1 | 2 | 0 | 0 | 0 |
| `NamedParameterOverloads.versetest` | 36 | 35 | 0 | 1 | 0 | 0 | 0 |
| `NamedParamsFromNative.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `NamesReservedForFuture.versetest` | 69 | 4 | 65 | 0 | 0 | 0 | 0 |
| `NativeDeepMutability.versetest` | 19 | 0 | 0 | 0 | 0 | 19 | 0 |
| `NativePropertyRequiresNativeClass.versetest` | 6 | 0 | 0 | 0 | 0 | 6 | 0 |
| `NativePropertyRollback.versetest` | 15 | 1 | 0 | 13 | 0 | 1 | 0 |
| `NativePropertyWriteHook.versetest` | 10 | 0 | 0 | 0 | 0 | 10 | 0 |
| `NestedArrays.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `NestedFunctions.versetest` | 32 | 13 | 0 | 17 | 0 | 2 | 0 |
| `NestedNamedTupleParameters.versetest` | 24 | 3 | 0 | 13 | 0 | 8 | 0 |
| `NestedObjects.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `NestedTupleParameters.versetest` | 16 | 2 | 0 | 11 | 0 | 3 | 0 |
| `ObjectToJson.versetest` | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| `Operators/Associativity.versetest` | 16 | 15 | 0 | 0 | 1 | 0 | 0 |
| `Operators/At.versetest` | 15 | 3 | 0 | 12 | 0 | 0 | 0 |
| `Operators/BinaryAddArray.versetest` | 14 | 9 | 0 | 5 | 0 | 0 | 0 |
| `Operators/BinaryAddFloat.versetest` | 36 | 22 | 0 | 4 | 0 | 10 | 0 |
| `Operators/BinaryAddInt.versetest` | 43 | 32 | 0 | 1 | 8 | 2 | 0 |
| `Operators/BinaryAddString.versetest` | 16 | 14 | 0 | 2 | 0 | 0 | 0 |
| `Operators/BinaryArrow.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Operators/BinaryDivFloat.versetest` | 88 | 70 | 0 | 2 | 0 | 16 | 0 |
| `Operators/BinaryDivInt.versetest` | 34 | 32 | 0 | 0 | 2 | 0 | 0 |
| `Operators/BinaryMulFloat.versetest` | 48 | 33 | 0 | 2 | 0 | 13 | 0 |
| `Operators/BinaryMulInt.versetest` | 32 | 28 | 0 | 0 | 4 | 0 | 0 |
| `Operators/BinaryOps.versetest` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| `Operators/BinarySubFloat.versetest` | 26 | 12 | 0 | 4 | 0 | 10 | 0 |
| `Operators/BinarySubInt.versetest` | 28 | 20 | 0 | 0 | 8 | 0 | 0 |
| `Operators/BoolQuery.versetest` | 5 | 3 | 0 | 0 | 2 | 0 | 0 |
| `Operators/CompareArray.versetest` | 30 | 22 | 0 | 4 | 4 | 0 | 0 |
| `Operators/CompareBool.versetest` | 18 | 12 | 0 | 0 | 6 | 0 | 0 |
| `Operators/CompareFloat.versetest` | 52 | 50 | 0 | 0 | 0 | 2 | 0 |
| `Operators/CompareInstance.versetest` | 18 | 18 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareInt.versetest` | 36 | 36 | 0 | 0 | 0 | 0 | 0 |
| `Operators/CompareMap.versetest` | 97 | 78 | 4 | 11 | 4 | 0 | 0 |
| `Operators/CompareOption.versetest` | 18 | 14 | 0 | 0 | 4 | 0 | 0 |
| `Operators/CompareRational.versetest` | 4 | 3 | 0 | 1 | 0 | 0 | 0 |
| `Operators/CompareString.versetest` | 148 | 98 | 0 | 44 | 5 | 0 | 1 |
| `Operators/CompareStruct.versetest` | 36 | 30 | 0 | 1 | 1 | 4 | 0 |
| `Operators/CompareTuple.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `Operators/CompareTypeChecking.versetest` | 39 | 33 | 0 | 6 | 0 | 0 | 0 |
| `Operators/DisallowedOperatorDefinitions.versetest` | 30 | 30 | 0 | 0 | 0 | 0 | 0 |
| `Operators/LogicalAnd.versetest` | 9 | 8 | 0 | 0 | 1 | 0 | 0 |
| `Operators/LogicalNot.versetest` | 11 | 7 | 4 | 0 | 0 | 0 | 0 |
| `Operators/LogicalOr.versetest` | 90 | 74 | 1 | 15 | 0 | 0 | 0 |
| `Operators/Negate.versetest` | 6 | 5 | 0 | 0 | 1 | 0 | 0 |
| `Operators/Of.versetest` | 15 | 1 | 0 | 14 | 0 | 0 | 0 |
| `Operators/PostAt.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Operators/PostfixCallArray.versetest` | 16 | 11 | 0 | 3 | 0 | 2 | 0 |
| `Operators/PostfixCallMap.versetest` | 31 | 31 | 0 | 0 | 0 | 0 | 0 |
| `Operators/PostfixCallString.versetest` | 22 | 22 | 0 | 0 | 0 | 0 | 0 |
| `Operators/Precedence.versetest` | 68 | 67 | 0 | 0 | 1 | 0 | 0 |
| `Operators/PrefixStar.versetest` | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `Option.versetest` | 63 | 61 | 1 | 0 | 1 | 0 | 0 |
| `OutOfScopeOverloads.versetest` | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| `Overloading.versetest` | 79 | 61 | 3 | 9 | 0 | 6 | 0 |
| `PackageCycles.versetest` | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| `ParametricCastingIsDisallowed.versetest` | 11 | 7 | 0 | 4 | 0 | 0 | 0 |
| `ParametricFunctions.versetest` | 106 | 48 | 3 | 52 | 0 | 3 | 0 |
| `ParametricTypes.versetest` | 274 | 132 | 8 | 111 | 0 | 23 | 0 |
| `Parentheses.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `Path.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `PersistentJson.versetest` | 103 | 1 | 0 | 0 | 0 | 102 | 0 |
| `PersistentJsonSnapshot.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `PersistentJsonSnapshotMacro.versetest` | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| `PersonaJson.versetest` | 102 | 0 | 0 | 0 | 0 | 102 | 0 |
| `Placeholder.versetest` | 9 | 9 | 0 | 0 | 0 | 0 | 0 |
| `Pointers.versetest` | 66 | 43 | 0 | 23 | 0 | 0 | 0 |
| `PrintScriptCallstack.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `QualifiedIdentifier.versetest` | 88 | 31 | 6 | 35 | 0 | 16 | 0 |
| `Range.versetest` | 39 | 32 | 0 | 5 | 2 | 0 | 0 |
| `Rational.versetest` | 49 | 48 | 0 | 0 | 0 | 1 | 0 |
| `Recursion.versetest` | 47 | 47 | 0 | 0 | 0 | 0 | 0 |
| `ReentrantExceptions.versetest` | 3 | 0 | 0 | 1 | 0 | 2 | 0 |
| `Reference.versetest` | 4 | 1 | 0 | 0 | 0 | 3 | 0 |
| `ReserveDotSpace.versetest` | 14 | 3 | 2 | 9 | 0 | 0 | 0 |
| `ResolvingIdentifiers.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `RetryTransactionUnderAutoRTFM.versetest` | 12 | 0 | 0 | 0 | 0 | 12 | 0 |
| `RollbackMutablity.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `RollbackTortureTest.versetest` | 15 | 1 | 0 | 12 | 0 | 2 | 0 |
| `Roundtrip/Comments.versetest` | 96 | 75 | 0 | 20 | 0 | 1 | 0 |
| `Roundtrip/Definitions.versetest` | 13 | 12 | 0 | 1 | 0 | 0 | 0 |
| `Roundtrip/For.versetest` | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| `Roundtrip/IfElse.versetest` | 24 | 22 | 0 | 2 | 0 | 0 | 0 |
| `Roundtrip/KnownBugs.versetest` | 23 | 17 | 0 | 5 | 0 | 1 | 0 |
| `Roundtrip/Literals.versetest` | 48 | 45 | 0 | 3 | 0 | 0 | 0 |
| `Roundtrip/Newlines.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Roundtrip/Operators.versetest` | 43 | 39 | 0 | 4 | 0 | 0 | 0 |
| `RuntimeErrorCallstack.versetest` | 3 | 2 | 0 | 0 | 0 | 1 | 0 |
| `RuntimeErrors.versetest` | 13 | 1 | 0 | 4 | 0 | 8 | 0 |
| `RuntimeErrorsAutoRTFMCascadingAbort.versetest` | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| `RuntimeErrorsAutoRTFMLanguageAbort.versetest` | 11 | 0 | 0 | 0 | 0 | 11 | 0 |
| `RuntimeErrorsAutoRTFMRuntimeAbort.versetest` | 8 | 0 | 0 | 0 | 0 | 8 | 0 |
| `RuntimeWarningCallstack.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `SamplingProfiler.versetest` | 2 | 0 | 0 | 1 | 0 | 1 | 0 |
| `Self.versetest` | 17 | 7 | 2 | 8 | 0 | 0 | 0 |
| `SelfClass.versetest` | 8 | 8 | 0 | 0 | 0 | 0 | 0 |
| `SemicolonsVsCommas.versetest` | 56 | 32 | 0 | 19 | 3 | 2 | 0 |
| `Serialization/Array.versetest` | 193 | 0 | 0 | 0 | 0 | 193 | 0 |
| `Serialization/Comparable.versetest` | 75 | 0 | 0 | 0 | 0 | 75 | 0 |
| `Serialization/Function.versetest` | 7 | 0 | 0 | 0 | 0 | 7 | 0 |
| `Serialization/Map.versetest` | 236 | 0 | 0 | 0 | 0 | 236 | 0 |
| `Serialization/Option.versetest` | 168 | 0 | 0 | 0 | 0 | 168 | 0 |
| `Serialization/Scalar.versetest` | 203 | 0 | 0 | 0 | 0 | 203 | 0 |
| `Serialization/Struct.versetest` | 53 | 0 | 0 | 0 | 0 | 53 | 0 |
| `Serialization/Tuple.versetest` | 56 | 0 | 0 | 0 | 0 | 56 | 0 |
| `ShadowDefinition.versetest` | 65 | 22 | 15 | 6 | 0 | 22 | 0 |
| `SingleParamArray.versetest` | 16 | 13 | 0 | 3 | 0 | 0 | 0 |
| `SingleParamTuple.versetest` | 7 | 6 | 0 | 1 | 0 | 0 | 0 |
| `SoftwareTransactionalMemory.versetest` | 31 | 24 | 0 | 4 | 3 | 0 | 0 |
| `StmCallbackErrors.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `StringInterpolationPlus.versetest` | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| `Subtype.versetest` | 106 | 40 | 11 | 54 | 0 | 1 | 0 |
| `Super.versetest` | 32 | 24 | 2 | 1 | 0 | 5 | 0 |
| `TestSubobjectRenaming.versetest` | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| `TimSyntax.versetest` | 282 | 188 | 6 | 88 | 0 | 0 | 0 |
| `TransactionalTaskScope.versetest` | 7 | 0 | 0 | 7 | 0 | 0 | 0 |
| `Tuple.versetest` | 70 | 49 | 1 | 8 | 0 | 12 | 0 |
| `Type.versetest` | 37 | 28 | 0 | 9 | 0 | 0 | 0 |
| `TypeAlias.versetest` | 79 | 26 | 0 | 39 | 0 | 14 | 0 |
| `TypeChecking.versetest` | 53 | 50 | 0 | 3 | 0 | 0 | 0 |
| `TypeParam.versetest` | 15 | 1 | 0 | 14 | 0 | 0 | 0 |
| `TypeSpec.versetest` | 5 | 4 | 0 | 1 | 0 | 0 | 0 |
| `TypeValue.versetest` | 12 | 1 | 0 | 1 | 0 | 10 | 0 |
| `Union.versetest` | 252 | 105 | 2 | 138 | 0 | 7 | 0 |
| `UnsupportedNativeConstructor.versetest` | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `VarAccessSpecifiers.versetest` | 25 | 12 | 0 | 0 | 0 | 13 | 0 |
| `VarSet.versetest` | 31 | 28 | 0 | 2 | 0 | 1 | 0 |
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
| `Versions/v2/v2-CommentsAreIncludedInStringContents.versetest` | 1 | 0 | 0 | 0 | 1 | 0 | 0 |
| `Versions/v2/v2-NoOctalLiterals.versetest` | 70 | 1 | 0 | 0 | 0 | 69 | 0 |
| `Void.versetest` | 60 | 29 | 1 | 26 | 3 | 0 | 1 |
| `WebDataSyncService.versetest` | 5 | 1 | 0 | 2 | 0 | 2 | 0 |
| `Where.versetest` | 6 | 5 | 0 | 1 | 0 | 0 | 0 |
| `WhereConstrainedFloats.versetest` | 27 | 24 | 0 | 3 | 0 | 0 | 0 |
| `WhereConstrainedInts.versetest` | 53 | 39 | 2 | 10 | 2 | 0 | 0 |
| `await-regalloc-transactional-unification-variables.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `await.versetest` | 41 | 7 | 0 | 1 | 0 | 33 | 0 |
| `closed.versetest` | 5 | 4 | 0 | 1 | 0 | 0 | 0 |
| `generators.versetest` | 67 | 11 | 0 | 2 | 0 | 54 | 0 |
| `persistable.versetest` | 23 | 11 | 8 | 1 | 0 | 3 | 0 |
| `profile_simple.versetest` | 36 | 9 | 0 | 12 | 0 | 15 | 0 |
| `return-should-be-trailed.versetest` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `upon.versetest` | 13 | 5 | 0 | 8 | 0 | 0 | 0 |
| `using-local_scope.versetest` | 21 | 12 | 0 | 0 | 0 | 9 | 0 |
| `weak_map.versetest` | 96 | 18 | 0 | 27 | 0 | 51 | 0 |
| `when.versetest` | 22 | 7 | 0 | 15 | 0 | 0 | 0 |
