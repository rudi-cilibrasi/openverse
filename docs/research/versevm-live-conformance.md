# Live VerseVM conformance

## Reference targets

OpenVerse's target is Epic's Verse VM wherever it and the legacy Blueprint
VM (BPVM) disagree (the owner's decision, 2026-11-18). The compile-time
rules taken from the UEFN 43.12 results below (3512 `no_rollback`, 3519
concrete initializers, 3509 subtypes) come from the compiler front end
both VMs share.

The [Book of Verse's pinned Tests tree](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests)
contains 636 `.versetest` files. The Book's [development guide](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/DEVELOPMENT.md#refreshing-tests)
identifies it as a copy of the compiler's own suite and gives the original
test path in `fortniteMain`. OpenVerse's
[Book survey](book-test-conformance.md) runs translated cases against the
recorded expectations. In particular, `verse_vm_only` and `bp_vm_only`
identify different targets in that development corpus.

The checked-in baseline has 702 VerseVM-targeted records. Of those, 273
agree, 323 are refused by OpenVerse, none is accepted where the Book
expects a refusal (the four were the module-evaluation link errors, given
since #724), none produces different output and 106 cannot be translated
by the harness (with ints beyond 64 bits alone: 269, 323, 4, 0, 106; with
Epic's VM results alone: 223, 284, 0, 89, 106; on main `b640fa6d`, before
#724: 219, 284, 4, 89, 106). The other records are 585 BPVM-targeted (including
`verse_vm_todo`) and 12,217 with no target restriction recognized by the
harness. See the [baseline verdicts](../../tests/conformance/book/baseline.tsv)
and the harness's [target handling](../../tests/conformance/book/booktests.py).

There are two ways to get fresh Epic results:

- With access to Epic's `fortniteMain` development tooling, record its source
  revision and binary hash, then use the Book's `bin/vtest Tests --verbose`
  with `VERSE_TESTSCRIPT_VM` pointing to `VerseTestScriptCmdVM.exe`. Keep
  the Book revision with the output. See the Book's
  [runner setup](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/DEVELOPMENT.md#verse-vm-locations).
- For shipped behavior, use UEFN on Windows and record the exact editor and
  session build. Fortnite/UEFN 43.10 is the initial release target for these
  probes. The server launch option **Use Verse VM** is documented by Epic.
  [43.10 release notes](https://dev.epicgames.com/documentation/en-us/fortnite/43-10-fortnite-ecosystem-updates-and-release-notes)
  · [Verse Insights setup](https://dev.epicgames.com/documentation/fortnite/verse-insights-in-uefn)
  · [UEFN system requirements](https://dev.epicgames.com/documentation/fortnite/install-and-launch-fortnite-creative-and-unreal-editor-for-fortnite).

Live compiler results for UEFN 43.12 are below
([Epic observations](#epic-observations-uefn-4312-compiler)). The Linux workspace
has no Epic runner available. On November 17, 2026, the
pinned Book's `vtest Tests/ArrayAppend.versetest --verbose` reached process
launch and returned `ENOENT` for `VerseTestScriptCmdVM.exe`. The authenticated
GitHub API calls for `EpicGames/UnrealEngine` and `EpicGames/fortniteMain`
returned 404. The probe results below had no live Epic observations then;
the two compound-write probes have one since (below).

QEMU and KVM are available on this Linux host. A
[Windows evaluation guest](https://www.microsoft.com/en-us/evalcenter/evaluate-windows-11-enterprise)
could host the standalone runner if its executable and dependencies become
available. [Wine](https://manpages.ubuntu.com/manpages/noble/man1/wine-stable.1.html)
is another candidate for that runner. The UEFN route requires the Fortnite
client for playtesting, and Epic says the client cannot run in virtual
machines. [UEFN installation](https://dev.epicgames.com/documentation/fortnite/install-and-launch-fortnite-creative-and-unreal-editor-for-fortnite)
· [Epic's virtual-machine support statement](https://www.epicgames.com/help/c-34254770/c-38015632/a25107496).

UEFN also offers **Connect To Platform** for a console or phone signed in
with the editor's Epic account. That gives the playtest a separate client
if the editor works in a Windows guest. Editor startup and session launch
in this guest configuration still need verification.
[Epic's playtest instructions](https://dev.epicgames.com/documentation/en-us/fortnite/playtesting-your-island-in-unreal-editor-for-fortnite)
· [Epic's mobile instructions](https://dev.epicgames.com/documentation/fortnite/playtesting-on-mobile-devices-in-fortnite).

## Run the same probe bodies

The sources are under [tests/conformance/versevm](../../tests/conformance/versevm).
With a built OpenVerse checkout, run one probe in Lean and C:

```sh
probe=tests/conformance/versevm/signal-direct.verse
work=$(mktemp -d)
.lake/build/bin/openverse run "$probe" --emit "$work/probe.vbc"
runtime/build/cverse "$work/probe.vbc"
.lake/build/bin/openverse check "$probe" --signal-rollback
```

Run C after successful bytecode emission. Save stdout, stderr and exit status
for each command, together with the OpenVerse revision.

For UEFN, make one device source from the same body:

```sh
{
    cat tests/conformance/versevm/device.verse.header
    printf '\n'
    cat "$probe"
} > openverse_probe.verse
```

Use an empty private UEFN project with an instance of `openverse_probe` in
the level. Save the generated `Verse.digest.verse` build header and the
`event` and `signalable` declarations from that build. Build Verse Scripts
with one probe body at a time so a compile
error cannot hide another probe's result. Save the full diagnostic for each
rejected build. For admitted builds launch a session with **Use Verse VM**,
start the game, and save the ordered `OVPROBE` lines and any runtime
diagnostics. The wrapper marks entry and completion. Use a fresh game run
for every body. If the same build also offers BPVM, keep a second session's
results with its target and build ID. Epic describes the
[Verse Print log](https://dev.epicgames.com/documentation/en-us/fortnite/debugging-and-troubleshooting-in-verse).

## What to compare

| Probe | Observation to collect |
| --- | --- |
| `signal-control` | Direct signaling in a selected branch should reach the trace marker. |
| `signal-direct`, `signal-alias` | Compare failure-context admission for a direct call and a receiver alias. |
| `signal-interface`, `signal-bound` | Compare failure-context admission through a `signalable(int)` view and a bound method. Each has a paired `-control` outside a failure context. A failed control makes the corresponding effect test inconclusive. |
| `signal-generic` | Check whether a generic `<transacts>` helper can call `Signal`. Its paired `-control` calls the helper outside the failure context. |
| `signal-await` | If admitted, see whether the failed signal wakes the pending waiter with 1 or whether the later successful signal delivers 2. |
| `signal-subscribe` | If admitted, read callback state after a failed signal and then a successful signal. The paired control verifies subscription, callback dispatch and cancellation outside a failure context. |
| `compound-indexed-write` | After the right operand replaces the array, record the first row's length and first element. The Book's VerseVM-only case expects a single zero. [ArrayAppend case](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/ArrayAppend.versetest#L12) · [OpenVerse issue #704](https://github.com/rudi-cilibrasi/openverse/issues/704). |
| `compound-whole-write` | The whole-variable control replaces the target during the right operand in the same way. The Book's VerseVM-only case expects `[0, 42]`. Run both probes on the same target to check whether the result changes when the assignment selects an array element. [ArrayAppend control](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/ArrayAppend.versetest#L7). |
| `compound-nested-root`, `compound-nested-row` | Nested indices: the right operand replaces the variable, the element's row, or (a control) another row. Each header gives OpenVerse's output and the other reading's. [#704](https://github.com/rudi-cilibrasi/openverse/issues/704) |
| `compound-map-replaced`, `compound-struct-replaced`, `compound-operators` | The same rule for a map's entry, a struct's field (a struct variable, an array of structs), and `-=`, `*=`, float `*=` and `/=`. |
| `compound-replaced-length` | Whether the element is read from the replaced array or its replacement, when only one of them has it. |
| `compound-object-replaced`, `compound-object-field-array` | An object on the path: a variable holding it replaced, and an array in its field replaced. |
| `compound-root-append` | Whether `set X += …` in the right operand replaces `X`'s array or appends to it in place. |
| `compound-object-alias`, `compound-object-call`, `compound-object-task` | An array or struct in an object's field replaced through another name for the object, inside a called function, and by another task while the right operand is suspended. |
| `compound-object-nested`, `compound-object-in-place`, `compound-object-generic` | Rows in an object's field; writes into the field that replace nothing (controls); a generic class's and an interface's fields. |
| `compound-module-entry` | A module-scoped `weak_map(session, []int)` entry replaced by the right operand (Epic only: OpenVerse has no `session`). |
| `compound-plain-append`, `compound-index-appended` | Whether `set X = X + …` replaces `X`'s array, and whether an index is checked when the place is resolved or when the old value is read. |
| `compound-indexed-control` | Controls: a later failure undoes everything, the index runs once, and the update's value. |
| `int-overflow` | Add 1 to the maximum signed 64-bit integer and compare the result with that maximum. The marker is a fixed string because the Book documents separate limits on interpolating large integers. [Book of Verse integer rules](https://verselang.github.io/book/02_primitives/#integers). |

For [#515](https://github.com/rudi-cilibrasi/openverse/issues/515), the API
pages render `transacts`, `predicts`, `dictates` and `no_rollback` together
for both the concrete and interface methods. The compiler diagnostics and
runtime traces are needed to decide how a specific release admits the calls
and what it rolls back. [event.Signal](https://dev.epicgames.com/documentation/fortnite/verse-api/versedotorg/verse/event/event%28t%29/signal)
· [signalable.Signal](https://dev.epicgames.com/documentation/fortnite/verse-api/versedotorg/verse/signalable/signalable%28payload%29/signal).

## Epic observations (UEFN 43.12 compiler)

Every Epic result this page cites is also in two tables under
[`tests/conformance/versevm/results/`](../../tests/conformance/versevm/results):
`epic-43.12-compile.tsv` (215 compiler verdicts with their error codes and
messages) and `epic-43.12-runs.tsv` (166 session records: the probe's lines
on the Verse VM or the Blueprint VM, and the runtime error if any). They
are extracts of the raw MCP records, with the project's identifiers
replaced by `<project>`; the raw records are not in the repository.

UEFN 43.12, build `++Fortnite+Release-43.12-CL-60598086`, compiled each
probe body on 2026-11-18 through the editor's Build Verse Scripts, one body
at a time in the device wrapper above. A diagnostic's line there is 0-based
in the wrapped file: the header's 9 lines and a blank line come first, so
the body's 0-based line is the reported line minus 10. These are compiler
diagnostics, from the front end the Verse VM target shares with the BPVM.

| Probe | UEFN 43.12 compiler |
| --- | --- |
| `signal-control`, `signal-interface-control` | Admitted. |
| `signal-direct`, `signal-alias`, `signal-await` | Refused, error 3512 at the `Signal` in the condition: "This invocation calls a function (`(/Verse.org/Verse/event:)Signal`) that has the 'no_rollback' effect, which is not allowed by its context." |
| `signal-interface` | Refused, 3512, naming `(/Verse.org/Verse/signalable:)Signal`. |
| `signal-bound` | Refused, 3512 at `Send(1)`: "This invocation calls a function that has the 'no_rollback' effect, which is not allowed by its context." |
| `signal-generic`, `signal-generic-control` | Both refused, 3512 at the `Signal` in the `<transacts>` helper `Send`: a `<transacts>` function cannot call `Signal`, even when it is called outside every failure context. |
| `signal-bound-control` (first version) | Refused, 3502: coercing `Signal` from package `Verse` to `int->void` is unsupported; "Consider writing a wrapper function". Not the effect under test: the probe now binds a method of its own that signals. |
| `signal-subscribe` and its control (first version) | Refused, 3588: the field name `Last` is ambiguous with the built-in `.Last`. `signal-subscribe` also has 3512 at its condition's `Signal`. The field is now `Seen`. |
| `compound-indexed-write`, `compound-whole-write`, `int-overflow` | Admitted. |

The rewritten `signal-bound-control`, `signal-subscribe` and
`signal-subscribe-control` were compiled and run later, with the
[follow-up probes](#follow-up-probes): they now test what they intend. OpenVerse makes
the 3512 refusals its default (#515): see [OpenVerse
observations](#openverse-observations).

## Epic observations (Verse VM runs)

On UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086), in sessions launched
with **Use Verse VM** (the matchmaking ticket carried
`player.option.newVerseVm=true`), on 2026-11-18, every compound probe
below compiled and ran:

| Probe | Epic |
| --- | --- |
| `compound-indexed-write` | `length 1`, `first 0`, as `ArrayAppend.versetest:12` expects |
| `compound-whole-write` | `length 2`, `first 0`, `second 42`, as `ArrayAppend.versetest:7` |
| `compound-nested-root` | `row1 7 7` |
| `compound-nested-row` | `same row 9 9`, `other row 13 4` |
| `compound-map-replaced` | `entry 100 size 1` |
| `compound-struct-replaced` | `struct 50`, `array replaced 40`, `element replaced 70` |
| `compound-operators` | `minus 100`, `times 200`, `float times 4`, `float divide 8` |
| `compound-replaced-length` | `short failed 0`, `long ok 0` |
| `compound-object-replaced` | `old 6 new 100` |
| `compound-object-field-array` | `field 8 9` |
| `compound-root-append` | `rows 2 row0 4` |
| `compound-indexed-control` | `rolled back 3`, `index calls 1`, `value 5 rows 1 row0 1` |

The rule they give: the place is resolved before the right operand, and an
update whose container the right operand replaced (with a plain `set`) goes
to that container; `+=` appends in place. OpenVerse follows it since #704
([the rule](../LANGUAGE.md#mutation-macros-tooling)), and prints these
results for all twelve. The probes `compound-object-alias`,
`compound-object-call`, `compound-object-task`, `compound-object-nested`,
`compound-object-in-place`, `compound-object-generic`,
`compound-module-entry`, `compound-plain-append` and
`compound-index-appended` are not yet run on Epic; each header gives
OpenVerse's output and the other reading's.

`compound-module-entry` and `compound-object-in-place` were first refused
by Epic's compiler for their form, not their meaning: a condition continued
on a second line gave error 3100 (S88, "Expected expression, got "else" in
indented block") in one and "Unknown identifier" (3506) for the names it
defined in the other. Rewritten with one-line conditions and helper
functions, both are admitted and ran on the Verse VM (UEFN 43.12, CL
60598086, 2026-11-19 08:47Z): `entry 8 9`, and `element 1 51`,
`append 1 3 7`, `other object 1 3 8 9`. OpenVerse prints the same three
lines for `compound-object-in-place`, and `entry 8 9` for its own
module-scoped entries.

### Integers beyond 64 bits

Same build, sessions with **Use Verse VM** (issue #724; the raw records are
the comparer's `vm-all.json` and, for the Blueprint VM, `live-all-bpvm.json`):

| Probe | Verse VM | Blueprint VM |
| --- | --- | --- |
| `int-overflow` (`2^63 - 1 + 1` compared with `2^63 - 1`) | `above signed 64-bit max` | `ErrRuntime_MathIntrinsicCallFailure` (integer add overflow) |
| `book-int-mul-overflow`, `book-int-negate-min`, `book-int-abs-min`, `book-int-floor-div-min` | `above signed 64-bit max` | integer multiply, negate, abs overflow; `ErrRuntime_IntegerOverflow` (integer divide overflow) |
| `book-int-sub-below-min` | `below signed 64-bit min` | integer subtract overflow |
| `book-int-compound-add` (`set +=`) | `start`, `above signed 64-bit max` | `start`, integer add overflow |
| `book-int-bitwise-pow63` | `big computed`, `and zero`, `or unchanged`, `not negated` | integer add overflow |
| `book-int-where-i64` | `big computed`, `i64 cast failed` | integer add overflow |
| `book-int-cast-int` | `big computed`, `int cast succeeded` | integer add overflow |
| `book-int-interpolate-pow63` | `big computed`, then the session stops: `ErrRuntime_GeneratedNativeInternal` in `ToString(:int)`, "Value exceeds the range of a 64 bit integer." | integer add overflow |
| `book-int-pow64-module-const` | refused by the editor build: 9003, "Runtime error while evaluating module" (its log: "integer add overflow") | not built with the Verse VM off |
| `book-int-shift-63` | refused: 3506, unknown identifier `BitShiftLeft`, `BitShiftRight` | not built with the Verse VM off |

The rule they give: on the Verse VM, `int` arithmetic is exact past 64 bits,
a 64-bit refinement's cast compares exactly, and `ToString` of such an int is
a runtime error; a module's constants are evaluated in 64 bits when the
module is linked. OpenVerse follows it since #724
([LANGUAGE.md, int](../LANGUAGE.md#int)): every probe above prints the Verse
VM's lines in Lean and C (`book-int-cast-int` too, with #727's `int[X]`,
which succeeds for every int), and `book-int-pow64-module-const` is refused
at compile time. The longest int, 2^20 bits, is the
Book's (`Math/Bitwise.versetest`, `verse_vm_only`, "MaxLengthBits"), not yet
observed: UEFN 43.12 has no shifts, and the probes that reach it by
multiplication printed nothing there ([below](#follow-up-probes-for-ints)).

### Follow-up probes for ints

[`followup-int/`](../../tests/conformance/versevm/followup-int) asks what
the evidence above leaves open, one question per probe, each header saying
what OpenVerse prints (its `expectations.tsv` has the same in its `note`
column, with Epic's outcome and lines in `epic_outcome` and `epic_lines`).
UEFN 43.12 (the same build) compiled the first 19 one at a time
(2026-11-19 03:37Z; the raw records: `compile-int.json`) and ran the 16 it
admitted in Verse VM sessions (from 03:39Z), every session's ticket carrying
`newVerseVm=true` (`live-int-vm.json`; with "Auto Start Game" some records
repeat a run after its `end`, and only the first run counts). OpenVerse's
column is this branch, Lean and C agreeing.

| Probe | UEFN 43.12, Verse VM | OpenVerse |
| --- | --- | --- |
| `int-compound-mul` | `squared`, `minus one` | the same |
| `int-float-tie` | `tie to even`, `above tie up`, `odd tie up` | the same |
| `int-float-inf` | `big computed`, `infinity` | the same |
| `int-index-big` | `index failed`, `negative index failed`, `set failed` | the same |
| `int-range-big` | `count 4`, `two above` | the same |
| `int-map-key-big` | `found 2^63`, `found 2^126`, `one entry` | the same |
| `int-rational-big` | `floor 2^63`, `ceil 2^63 + 1`, `reduced` | the same |
| `int-where-natural-big` | `natural cast succeeded`, `negative cast failed` | the same |
| `int-module-const-back-control` | `max` | the same |
| `int-float-floor-big` | `before floor`, then `ErrRuntime_IntegerBoundsExceeded` in the native `Floor(:float)`: "The value 10000000000000000000.000000 cannot be converted to an integer because it does not fall inside the representable range of a Verse integer" | `before floor`, then the overflow error |
| `int-tostring-direct` | `in range`, then `ErrRuntime_GeneratedNativeInternal` in the native `ToString(:int)`: "Value exceeds the range of a 64 bit integer" | `in range`, then the overflow error |
| `int-literal-big` | refused, 3555 "Integer literal must be in the range -9223372036854775808 to 9223372036854775807" | refused |
| `int-module-const-back` | refused, 9003 "Runtime error while evaluating module" | refused at compile time (integer add overflow) |
| `int-div-zero-big` | no line: the first statement, `Quotient[2^63, 0]`, stops with `ErrRuntime_GeneratedNativeInternal` in the native `Quotient(:int,:int)`, "Value exceeds the range of a 64 bit integer" | `quotient failed`, `mod failed`, `floor failed`. **Differs** |
| `int-euclid-big` | no line: the same error in `Quotient`, at the first statement | `quotient -4`, `mod D - 1`, `floor -4`, `ceil -3`. **Differs** |
| `int-intrinsics-big` | `min max`, then the same error in the native `Clamp(:int,:int,:int)` | `min max`, `clamp`, `sgn`, `containers equal`. **Differs** |
| `int-module-const-call` | refused, 3582 "Divergent calls (calls that might not complete) cannot be used to define data-members", at the call of `Next`, a `<computes>` function | `above`. **Differs** |
| `int-length-max`, `int-length-over` | nothing, in three sessions each (`int-length-over` not even `half computed`), and no error reported; the game then left the startable state. Cause not known | `longest computed`, `longer than half`; `half computed`, then the overflow error |

What they settle: on Epic's Verse VM, ints past 64 bits go through the
operators, `set *=` and `-=`, comparisons, map keys, ranges, indices (which
fail), the conversion to a float (to nearest, ties to even, `Inf` past the
largest double), `Min`, `Max`, rationals and their `Floor` and `Ceil`, and
a one-sided refinement's cast; `Floor[F]` of a float and `ToString` of an
int stay 64-bit, with a runtime error; an int literal must fit in 64 bits.
OpenVerse prints the same for all of these.

The owner's decisions (#724), and the differences that remain:

- **Module constants in 64 bits: kept.** `int-module-const-back`, whose
  value is in range but whose evaluation leaves it, is refused with 9003,
  as `book-int-pow64-module-const` is: Epic evaluates a module's constants
  in 64 bits when it links the module. OpenVerse keeps its compile-time
  refusal of a module constant that leaves 64 bits, though it costs the 39
  Book cases that use `Pow2_64` in `Math/Bitwise.versetest`
  ([the survey](book-test-conformance.md#after-ints-beyond-64-bits)).
- **Native intrinsics limited to 64 bits: not imitated.** Epic's native
  `Quotient(:int,:int)` and `Clamp(:int,:int,:int)` stop with
  `ErrRuntime_GeneratedNativeInternal`, "Value exceeds the range of a 64 bit
  integer", when an argument is beyond 64 bits, even with a zero divisor.
  OpenVerse keeps computing the exact result (and fails on a zero divisor):
  a known difference where Epic's native intrinsics are limited to 64 bits.
  `ToString` is unchanged: the overflow error, as Epic's.
- **A module constant that calls a function**: Epic refuses it at compile
  time (3582); OpenVerse admits it and computes it at run time, with the
  Verse VM's ints. The rule is left to a separate change. Compile-only
  evidence from the same build, 2026-11-19 (08:29Z, `compile-3582.json`):
  `Limit:int = Min(Abs(-3), 7)` is refused with 3582 too,
  `Half:int = Floor(Base / 4) or 0` is admitted, and `<converges>` on a
  user function is refused (3565, "The 'converges' effect is only allowed
  on native functions").
- **The longest int**: `int-length-max` and `int-length-over` printed
  nothing on Epic, with no error. `int-length-steps` (2026-11-19 09:20Z)
  squares 2 twenty times, printing and yielding after each: Epic printed
  `step 1` to `step 19` and then nothing, no error and no end marker. So
  an int of 2^19 bits is computed, and the multiplication whose result
  would reach 2^20 bits does not return (the session then has to be
  replaced); OpenVerse raises the overflow error there. The two earlier
  probes never yield, and their lines before the stall were not delivered.

Added after these runs and run on Epic 2026-11-19 09:09Z to 09:16Z, one
call that might stop the session per probe, after a `before …` line, so
that an error hides nothing else. Epic agrees with OpenVerse on
`int-floor-div-zero-big`, `int-sgn-big`, `int-abs-big`,
`int-array-equal-big` and `int-tuple-equal-big`; in `int-mod-big` and
`int-mod-zero-big` its native `Mod(:int,:int)` raises the same internal
error as `Quotient` and `Clamp` ("Value exceeds the range of a 64 bit
integer"), the known difference above. OpenVerse's output, Lean and C
agreeing:

| Probe | Asks | OpenVerse |
| --- | --- | --- |
| `int-mod-big` | `Mod[N, D]` with `D = 2^63`, `N = -(3 D) - 1` | `before mod`, `mod D - 1` |
| `int-mod-zero-big` | `Mod[2^63, 0]` | `before mod`, `mod failed` |
| `int-floor-div-zero-big` | `Floor(2^63 / 0)` | `before floor`, `floor failed` |
| `int-sgn-big` | `Sgn(-2^63 - 1)` | `before sgn`, `sgn -1` |
| `int-abs-big` | `Abs(-2^63 - 1)`, an argument beyond 64 bits (`book-int-abs-min`'s, `-2^63`, is inside) | `before abs`, `abs 2^63 + 1` |
| `int-array-equal-big` | `array{2^63, 1} = array{(2^63 - 1) + 1, 1}`, `array{2^63} <> array{2^63 - 1}` | `before arrays`, `arrays equal`, `arrays differ` |
| `int-tuple-equal-big` | the same with tuples | `before tuples`, `tuples equal`, `tuples differ` |

### Fingerprint and Book probes ([#724](https://github.com/rudi-cilibrasi/openverse/issues/724))

The same build, the same day: Verse VM sessions had "Use Verse VM" on (the
ticket carried `newVerseVm=true`), Blueprint VM sessions had it off. The
lines are shown without the `OVPROBE` marker. Where the two VMs disagree,
OpenVerse follows the Verse VM (the owner's decision).

| Probe | Verse VM | Blueprint VM | OpenVerse before | OpenVerse now |
| --- | --- | --- | --- | --- |
| [`book-query-true-equals-false`](../../tests/conformance/versevm/book/book-query-true-equals-false.verse), [`book-query-and-value`](../../tests/conformance/versevm/book/book-query-and-value.verse), [`book-query-or-value`](../../tests/conformance/versevm/book/book-query-or-value.verse) | `query value equals false`, `and value equals false`, `or value equals false` | the same | `… differs from false`: `true?` was `true` | the VMs' and the Book's tests': `X?` of a logic succeeds with the empty value ([the rule](book-forms-rules.md#the-value-of-true)) |
| [`book-global-block-var`](../../tests/conformance/versevm/book/book-global-block-var.verse), [`-call-var`](../../tests/conformance/versevm/book/book-global-block-call-var.verse), [`-fn-var`](../../tests/conformance/versevm/book/book-global-block-fn-var.verse), [`-cond-var`](../../tests/conformance/versevm/book/book-global-block-cond-var.verse) | the editor builds them; the session's server cook (`linux-server-vm`) fails: `Script error 9003: Runtime error while evaluating module.` | `linked` | `linked` | the Verse VM's: refused before the program runs, naming the constant and the `var` ([the rule](../LANGUAGE.md#modules)) |
| [`book-global-block-cond-var-control`](../../tests/conformance/versevm/book/book-global-block-cond-var-control.verse) | `linked` | `linked` | `linked` | `linked` |
| [`vm-branch-outlives-return`](../../tests/conformance/versevm/fingerprint/vm-branch-outlives-return.verse) | `function returning`, `returned`, `branch body finished`, `branch cleanup`, `after wait` | `function returning`, `branch cleanup`, `returned`, `after wait` | the Blueprint VM's: the function's return cancelled its branch | the Verse VM's: a branch is a child of the task whose code started it, stopped when that task ends ([the rule](scheduler-conformance.md#a-branch-lives-as-long-as-its-task)) |
| [`vm-branch-await-after-return`](../../tests/conformance/versevm/fingerprint/vm-branch-await-after-return.verse) | `function returning`, `returned`, `branch received 7`, `signaled`, `after wait` | `function returning`, `returned`, `signaled`, `after wait` | the Blueprint VM's | the Verse VM's |
| [`vm-sleep-zero-yields`](../../tests/conformance/versevm/fingerprint/vm-sleep-zero-yields.verse) | `worker before sleep`, `main after spawn`, `worker after sleep`, `main after wait` | the same | `worker after sleep` before `main after spawn`: `Sleep(0.0)` completed at once (#608) | the VMs': `Sleep(0.0)` yields, a tick ([the rule](scheduler-conformance.md#sleep00-yields)) |

Follow-up probes for the shapes OpenVerse extrapolates from these
(branches and `rush` arms in spawned tasks, arms and branches; the order of
a task's defers and its children's; `Sleep` of a negative duration and of
zero within an update; a module constant whose own initialiser declares a
`var`) are in [`followup-conc/`](../../tests/conformance/versevm/followup-conc),
each with OpenVerse's output, the other reading and Epic's result in its
header, and in its `expectations.tsv` (`epic_outcome`, `epic_lines`). Run
`branch-at-entry-top-level` and `link-constant-own-var` alone: the first
leaves a branch to its device's `OnBegin`, the second may fail the cook.
On the Verse VM (the same build, "Use Verse VM" on, `newVerseVm=true`,
2026-11-19; nine in one batch, `branch-at-entry-top-level` alone, the two
refusals in the editor's build):

| Probe | Verse VM | OpenVerse |
| --- | --- | --- |
| [`branch-cancel-order`](../../tests/conformance/versevm/followup-conc/branch-cancel-order.verse) | `winner done`, `branch cleanup`, `arm cleanup`, `after race`, `after wait`: a cancelled task's child is stopped before the task's own defers run | had `arm cleanup` before `branch cleanup`; now Epic's ([the rule](../LANGUAGE.md#concurrency)) |
| [`branch-in-branch`](../../tests/conformance/versevm/followup-conc/branch-in-branch.verse) | `function returned`, `outer done`, `outer cleanup`, `inner cleanup`, `after wait`: a task that ends runs its defers, then stops its children | the same |
| [`branch-end-before-awaiter`](../../tests/conformance/versevm/followup-conc/branch-end-before-awaiter.verse), [`branch-in-race-winner`](../../tests/conformance/versevm/followup-conc/branch-in-race-winner.verse), [`branch-in-spawned-helper`](../../tests/conformance/versevm/followup-conc/branch-in-spawned-helper.verse), [`branch-in-sync-arm`](../../tests/conformance/versevm/followup-conc/branch-in-sync-arm.verse), [`rush-loser-outlives-return`](../../tests/conformance/versevm/followup-conc/rush-loser-outlives-return.verse) | as in their headers' first reading | the same |
| [`branch-at-entry-top-level`](../../tests/conformance/versevm/followup-conc/branch-at-entry-top-level.verse) | `begin`, `main returning`, `end`, `branch cleanup`, no `branch tick` in the 12 s after: stopped when the device's `OnBegin` ends | `main returning`, `branch cleanup` (stopped when `Main` ends) |
| [`sleep-negative-yields`](../../tests/conformance/versevm/followup-conc/sleep-negative-yields.verse) | `worker before sleep`, `worker after sleep`, `main after spawn`, `main after wait`: no yield | the same |
| [`sleep-zero-next-update`](../../tests/conformance/versevm/followup-conc/sleep-zero-next-update.verse) | `b after short sleep`, `a after three zero sleeps`, `main after wait`: each zero sleep waits for the next update | the same |
| [`branch-in-defer`](../../tests/conformance/versevm/followup-conc/branch-in-defer.verse) | refused, 3512: the `branch` macro's `suspends` effect is not allowed in a `defer` | refused (#156) |
| [`link-constant-own-var`](../../tests/conformance/versevm/followup-conc/link-constant-own-var.verse) | refused: 3512 (the `var`'s `allocates`, `Sum`'s `reads`), 3582 twice (side effects, divergent calls defining data-members) | refused (the constant allocates a `var`) |

The rule's open cases, a second batch the same day (same build, Verse VM,
`newVerseVm=true`):

| Probe | Verse VM | OpenVerse |
| --- | --- | --- |
| [`cancel-branch-before-sync-arms`](../../tests/conformance/versevm/followup-conc/cancel-branch-before-sync-arms.verse) | `winner done`, `arm two cleanup`, `arm one cleanup`, `branch cleanup`, `loser cleanup`, `after race`, `after wait`: the arms a cancelled task waits in go first, as its newest children | had `branch cleanup` first; now Epic's ([the rule](../LANGUAGE.md#concurrency)) |
| [`cancel-grandchild-order`](../../tests/conformance/versevm/followup-conc/cancel-grandchild-order.verse), [`end-grandchild-order`](../../tests/conformance/versevm/followup-conc/end-grandchild-order.verse) | a stopped child's own children first: `grandchild cleanup` before `child cleanup` | the same |
| [`cancel-two-children-order`](../../tests/conformance/versevm/followup-conc/cancel-two-children-order.verse), [`end-two-children-order`](../../tests/conformance/versevm/followup-conc/end-two-children-order.verse) | newest first: `second cleanup` before `first cleanup` | the same |
| [`cancel-spawned-not-child`](../../tests/conformance/versevm/followup-conc/cancel-spawned-not-child.verse) | the spawned task goes on: `spawned done`, `spawned cleanup` after `after race` | the same |
| [`cancel-sync-arm-child`](../../tests/conformance/versevm/followup-conc/cancel-sync-arm-child.verse), [`cancel-rush-child`](../../tests/conformance/versevm/followup-conc/cancel-rush-child.verse) | a cancelled `sync` arm's branch, a `rush` arm that went on, stopped before the defers of the task that is cancelled | the same |
| [`cancel-task-child`](../../tests/conformance/versevm/followup-conc/cancel-task-child.verse) | refused, 3593: ``(/Verse.org/Concurrency/task:)Cancel`` is `epic_internal` | admitted (`T.Cancel()`), a known difference |

A third batch (the same build, 2026-11-19 11:32 UTC) printed what OpenVerse
prints for `cancel-branch-before-race-arms` (a `race`'s arms as a
`sync`'s), `cancel-branch-in-and-before-sync-arm` (a branch started in an
arm is that arm's child) and `cancel-branch-before-nested-sync` (the arms
one call deeper still before the branch); the lines are in each header
and in `expectations.tsv`.

## OpenVerse observations

On the merge of #515's branch with main after #704, Lean and C agreed on
stdout, stderr and exit status for every probe below that produced
bytecode (the compound probes' outputs are in their headers and in
[Epic observations (Verse VM runs)](#epic-observations-verse-vm-runs)). The legacy column is
`--signal-rollback`, the transactional mode that was the default before
(and the previous table's `default`).

| Probe | Default outcome | With `--signal-rollback` |
| --- | --- | --- |
| `signal-control`, `signal-interface-control` | Print `selected` and `after`. | Same. |
| `signal-bound-control` (rewritten: a method of its own that signals, bound) | Prints `after`. | Same. |
| `signal-direct`, `signal-alias`, `signal-bound`, `signal-interface`, `signal-await` | Refused at the `Signal` in the condition, as 43.12 (3512). | Print `after`; `signal-await` prints `waiting`, then `received 2`. |
| `signal-generic`, `signal-generic-control` | Refused at the `Signal` in the `<transacts>` helper `Send`, as 43.12 (3512). | Print `after`. |
| `signal-subscribe` and its control (rewritten: the field is `Seen`) | `signal-subscribe` is refused at its condition's `Signal` only, as 43.12 (3512); the control prints `after success 2`, as the Verse VM does: `event` has `Subscribe` (#724). | `signal-subscribe` prints `after failure 0`, `after success 2`; the control as the default. |
| `compound-indexed-write` | Prints `length 1`, then `first 0`, as Epic does (#704). | Same. |
| `compound-whole-write` | Prints `length 2`, `first 0`, and `second 42`. | Same. |
| `int-overflow` | Runtime overflow, exit 2; since #724, `above signed 64-bit max`, as Epic's Verse VM prints. | Same. |

## Follow-up probes

[`followup/`](../../tests/conformance/versevm/followup) holds bodies, in the
same wrapper, for what the first 43.12 results left open. UEFN 43.12
(the same build) compiled them, with the three rewritten signal probes,
through BuildAll on 2026-11-18 (about 23:58Z), and ran the eight it admitted
in one Verse VM session (`newVerseVm=true`) on 2026-11-19 (00:02Z). L is the
diagnostic's 0-based body line. OpenVerse's column is this branch's default,
Lean and C agreeing wherever a program ran.

| Probe | UEFN 43.12 | OpenVerse |
| --- | --- | --- |
| `await-in-transacts` | 3512 L1: `(/Verse.org/Verse/event:)Await` has `no_rollback` | refused, `event.Await` has `no_rollback` |
| `concrete-abstract-child` | 3632 L3 "`concrete` classes must not be `abstract`"; 3519 for `B` | refused, 3632's reason |
| `constant-default-call` | 3582 L2 "Divergent calls (calls that might not complete) cannot be used to define data-members" | refused, the same: `Count` might not complete ([data members](#data-members-3582)) |
| `constructor-default-in-if` | 3512 L7: `MakeThing` has `no_rollback` | refused, the same |
| `decides-body-default-call` | admitted; prints `compiled` | `compiled` |
| `decides-plain-if` | 3512 L4: `Positive` has `no_rollback` | refused, the same |
| `default-into-default-type` | admitted; `result 1` | `result 1` |
| `for-filter-default-call`, `for-range-default-call` | 3512 L3 (`Value`, `Limit`) | refused, the same |
| `int-cast-variants` | 3509 L5 "Dynamic cast to `int` takes an int as its parameter, instead got any" | refused, the same reason |
| `join-if-common-base-interface`, `join-if-expected-interface` | 3510 L6: the body's value is an `any`, not a `super_class` / `named` | refused, the same reason |
| `join-interface-only` | admitted; `length 2` | `length 2` |
| `print-in-condition` | admitted; `(Rolling Back) printed in condition`, `after` (the raw log's label, which the batch runner strips) | `after`: openverse rolls the `Print` back with the failed condition and does not echo it. **Open** (#724): the Verse VM logs the line labelled as rolled back; [`followup-print/`](../../tests/conformance/versevm/followup-print) asks which lines get the label |
| `signal-class-block`, `signal-transacts-method` | 3512 L3, L4: `Signal` has `no_rollback` | refused, the same |
| `subscribable-event-control` | 3506 L7 "Unknown identifier `subscribable_event`" | `after success 2`: `subscribable_event` is an openverse extension, an `event` and nothing more (#724) |
| `subscribe-in-transacts` | admitted; `seen 4` | `seen 4`: `event` has `Subscribe` (#724) |
| `transacts-into-decides-type` | admitted; `result 1` | `result 1` |
| `signal-bound-control` (rewritten) | admitted; `after` | `after` |
| `signal-subscribe` (rewritten) | 3512 L10 at its condition's `Signal`, nothing else | refused at its condition's `Signal`, nothing else (#724) |
| `signal-subscribe-control` (rewritten) | admitted; `after success 2` | `after success 2` (#724) |

What they settle, now openverse's rules: a plain `<decides>` function has
`no_rollback`, and its body's top may call one that has it, while a failure
context inside it may not; a `for`'s range and filter are failure contexts;
constructors without specifiers have `no_rollback`; an event's `Await` has
it, `Print` and `Subscribe` do not; a `<transacts>` function is a value of a
`<transacts><decides>` type; an `if`'s branches of two classes with two
nearest common supertypes are an `any`, whatever is expected; a class below
a `<concrete>` one cannot be `<abstract>`; `int[X]` of an `any` is refused.
`Subscribe` is on `event` now (#724). The Verse VM logs a rolled-back
`Print`'s line with the label `(Rolling Back)`, while openverse's output is
transactional in Core and in the C runtime and echoes nothing (#724,
`followup-print/`).

### Subscribe follow-up probes

[`followup-event/`](../../tests/conformance/versevm/followup-event) asks
what the results above leave open about `Subscribe` (#724); each probe's
header gives what OpenVerse prints and the other readings, and its
`expectations.tsv` the Book's expectation, Epic's outcome and the
comparison. UEFN 43.12 (the same build, "Use Verse VM",
`newVerseVm=true`) compiled twelve and ran the eleven it admitted on
2026-11-19 (08:38Z). OpenVerse's column is after #724's fix, Lean and C
agreeing.

| Probe | Verse VM | OpenVerse |
| --- | --- | --- |
| `await-and-subscribe` | `awaiter 1`, `handler 1`, `after signal`, `after wait`: the awaiter goes on inside `Signal`, then the function | the same |
| `subscribe-from-awaiter` | `awaiter 1`, `late 1`, `after signal 1`, `late 2`, `after signal 2`: a function a resumed awaiter subscribes is called by that `Signal` | the same (before the fix, no `late 1`) |
| `subscribe-during-signal` | `first 1`, `first 2`, `added 2`, `after`: one a called function subscribes waits for the next `Signal` | the same |
| `cancel-during-signal`, `cancel-twice`, `same-handler-twice`, `nested-signal-in-handler` | one cancelled before its turn is skipped; a second `Cancel` does nothing; a function subscribed twice is called twice; a nested `Signal` runs depth first | the same |
| `subscribe-rollback`, `cancel-rollback` | `Subscribe` and `Cancel` in a failing condition are undone | the same |
| `event-unit-subscribe` | `event()` takes a function without parameters | the same |
| `subscribe-order` | `c 1`, `b 1`, `a 1`, `c 2`, `b 2`, `a 2`, `a 3`, `b 3`, `c 3`: the order varies between `Signal`s | subscription order. **Differs**, a documented difference: a program must not rely on the order |
| `sticky-event-subscribe` | refused, 3506 "Unknown identifier `sticky_event`" (it asks for `using { /Verse.org/Restricted }`) | admitted: `subscribed`, `sticky 2`, `after` |

So a `Signal` resumes its awaiters, then calls the functions subscribed
at that point. Two probes asked what that rule leaves open and ran on
the Verse VM at 09:43Z, both printing what OpenVerse prints:
`cancel-from-awaiter` (a subscription a resumed awaiter cancels is skipped
by that `Signal`: `awaiter 1`, `after signal 1`, `after signal 2`) and
`await-from-subscriber` (an await a called function starts is resumed by
the next `Signal`: `handler 1`, `after signal 1`, `waiter 2`, `handler 2`,
`after signal 2`).

### Data members (3582)

[`followup-3582/`](../../tests/conformance/versevm/followup-3582) holds the
probes of the rule behind `constant-default-call`, with their outcomes in
its `expectations.tsv`. UEFN 43.12 compiled the first eleven one at a time
(2026-11-18/19) and ran the three it admitted on the Verse VM
(`newVerseVm=true`, 2026-11-19). L is the diagnostic's 0-based body line;
Epic's span is the call's argument list.

| Probe | UEFN 43.12 | OpenVerse |
| --- | --- | --- |
| `div-const-intrinsic`: `Limit:int = Min(Abs(-3), 7)` | 3582 L2 at `Min`'s arguments, nothing for `Abs` | refused, `Min` might not complete (before #724: admitted, `limit 3`) |
| `div-const-constructor-fn`: a `<constructor>` function | 3582 L8 | refused, the same reason (before: it writes) |
| `div-const-method`: `Twice:int = Shared.Double()`, a `<computes>` method | 3582 L7, and 3512 L6 for `Shared:thing = thing{}` | refused at L6, 3512's reason |
| `div-const-constructor`: `Shared:thing = thing{}`, a class without specifiers | 3512 L5 "This archetype instantiation constructs a class that has the 'transacts' effect, which is not allowed by its context" | refused, the same reason |
| `div-const-converges`, `div-field-default-converges`: a function of the program's marked `<converges>` | 3565 L2 "The 'converges' effect is only allowed on native functions" | refused: `<converges>` is unsupported (#494) |
| `div-field-default-call`: `Size:int = Count()`, `Count` without specifiers | 3582 L5 | refused, the same reason (before: `Count`'s `no_rollback`, 3512) |
| `div-field-default-computes`: the same with `Count()<computes>` | 3582 L5 | refused, the same reason (before: #511's convergence) |
| `div-const-operator`: `Half:int = Floor(Base / 4) or 0` | admitted; `half 1` | `half 1` |
| `div-archetype-call`: `thing{Size := Count()}` in a function | admitted; `size 3` | `size 3` |
| `div-local-const-call`: a local `Limit:int = Count()` | admitted; `limit 3` | `limit 3` |

So a data member's definition (a module's constant, a field's default) may
call only a `<converges>` function, which only a native one may be: no
function, method or constructor of the program's, whatever its
specifiers. Of the built-ins, the operators and `Floor` of a rational are
admitted and `Min` is not; the Book's Runtime API reference, generated from
the Verse runtime of UE 6.0.0, declares `<converges>` on the compiler's
intrinsics (the operators, indexing, `Length`, `Abs`, `Floor` and `Ceil` of
a rational, `BitAnd` and its kin, `ConcatenateMaps`, the char conversions)
and on none of `Min` (written in Verse), `Sqrt`, `Quotient`, `ToString` and
the other natives. openverse takes that list
([the rule](../LANGUAGE.md#data-members-call-only-converging-functions));
the other twenty-one probes ask UEFN 43.12 about one construct each. It
compiled them on 2026-11-19 (10:40Z) and gave openverse's verdict on every
one, so the list is confirmed as far as they reach: 3582 for `Min`, `Sqrt`,
`Quotient`, `ToString`, `Floor` of a float, the interpolated int, `Min` in
a field default and the module-scoped `var`; 3512 for the struct's
archetype; 3502 ("Only <final> fields may be referenced from the default
value of a data member") for the default that reads a field of its own
object; the rest admitted. The constructs: `Abs`, `Min`, `BitAnd`, `Sqrt`, `Quotient`, `ToString`,
`Floor` of a float, an interpolated int, an array's `Length`, indexing and
`+`, archetypes of a `<computes>` class and of a struct, an enum value,
`option{…}`, a tuple, a map, a field default that reads another field of its
object (3502 in the Book's tests) or a field of another object, `Min` in a
field default, and a module-scoped `var` initialised by a call. openverse
admits the converging ones and refuses the others; it refuses the struct's
archetype for its `<transacts>` construction (#512) and the module-scoped
`var` because it has no `session`.

Eight more ask about the paths a call can take inside
a constant's definition, which openverse now notes wherever the call is
written (#724's follow-up to the rule): a `for` whose generator calls a
function with several values (`div-const-for-choice-call`, admitted by
openverse before the follow-up, and its control in a local constant), a
call in a `for`'s body and in an `if`'s condition, an operator the
program overloads, a call through a function value (with a control that
only names the function), all refused by openverse, and an archetype of a
`<computes>` class whose `block:` calls a function, which openverse
admits.

UEFN 43.12 compiled them on 2026-11-19 (15:00Z). It refuses the call in a
`for`'s body, in an `if`'s condition, the overloaded operator and the call
through a function value with 3582, and admits the control that only names
the function: openverse's verdicts. The two probes with a function of
several values are refused for another reason, 3101 "Infix `|` operator is
unimplemented": the shipped compiler has no choice operator, so the gap
closed here cannot be asked of it. The class whose `block:` calls a
function is refused with 9000, "Linker task graph contains a cycle"
(`_Root`, `thing`, `_Root`): a limit of Epic's linker, not a rule about
data members, and openverse keeps admitting it.

### The Book's accepted refusals

The survey's baseline (`0471c1d4`) has 74 cases where openverse runs a
program the Book's tests refuse (38) or gets another result (36). The 36
are `bp_vm_only` ints, the Blueprint VM's 64-bit overflow: settled, the
Verse VM's exact ints, by the int probes above (`int-overflow`,
`book-int-*`, `followup-int/`; the shifts of `Math/Bitwise.versetest`
194-200 by `book-int-shift-63`, UEFN 43.12 having no `BitShiftLeft`). None
of the 38 had been asked of Epic.
[`followup-book2/`](../../tests/conformance/versevm/followup-book2) asks
whether Epic's shipped compiler refuses each of them, one construct per
probe, with controls; each header gives the Book's case and openverse's
output, Lean and C agreeing, and its `expectations.tsv` the same, with
Epic's results. UEFN 43.12 (`++Fortnite+Release-43.12-CL-60598086`)
compiled each alone with BuildAll on 2026-11-19 (~13:10Z; raw records
`compile-book2.json`) and refused every probe of an accepted refusal; it
admitted the 15 controls and `interface-var-field`, which then ran on the
Verse VM (`newVerseVm=true`, 14:41Z, `live-book2-vm.json`;
`long-ident-class-1024-control` alone, in single mode, 14:44Z) and printed
what openverse prints. So each refusal is the form's under test:

| Probes | Book cases | Asks whether UEFN 43.12 refuses | UEFN 43.12 |
| --- | --- | --- | --- |
| `case-collision-*` (4 and a control) | `FORT-793952…` (16, `bp_vm_only`, 9200, 9002, 9000) | names of one scope that differ only in case: module functions, methods, `<suspends>` methods, the same parameters | refuses all four: 9200 "Found multiple functions that map to the same target function. Please rename the function to be case insensitive unique" (module functions, methods), 9002 and 9200 (`<suspends>` methods: "Found existing type 'task_cc$Function'"), 9000 twice (the same parameters: "Local variable `Value` not found internally in VM"); admits the control |
| `long-ident-*` (4 and a control) | `FORT-555217…` 25, 31, 37 (`bp_vm_only`, 9002, 3655); 11 (3655, both VMs, agreeing only for another reason) | a class name of 1024 characters, a mangled method name too long, a name of 1025, one of 4096 | refuses a name of 1025 and one of 4096 characters, 3655 "Identifier is too long" at each occurrence, the mangled method name, 3655 at the method, and the class of 1024 characters, 9002 "Cannot find class"; admits the class of 960 |
| `join-named-*`, `join-generic-effects-*`, `generic-higher-order`, `parametric-method-value`, `interface-fn-param-generic` (8 and 7 controls) | `DefaultNamed` 629, 640, 741, 751; `Tuple:456`; `Function` 238, 271; `ParametricFunctions:276`; `FORT-592189:4`; `SOL-5477:5` (all `bp_vm_only`, IR error 3502; their Verse VM twins valid) | the Blueprint VM's code generation limits on function values: joins of functions with named or defaulted parameters, joins of generic functions with other effects, generic functions passed as values, a parametric class's method as a value, a function parameter in a parametric interface | refuses all eight, 3502 "Using a value of type … as a value of type … is not yet implemented"; admits the seven controls (left to another change) |
| `overload-tuple-named-call` and its control | `FORT-744399:62` (3509, both VMs) | two arguments packed into a tuple parameter beside a named one | refuses it, 3509 "This function parameter expects a value of type tuple(tuple(float,float),?E:float = ...), but this argument is an incompatible value of type tuple(type{1.000000},type{2.000000})"; admits the control |
| `parametric-var-where-*`, `parametric-interface-var`, `interface-var-field` (3 and 3 controls) | `ParametricFunctions` 431, 438 (3552), 496 (3502), both VMs | a parametric class's `var` field used in a generic function; a parametric interface with a `var` field | refuses the two generic functions, 3552 "An implicit type parameter (`t`) used in the type of mutable data (`…/c.Data`) may not be used in the type of a function", and the interface, 3502 "Mutable members in parametric interfaces are not yet implemented"; admits the three controls |
| `enum-wide` and its control | `Enum:171` (`bp_vm_only`, 3552) | an enum of 257 values | refuses 257 values, 3552 "Enumerator value `wide.e100` is out of byte-range which is not yet supported"; admits 256 |
| `final-method-interface`, `-nonfinal`, `-control` | `Attributes/final.versetest:125` (3591, both VMs) | a class's `<final>` method (and, not a Book case, one that is not `<final>`) taken for an interface's method of its name | refuses both, `<final>` or not, 3591 "Non-abstract class inherits abstract function `MethodX` from `i_y` but does not provide an implementation"; admits the control |
| `spawn-in-transacts-*` (4 and a control) | `Effects` 557, 565, `SoftwareTransactionalMemory:505` (`bp_vm_only`, 3512) | `spawn` in a `<transacts>` and a `<transacts><decides>` function, and whether a failed condition undoes the spawn (openverse undoes it) | refuses all four, 3512 "This 'spawn' macro has the 'no_rollback' effect, which is not allowed by its context" (in the `<transacts><decides>` ones, also 3512 for the call of `Work`, which has `no_rollback`); admits the control |
| `live-when-sentinel`, `live-upon-sentinel`, `live-await-block-sentinel` | `when:7`, `upon:7`, `await:6` (`verse_vm_only`, valid) | whether 43.12 knows `when`, `upon` and `await{…}` (it refuses `live`, `book-live-set`); openverse refuses all three | refuses all three, 3506 "Unknown identifier `when`", `upon`, `await` |

Build the `long-ident-*` probes alone, in single mode: Epic's names for
them may depend on the module that holds them.

openverse takes these refusals (#724; [the survey](book-test-conformance.md#after-epics-verdicts-on-the-accepted-refusals)):
names of one scope's functions that differ only in case with the same
parameters (9200), identifiers past 1024 characters (3655) and class
names past 1023 (9002), enums past 256 values (3552), an interface's
abstract method implemented only below the interface (3591), no packing
of several arguments into a tuple parameter beside a named one (3509),
`spawn`'s `no_rollback` (3512), and the parametric `var` fields (3552,
3502), with `--parametric-var-fields` to keep openverse's extension (32
of openverse's test programs and 4 error tests take it). Not taken: a
method's mangled name with parameters (its limit counts names openverse
does not have). The function-value coercions (3502) are refused since
#735 ([below](#function-value-coercions-3502)), so the eight such probes of
`followup-book2` are refused by openverse as by Epic.

[`followup-book3/`](../../tests/conformance/versevm/followup-book3) asked
the edges the evidence left open, one construct each: names differing
only in case under other parameter names, beside a named parameter, in a
subclass, as two classes, a function and a constant, an interface's
methods; long names; an interface default beside a class's method of its
name; mutable data through another class's field, in a body, in a field
not of the parameter; the named argument given, an array parameter
beside a named one, packing without one; a spawn in a condition, in a
class's `block:`, at the top of a plain `<decides>` body. UEFN 43.12
compiled them one at a time on 2026-11-19 (~16:45Z, `compile-book3.json`):
13 as openverse had them; it refused two classes whose names differ only
in case (9002, "Found existing type 'CC' that is already being created
this compile"), an interface's two such methods (9200), an array of
several arguments beside a named parameter (3509), mutable data through a
class's field (3552), and the long names, which a bisection on the same
build then measured, for definitions without parameters:

| What | Longest admitted | Shortest refused |
| --- | ---: | ---: |
| a field of a class, a local constant | 1004 | 1005 |
| a module function | 990 | 991 |
| a class with a field only | 1023 | 1024 (9002) |
| that class with a method `F()` | 983 | 984 |
| a method in a class `holder` | 981 | 982 |
| a struct | | 1024 (9002, "Cannot find struct"); a struct name of 1016 characters crashed the editor |

openverse follows all 22 since (the length limits as constants citing
these measurements). [`followup-book4/`](../../tests/conformance/versevm/followup-book4)
asks the edges of those rules: two structs, interfaces, enums, a class
and a struct, an interface or an enum of case-different names (refused by
openverse), a class and a function so named, a class in a module and one
at the top level (admitted); a generic parameter beside a named one
(admitted, packed into a tuple); a method and a module function with a
parameter at the measured limits, a parameter and a module constant of
1005 characters, an interface and an enum of 1023; mutable data through a
struct's field (admitted), in an array type and a method's own type
parameter (refused). UEFN 43.12 compiled them on 2026-11-19 (~19:55Z,
`compile-book4.json`): 13 as openverse had them, the six type collisions
among them (9002, "Please rename the struct/interface/enumeration to be
case insensitive unique"). It refused mutable data through a struct's
field (3552) and admitted a parameter of 1005 characters, which openverse
now follows; it refused a function of 990 characters and a method whose
names make 977, each with one parameter (3655), which openverse admits, a
known difference (a parameter lowers the limit, not modelled); and it
refused `generic-param-named-pack` for its form (the default `0 where
t:type` read as one expression: 3502, 3506), so that probe was
rewritten, `F(X:t, ?E:int where t:type)` called `F(1, 2, ?E := 5)`, which
it refuses (3509, "This function parameter expects a value of type
tuple(any,?E:int)", ~20:40Z, `compile-book4b.json`): openverse packs no
several arguments into a generic parameter beside a named one since.

Of the 323 refusals of `verse_vm_only` cases, all but one are of forms
UEFN 43.12 refuses too, or that the sentinels above ask: `union` (138: the
cause's 136 and 2 counted under others; `book-union-equality`), live
variables (90: `live-variables` 57, `set-forms` 28, 3 of `metatypes`, 2
`when` cases of `syntax-other`; `book-live-set` and the sentinels),
module constants beyond 64 bits (39, `book-int-pow64-module-const`),
nested functions (26, `book-nested-function`), `<closed>` functions as
types (6, `book-closed-function-type`), and the `spawn`, function-join,
sibling-key, default-cycle, field-tuple, `branch`-in-a-loop and
type-parameter forms of the `book/` probes (23). Left unasked: a generic
function joined with another (`Castable.versetest:601`).


### Function-value coercions (3502)

UEFN 43.12 compiled the eight function-value probes of
[`followup-book2`](../../tests/conformance/versevm/followup-book2) and their
seven controls one at a time (2026-11-19; L is the diagnostic's 1-based
body line). It refused every probe with error 3502 and admitted every
control:

| Probe | UEFN 43.12 | Control, admitted |
| --- | --- | --- |
| `join-named-default-fn` | L14, both branches: "Using a value of type (?A:int = ...)->int as a value of type tuple()->int is not yet implemented" (and ?B's) | `F:type{_():int} = F2` |
| `join-named-default-param` | L16, both branches: "((?A:int)->int)->int as … (tuple(?A:int = ...,?B:int = ...)->int)->int" | `F1(F9)` |
| `join-named-tuple` | L14, the branch with the default only: "tuple([]char,?Y:int = ...)->[]char as … []char->[]char" | the function at the type alone |
| `join-generic-effects-decides` | L15, `Identity`'s branch only: "type{_(:int)<computes>:int} as … type{_(:int)<computes><decides>:int}" | `F:… = Identity` |
| `join-generic-effects-transacts` | L15, both: "type{_(:int)<computes><decides>:int} as … type{_(:int)<transacts><decides>:int}", and `<transacts>` as `<transacts><decides>` | `F:… = TransactsIdentity` |
| `generic-higher-order` | L18-21, each of the eight arguments: "type{_(:type{_(:t)<transacts>:t},:t where t)<transacts>:t} as … type{_(:type{_(:int)<transacts>:int},:int)<transacts>:int}" | `One(Succ, 0)` |
| `parametric-method-value` | L27, the call's arguments: "type{_(:tuple(p_type,c_type)->void,:c_type where p_type,c_type):p_type->void} as … tuple(tuple(first_arg,second_arg)->void,second_arg)->(first_arg->void)" | (none) |
| `interface-fn-param-generic` | L17, the override: "type{_(:int->void)<transacts>:void} as … type{_(:any->void)<transacts>:void}" | `F(X:t)` overridden |

So Epic's compiler converts a function named where a function type is
expected, whatever the conversion (the controls), and no other function
value that the conversion changes: a branch of an `if`, even a branch that
names a function; a generic function whose type parameter is inside a
function type of its own; the function a generic function's call returns;
an override called through a parametric interface's declaration, its type
parameter as `any`. The branches that need no conversion are not reported
(`ArrayToString`, `DecidesIdentity` at its own type), and the Book's tests
show conversions that change nothing admitted in a join (classes,
`FunctionTypes.versetest` 198-203; a default kept, `DefaultNamed.versetest`
623).

[`followup-coerce`](../../tests/conformance/versevm/followup-coerce) asked
where the edges are, 37 compile-only probes, one construct each. UEFN 43.12
compiled them one at a time on 2026-11-19 (~15:40Z); its outcome and
diagnostics are in the probes' headers and `expectations.tsv`. 31 agreed
with openverse's first rule (branches of an `if`, generic values, generic
results, overrides); six did not, and the rule is now wider:

| Probe | UEFN 43.12 | openverse before, now |
| --- | --- | --- |
| `value-computes-as-transacts` | 3502, a parameter of `<computes>` type passed as `<transacts>` (its control, the parameter at its own type, admitted) | admitted, refused |
| `value-plain-as-decides` | 3502, the same to `<computes><decides>` | admitted, refused |
| `value-default-drop` | 3502 "Using a value of type (?A:int = ...)->int as a value of type tuple()->int", a local bound to `F2` | admitted, refused |
| `option-of-fn-default` | 3502 "Using a value of type ?((?A:int = ...)->int) as a value of type ?(tuple()->int)", `option{F2}` (an array's and a tuple's elements naming `F2`, and a `case`'s arms, admitted) | admitted, refused |
| `parametric-method-fn-result` | 3502 "Using a value of type (t->void)->(t->void) as a value of type (int->void)->(int->void)", `box(int){}.Make(TakeInt)` | admitted, refused |
| `value-class-variance` | admitted: a `type{_(:animal):int}` parameter passed as a `type{_(:dog):int}` | refused (no variance for values), refused: a recorded difference |

The matching refusals: `join-computes-transacts` and `join-method-values`
(an effect added in a join, functions and methods), `generic-higher-order-bound`
and `generic-higher-order-concrete-param` (`One` bound to a local, passed
to a function that is not generic), `generic-result-fn` ("Using a value of
type type{_(:t,:t->void where t):t->void} as a value of type
tuple(int,type{_X:int where 1 <= _X, _X <= 5}->void)->(int->void)": Epic's
flow types give `t` the literals' range), `iface-override-fn-result` and
`class-override-fn-param` (3502, the override as `any->void`),
`overloaded-fn-value` (3502 "Referencing an overloaded function without
immediately calling it is not yet implemented") and `name-decides-as-plain`
(3509). Admitted, as by openverse: names at other types
(`name-computes-as-transacts`, `name-default-arg`, `method-value-effect`,
`generic-arg-*`, `generic-bound-first`), joins of class results and
parameters, `array-of-fns-*`, `tuple-of-fns-default`, `case-join-*`,
`generic-result-plain`, `generic-result-fn-comparable`, the
`iface-*` overrides that need no wrapper, and the controls.

So the rule is about values, not joins: any function value that is no
function named where its type is expected (a local, a parameter, a field,
a call's result, an option's content, a branch of an `if`) needs the
wrapper to be one of another function type that changes it, and a
parametric class's method returning a function of its type parameter is
judged as a generic function is ([the
rule](../LANGUAGE.md#function-values-epics-compiler-does-not-convert-724),
`--function-coercions` keeps openverse's conversions). The Book survey moves
no case for the wider rule. One difference is left, `value-class-variance`:
openverse has no class variance for function values (Verse Core has no
contravariance, and the front end makes adapters for names only).

[`followup-coerce2`](../../tests/conformance/versevm/followup-coerce2) asked
what the wider rule left unasked, 17 probes. UEFN 43.12 compiled them one
at a time on 2026-11-19 (~17:40Z), and 14 agreed with openverse. It refuses
with 3502 every function value converted where that needs a wrapper: a
parameter returned at a wider type, a field read and one stored at a
construction, a call's result, an array ("[]type{_(:int)<computes>:int}
as []type{_(:int)<transacts>:int}"), a map, a tuple's element, a field
passed to a generic call, and `int->int` as `int->rational` and as
`int->void` (which openverse refused as type errors and now refuses citing
3502); it admits a parameter returned at its own type, a method named as a
generic call's argument, a function of a `rational` named at
`type{_(:int):int}`, and a parametric class's method at `any`. Three
differed:

| Probe | UEFN 43.12 | openverse before, now |
| --- | --- | --- |
| `join-int-rational` | 3502 "Using a value of type tuple()->int as a value of type tuple()->rational", an if's branches | admitted (an `int`/`rational` exemption), refused: the exemption is gone |
| `name-void-result` | admitted: `IntIdentity` named where a `type{_(:int):void}` is expected | refused, admitted: a function named converts by variance to a `void` result or from a `void` parameter |
| `value-class-result` | admitted: a `type{_():dog}` local as a `type{_():animal}` | refused, refused: the class-variance difference, with `value-class-variance` |

## Running many probes

[`ovprobe.py`](../../tests/conformance/versevm/ovprobe.py) (Python 3
standard library, Linux or Windows) generates the UEFN sources, runs
OpenVerse, reads UEFN's logs and writes the comparison. Probe directories:
the original probes, [`book/`](../../tests/conformance/versevm/book) (a ranked
shortlist of Book cases where OpenVerse and the Book differ, with the cases
and expectations in its `expectations.tsv`) and
[`fingerprint/`](../../tests/conformance/versevm/fingerprint) (behaviour
reported to differ between Epic's VMs) and
[`followup/`](../../tests/conformance/versevm/followup) (what the 43.12
compiler results leave open, [above](#follow-up-probes)). With `P` for
`tests/conformance/versevm`:

```sh
python3 $P/ovprobe.py openverse $P $P/book $P/fingerprint $P/followup --json ov.json --tsv ov.tsv
python3 $P/ovprobe.py generate --mode single --out single $P $P/book $P/fingerprint $P/followup
# build each single/<probe>/openverse_probe.verse alone; for each build's log:
python3 $P/ovprobe.py parse --single <probe> --out admit/<probe>.json UnrealEditorFortnite.log
python3 $P/ovprobe.py generate --mode batch --exclude-refused admit --risky-last ov.json \
    --out batch $P $P/book $P/fingerprint $P/followup
python3 $P/ovprobe.py parse --manifest batch/manifest.json --out session.json UnrealEditorFortnite.log
python3 $P/ovprobe.py compare --openverse ov.json --epic admit --epic session.json \
    --tsv report.tsv --md report.md
```

Test compile admission with `--mode single`, one file at a time, as above:
its output is byte for byte this runbook's concatenation. Run only admitted
probes in a batch. The default batch is one file,
`ovprobes/openverse_probe_driver.verse`, with one inline module per probe and
one device, `openverse_probe_driver`, that runs them in order, every line
tagged `OVPROBE <probe> …`. A Verse runtime error ends the session's Verse:
`parse` reports the probe that began without an end as aborted and the later
ones as missing, and `generate --exclude-done session.json` makes the next
batch from the rest. Empty the single-probe file before a batch build: a
probe's `Main` left at the project's top level would be shadowed by the
batch modules' own, which the Book forbids (chapter 16). `--layout devices`
instead gives each probe a folder and its own device class. `parse` also
reads the JSON that
[`uefn_mcp.py`](../../tests/conformance/versevm/uefn_mcp.py) writes from
UEFN's local MCP server (`admit` builds the single-mode files one by one;
`build`, `session`, `logs`). That client has not been run against an editor.

No wrapper here has been compiled by Epic's compiler. The batch layout uses
the Book's module forms (chapter 16): inline `module:` definitions and
`<public>` entries called as `ovp_<probe>.RunOVProbe()`. OpenVerse runs the
same file with its device class replaced by a `Main`
(`generate --host openverse`, checked by `tests/scripts/test-versevm-live.py`).
If the first build cannot resolve a name of the header, such as `Print`,
pass an edited copy with `--header`.
