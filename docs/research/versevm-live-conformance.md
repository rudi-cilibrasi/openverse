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

The checked-in baseline has 702 VerseVM-targeted records. Of those, 216
agree, 288 are refused by OpenVerse, 4 are accepted by OpenVerse where the
Book expects a refusal, 88 produce different output and 106 cannot be
translated by the harness. The other records are 585 BPVM-targeted (including
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
| `signal-subscribe` and its control (rewritten: the field is `Seen`) | Refused because OpenVerse's `event` lacks `Subscribe`; it provides subscription through `subscribable_event` (`followup/subscribable-event-control.verse` asks 43.12 which type has it). | Same refusal. |
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
| `constant-default-call` | 3582 L2 "Divergent calls (calls that might not complete) cannot be used to define data-members" | refused: the constant calls a function that writes |
| `constructor-default-in-if` | 3512 L7: `MakeThing` has `no_rollback` | refused, the same |
| `decides-body-default-call` | admitted; prints `compiled` | `compiled` |
| `decides-plain-if` | 3512 L4: `Positive` has `no_rollback` | refused, the same |
| `default-into-default-type` | admitted; `result 1` | `result 1` |
| `for-filter-default-call`, `for-range-default-call` | 3512 L3 (`Value`, `Limit`) | refused, the same |
| `int-cast-variants` | 3509 L5 "Dynamic cast to `int` takes an int as its parameter, instead got any" | refused, the same reason |
| `join-if-common-base-interface`, `join-if-expected-interface` | 3510 L6: the body's value is an `any`, not a `super_class` / `named` | refused, the same reason |
| `join-interface-only` | admitted; `length 2` | `length 2` |
| `print-in-condition` | admitted; `printed in condition`, `after` | `after`: openverse rolls the `Print` back with the failed condition. **Differs**: the Verse VM keeps output across rollback |
| `signal-class-block`, `signal-transacts-method` | 3512 L3, L4: `Signal` has `no_rollback` | refused, the same |
| `subscribable-event-control` | 3506 L7 "Unknown identifier `subscribable_event`" | `after success 2`: `subscribable_event` is an openverse extension |
| `subscribe-in-transacts` | admitted; `seen 4` | refused: openverse's `event` has no `Subscribe`. **Differs** |
| `transacts-into-decides-type` | admitted; `result 1` | `result 1` |
| `signal-bound-control` (rewritten) | admitted; `after` | `after` |
| `signal-subscribe` (rewritten) | 3512 L10 at its condition's `Signal`, nothing else | refused: no `Subscribe` on `event` |
| `signal-subscribe-control` (rewritten) | admitted; `after success 2` | refused: no `Subscribe` on `event`. **Differs** |

What they settle, now openverse's rules: a plain `<decides>` function has
`no_rollback`, and its body's top may call one that has it, while a failure
context inside it may not; a `for`'s range and filter are failure contexts;
constructors without specifiers have `no_rollback`; an event's `Await` has
it, `Print` and `Subscribe` do not; a `<transacts>` function is a value of a
`<transacts><decides>` type; an `if`'s branches of two classes with two
nearest common supertypes are an `any`, whatever is expected; a class below
a `<concrete>` one cannot be `<abstract>`; `int[X]` of an `any` is refused.
Two differences remain: `Print`'s rollback (openverse's output is
transactional in Core and in the C runtime) and `Subscribe` on `event`
(openverse has it on `subscribable_event` only).

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
