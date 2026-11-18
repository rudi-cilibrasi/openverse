# Live VerseVM conformance

## Reference targets

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

The Linux workspace has no Epic runner available. On November 17, 2026, the
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
.lake/build/bin/openverse check "$probe" --signal-no-rollback
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

## Epic observations

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

## OpenVerse observations

On the tested head of [#702](https://github.com/rudi-cilibrasi/openverse/pull/702),
`adb392adb0dd8288c3366d1b45753b9c0904399c`, Lean and C agreed on stdout,
stderr and exit status for all thirteen probes that produced bytecode.

| Probe | Default outcome | With `--signal-no-rollback` |
| --- | --- | --- |
| `signal-control` | Prints `selected`. | Admitted. |
| `signal-direct`, `signal-alias`, `signal-bound`, `signal-generic` | Print `after`. | Refused at the call in the failure context. The bound and generic controls are admitted. |
| `signal-await` | Prints `waiting`, then `received 2`. | Refused at the first signal. |
| `signal-interface` and its control | Both print `after`. | The failure-context call is refused through the interface. The control is admitted. |
| `signal-subscribe` and its control | Refused because OpenVerse's `event` lacks `Subscribe`. OpenVerse provides subscription through `subscribable_event`. | Same refusal. |
| `compound-indexed-write` | Prints `length 2`, then `first 0`; since #704, `length 1`, then `first 0`, as Epic does. | Admitted. |
| `compound-whole-write` | Prints `length 2`, `first 0`, and `second 42`. | Admitted. |
| `int-overflow` | Runtime overflow, exit 2. | Admitted by `check`. |
