# Scheduler conformance audit

Issue [#495](https://github.com/rudi-cilibrasi/openverse/issues/495), measured on
main `2cfc6644770fcd27c222d1e657ec6a755f5bf504` (#512). This audit retains the
existing reference scheduler and adds trace oracles and an explicit account of
its compatibility boundaries. It changes no scheduler, Core, runtime or proof
input. The ordinary and `--no-choice` source profiles use the same scheduler;
neither selects an engine timing or effect policy.

## Sources and evidence

The Book snapshot is commit
[`beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/14_concurrency.md),
still its main head when checked on 2026-11-11 America/Los_Angeles. The
[event tests](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/Event.versetest),
[concurrency tests](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/Coroutines/Concurrency.versetest)
and [spawn/task tests](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/Coroutines/SpawnAndTask.versetest)
are development expectations; they are not a released-engine certification.

Published Epic references were checked on the same local date (2026-11-12
UTC): [Sleep](https://dev.epicgames.com/documentation/fortnite/verse-api/versedotorg/simulation/sleep?lang=en-US),
[simulation updates](https://dev.epicgames.com/documentation/en-us/fortnite/simulation-update),
[structured concurrency](https://dev.epicgames.com/documentation/fortnite/structured-concurrency?lang=en-US),
[sync/race/rush examples](https://dev.epicgames.com/documentation/fortnite/debugging-and-troubleshooting-in-verse),
[event](https://dev.epicgames.com/documentation/fortnite/verse-api/versedotorg/verse/event/event%28t%29),
[event Signal](https://dev.epicgames.com/documentation/fortnite/verse-api/versedotorg/verse/event/event%28t%29/signal)
and [signalable Signal](https://dev.epicgames.com/documentation/fortnite/verse-api/versedotorg/verse/signalable/signalable%28payload%29/signal?lang=en-US).
These are dated, unversioned public descriptions. They do not identify a
particular installed SDK/compiler. Both Signal pages render `transacts` and
`no_rollback`; their effect descriptions cannot substitute for a versioned
compiler/admission experiment.

No Epic compiler or engine was run. Evidence below is either a published rule,
a development-source expectation, or an OpenVerse model/VM observation. When
the sources disagree, the table records that disagreement.

## Observable rules

| Rule | Upstream evidence | Reference scheduler and trace evidence | Classification |
| --- | --- | --- | --- |
| Clock and positive delays | The Book uses simulation updates. Epic permits variable update durations, independent of rendering. Neither cited timing description specifies a fixed 30 Hz rate. The Book's API reference (`Sleep`, line 3939): "a sleep resumes on the first update at or after its deadline and never sooner than the next one. Short sleeps therefore round up". | A virtual 30 Hz clock skips idle ticks. Supported positive finite delays use `max(1, Ceil(30*S))` after binary64 multiplication: the first tick at or after the deadline ([the Book's rules](#the-books-scheduler-rules)). In [sleep](../../tests/verse/scheduler_audit_sleep.verse), `Sleep(0.04)` (1.2 ticks) completes at the second tick, after the first one-tick sleeper. | The API's rounding up; the 30 Hz rate is the reference clock's, no engine-rate claim. |
| Zero delay | The pinned Book's NextTick discussion permits same-tick resumption for `Sleep(0.0)`; its tested ch. 14 examples have it complete at once. Epic's Sleep page and the Book's API reference specify the next update. | Zero completes at once, without yielding, as negative and NaN durations do ([the Book's rules](#sleep00-completes-at-once)); in [sleep](../../tests/verse/scheduler_audit_sleep.verse) the zero sleeper goes on before its peer starts. | The Book's tested examples; its prose and API differ. |
| Negative, NaN and infinite delays | Epic describes negative durations as immediate and positive infinity as indefinite. The cited API does not specify NaN. | Negative/NaN durations return immediately; positive infinity never wakes. [Sleep](../../tests/verse/scheduler_audit_sleep.verse), [cancel](../../tests/verse/scheduler_audit_cancel.verse) and [deadlock](../../tests/verse/scheduler_audit_deadlock.verse) separate these cases. | Negative/infinite cases follow the API; NaN is a reference choice. |
| Numeric limits | The cited timing sources give no matching finite cutoff or int64 accumulation limit. | The binary64 product `30*S` must be below `2^63`. Finite inputs outside that domain terminate immediately with `error: user`; they do not become infinite waits. Current time plus the rounded ticks uses checked int64 addition and terminates with `error: overflow` beyond the clock maximum. [Bounds](../../tests/verse/scheduler_audit_clock_bounds.verse) now completes across the former cutoff; [overflow](../../tests/verse/scheduler_audit_clock_overflow.verse) retains its deliberate overflow result. | Explicit bounded reference-clock policy ([#514](https://github.com/rudi-cilibrasi/openverse/issues/514)); not measured engine limits. |
| Structured completion and ties | The Book and Epic tutorial describe sync waiting for all, race cancelling losers, and rush allowing unfinished work to continue. | Arms run to a wait/end in source order. Same-tick race completion chooses the earlier arm; an immediate winner prevents later arms from starting. [Ties](../../tests/verse/scheduler_audit_ties.verse) records winner and cleanup. | Common completion behavior; the exact tie/start/cleanup ordering here is the tested reference policy, not a measured engine trace. |
| Event fanout | The Book's prose conflicts between broadcast and one recipient. Epic's event/Signal descriptions resume all current awaiters. | One signal delivers the value to every current waiter. [Event order](../../tests/verse/scheduler_audit_event_order.verse) deliberately registers B before A and observes both receive 7. | Selects the published API's broadcast reading. |
| Event wake order | Epic specifies suspension order. | Main precedes spawned roots; roots retain spawn order, and structured arms retain source order. B waits first but A resumes first in [event order](../../tests/verse/scheduler_audit_event_order.verse). | Published FIFO mismatch, tracked in [#513](https://github.com/rudi-cilibrasi/openverse/issues/513). |
| Signal boundary and re-await | The Book drops signals with no waiter; Epic describes which already-suspended tasks resume and re-await during a signal waiting for a later signal. | Signal marks waiters ready and returns before their continuations run. Consecutive signals 1 and 2 deliver only 1 to those waiters; after they re-await, signal 3 reaches both. [Re-await](../../tests/verse/scheduler_audit_event_reawait.verse). | Reference non-reentrant resumption boundary; no claim that a versioned engine produces the same trace. #513 includes this boundary in its compatibility work. |
| Subscriptions and event transactions | The Book describes transactional Subscribe/Cancel. Epic's signalable API invokes callbacks synchronously, but its Signal effects include no_rollback. | Callbacks execute synchronously in subscription order. Failed Signal restores callback state/output and pending waiter readiness. Failed Subscribe/Cancel restores the subscriber list. [Transactions](../../tests/verse/scheduler_audit_transactions.verse) counts exactly `2+3+4=9`; the waiter receives 2, never rolled-back 1. | Transactional reference policy. Engine-compatible failure-context admission is tracked in [#515](https://github.com/rudi-cilibrasi/openverse/issues/515), coordinated with #494. |
| Cancellation and source return | The Book requires immediate, non-suspending cleanup; return in a concurrent arm leaves the enclosing function. | Nested defers run once; repeated Cancel is harmless. An arm return unwinds that arm, cancels its race siblings, runs surrounding defers, then stops the function's registered branches. [Cancel](../../tests/verse/scheduler_audit_cancel.verse), [source return](../../tests/verse/scheduler_audit_source_return.verse). | Lifetime/cleanup checks; the complete ordering is an OpenVerse policy, including function defers before registered branches. |
| Creator and host lifetime | Structured concurrency constrains child lifetimes. The Book distinguishes spawn from branch. A standalone Main/process shutdown is not an engine-device lifetime rule. | A spawn survives its creating function; a branch does not. Main finishing ends this host without cancelling unfinished unstructured tasks, so their pending defers do not run. Main stalled with no possible wake exits 2. [Lifetime](../../tests/verse/scheduler_audit_lifetime.verse), [deadlock](../../tests/verse/scheduler_audit_deadlock.verse). | Explicit command-line host boundary, not a Fortnite session guarantee. |

### Bounded clock domain (#514)

For a nonnegative finite binary64 input `S`, the scheduler first computes the
binary64 product `P = fl(30*S)`. It requires `P < 2^63`, then uses
`max(1, Ceil(P))` ticks (until `feat/core-book-primitives`, `RoundEven(P)`). The guard precedes integer conversion: a finite
out-of-range `Round` is an overflow error in Core, whereas this input-domain
policy deliberately reports fatal `Err()` (`error: user`). It is not a
`<decides>` failure and cannot be caught as a failed condition.

| Boundary | Exact result |
| --- | --- |
| Largest supported binary64 seconds | `307445734561825792.0`, bits `0x4391111111111110` |
| Its rounded ticks | `9223372036854773760 = 2^63 − 2048` |
| Next binary64 seconds | `307445734561825856.0`, bits `0x4391111111111111`; its product rounds to `2^63` and is rejected |
| Accumulated clock | starts at zero; supported values run through `9223372036854775807 = 2^63 − 1` |
| Exact maximum-time control | the largest duration, followed by `68.23333333333333` seconds (2047 ticks), reaches the clock maximum |
| Next zero/subnormal sleep there | one additional tick deliberately raises checked-int `error: overflow` |

The floating quotient `2^63/30` is the first **unsupported** duration, so a
comparison `S <= 2^63/30` would be wrong. At and above `2^52`, binary64
products are integral; below it, rounded products are far inside int64.
This establishes that the product guard covers representable rounded ticks.
Clock accumulation retains Core's checked addition; no wrap or clamp is
introduced. There are no new Core primitives, runtime operations, toolchain
changes or proof-input changes. Compiled-program checks and the existing
checked-int/heap proofs remain the trust boundary.

Positive infinity alone is the intentional indefinite input. Negative
values (including negative infinity) and NaNs retain their immediate
reference behavior, as both signed zeros now do (the tested examples of
ch. 14, [below](#sleep00-completes-at-once)); positive subnormals wait at
least one tick. Infinite terminal deadlock and unsupported finite input
share the generic `error: user` text, but differ observably: the
[invalid finite race](../../tests/verse/clock_domain_fatal_first_unsupported.verse)
errors before its peer starts, while the
[infinite timer](../../tests/verse/clock_domain_cancel_positive_infinity.verse)
can be cancelled and runs its cleanup. Fatal runtime errors do not promise
cleanup unwinding. Primitive rounding and infinity classification are
isolated from source-owned `Round`, `Inf` or `IsFinite`; explicit source
calls and values keep their ordinary meaning.

The [clock-domain gate](../../tests/scripts/test-clock-domain.py) checks exact
stdout/stderr/status in Lean and C under both source profiles and requires
identical bytecode. Its [independent model](../../scripts/models/clock_domain.py)
uses exact fractions and binary64 quantization, without VM imports, across
100 programs per complete period: two timers, a tick reference arm,
cancellation races and accumulated time. It includes adjacent rounding and
range boundaries, unsupported finite products, infinity, zero, subnormals
and source overrides. Existing scheduler traces remain in the normal gate;
the old finite-cutoff reproducer now has its intended finite-success oracle.

The pinned Book labels `Task.Cancel`, `NextTick`, sticky events and subscribable
events unreleased. OpenVerse implements cancellation, sticky and subscribable
events as documented extensions; it does not expose NextTick. This reports
the snapshot's labels, not a claim about every later SDK release. Existing
[subscribable-event mutation cases](../../tests/verse/subscribable_event_more.verse)
also cover subscription/cancellation during delivery;
[stop-order cases](../../tests/verse/stop_order_return_arm.verse) cover deeper
branch/rush/source-return combinations.

## Compatibility decisions

The reference policy remains the default for both source profiles. The bounded-clock policy above updates numeric admission; it adds no
scheduler option or rollback change. In
particular, `--no-choice` permits the same clock, mutation, event transactions
and cleanup behavior; it restricts source choices/generators, not engine
compatibility.

Three focused issues carry the implementation decisions:

- [#513](https://github.com/rudi-cilibrasi/openverse/issues/513): define FIFO
  resumption and the Signal-return boundary, including nested arms,
  cancellation and re-await. A different policy/default must be adopted
  explicitly before changing existing traces.
- [#514](https://github.com/rudi-cilibrasi/openverse/issues/514): the bounded
  clock domain above now defines finite duration admission and checked
  accumulation; supported finite time is not silently treated as infinity.
- [#515](https://github.com/rudi-cilibrasi/openverse/issues/515): establish
  versioned SDK failure-context rules and an explicit engine-compatible
  Signal admission policy. Retain reference rollback and unsupported
  native/no_rollback annotation diagnostics until a separate change is adopted.

This is an audit of the current scheduler's observable timing, event, cleanup
and host rules. It does not introduce parallel CPU threads, networking,
external event arrivals, wall-clock integration, Fortnite device/session
lifecycle, persistence or services. Those require separate host and effect
contracts; they do not follow from support for the concurrency expressions.

## Validation and proof boundary

```sh
lake build
make -C runtime
bash tests/scripts/test-scheduler-conformance.sh
CHECK_JOBS=6 scripts/check.sh
```

The dedicated runner checks **11 trace fixtures and three finite controls**
against explicit stdout, stderr and exit oracles in Lean and C. It also runs
each source under `--no-choice` and requires identical admitted bytecode.
Stall and overflow errors are checked separately, so a generic failure, fuel
limit or compile refusal cannot pass as the intended numeric boundary.
The ordinary regression suite includes all eleven fixtures. The new runner
reports 88 checks and participates in the full gate alongside the independent
[scheduler models](../../scripts/models/sched_gen.py), source cleanup models,
sanitizers and existing effect/profile contracts.

The event wake-order reproducer emits identical bytecode on main #509 and
#512; the audit does not create that difference. Its oracles are reference
policies and public-source comparisons, not captured engine outputs. Core's
`Eval.det`/`Runs.det` guarantees still concern a checked Core execution. VM
agreement and frontend/model tests do not prove equivalence to an external
scheduler or correctness of the entire lowering; see [CLAIMS.md](../CLAIMS.md).

## The Book's scheduler rules

The owner's rule is to follow the pinned Book where it and openverse
disagree. Three scheduler readings were [designed in the readings
audit](readings-audit.md#the-scheduler-rows); this section pins each from
the Book (chapters under `docs/`, the API reference
`docs/api/verse_runtime_api.html` by line, tests under `Tests/`) and says
what openverse does now.

### `Sleep(S)` rounds up

- **API** (`Sleep`, line 3939): "For positive finite waits, resumption is
  driven by the world's timer manager, so this measures game time and not
  wall-clock time, and it is quantised to ticks: a sleep resumes on the
  first update at or after its deadline and never sooner than the next
  one. Short sleeps therefore round up, and a chain of them accumulates
  error".
- **Chapters and tests:** no tick rate, no rounding rule.
- **openverse:** the deadline, in ticks of the reference clock's 30 a
  second, is the binary64 product `30·S`, as before; the sleep wakes at the
  first tick at or after it, `Ceil(30·S)` ticks later, at least one. (Until
  now `Round`, ties to even.) `Sleep(0.04)` (1.2 ticks) and
  `Sleep(0.049999999999999996)` (1.4999999999999998) take two ticks, not
  one; `Sleep(0.15)` (4.5) five, not four; `Sleep(0.1)`, whose product
  rounds to exactly 3.0 in binary64, still three. The bounded clock domain
  (#514) is unchanged: products at or above 2^52 are integers, so the
  largest supported duration and its ticks are the same.

### `Sleep(0.0)` completes at once

The Book disagrees with itself.

- **Prose** (ch. 14): `14_concurrency.md:1210`, "`Sleep(0.0)      # One
  frame, the smallest possible delay`"; `:1213-1219`, "While it does not
  add actual delay, it serves two critical purposes. It creates a
  suspension point, which is where cancellation gets checked, and it
  yields control to other concurrent tasks, so that no single task can
  monopolize execution"; `:1227-1228`, "Unlike `Sleep(0.0)` which yields
  control and may resume in the same tick if no other work is pending".
- **API** (`Sleep`, line 3939): "0.0 resumes on the next update and,
  crucially, does yield, which is what makes it the correct body of a
  per-frame coroutine loop".
- **Tested examples** (ch. 14's `<!--versetest-->` blocks, each checking a
  task's effects right after `spawn{…}` returns, with no tick between):
  `<!-- 03 -->` (`:138-167`, a `sync` of three arms that each
  `Sleep(0.0)`: "`Loaded.Ids = (1, 2, 3)`"), `<!-- 05 -->` (`:246-274`,
  `Race.Winner = 2`), `<!-- 06 -->` (`:297-333`, "The square won"),
  `<!-- 07 -->` (`:342-370`, `Won.Id = 2`), `<!-- 08 -->` (`:378-407`:
  "`Sleep(0.0)                   # Completes at once, and wins`", "Arm two
  wins on the first pass through the arm list, before arm three has been
  entered even once"), `<!-- 09 -->` (`:438-485`, `rush` and `race`,
  `Trail.Trace = 102`, `RaceLog.Trace = 2`), `<!-- 10 -->` (`:518-548`,
  "Arm two never got to run, the code after the sync never ran, and 5 came
  out") and `<!-- 11 -->` (`:555-588`, `Steps.PastSync = 1`). In each, every
  `Sleep(0.0)` on the task's path completed without suspending: the
  spawned task ran to its end within the `spawn`.
- **Book tests** (`Tests/`): none call `Sleep(0.0)`.
- **openverse:** the tested examples': `Sleep(0.0)` (and `-0.0`, which is
  `0.0`) completes at once, without suspending, as a negative or NaN
  duration does; it is no suspension point, so neither cancellation nor
  other tasks get a turn there. Until now it always yielded, to the next
  tick. A positive duration, however small, waits at least one tick
  (`Sleep(0.01)` is one tick, rounded up). The audit had proposed a
  narrower rule ("complete without yielding when no other task is
  runnable at that point of a `race`'s first pass"); the examples `03`,
  `10` and `11` show the same in a `sync` and in plain code, and openverse
  has no notion of a task that is runnable without running it, so the rule
  is the examples' without a condition. A loop whose only wait is
  `Sleep(0.0)` never lets another task run (the API says the same of a
  negative duration); a loop that should give way writes a positive one.

### Awaiters run inside `Signal`

The Book fixes both the order in which a `Signal` resumes the tasks
awaiting it and when they run: inside the `Signal`, before it returns.
This section pins every consequence from the Book (the API reference
`docs/api/verse_runtime_api.html` by line, ch. 14 `docs/14_concurrency.md`
by line, tests under `Tests/` by file and line), says what openverse did
before, and gives the design; [as built](#awaiters-inside-signal-as-built)
says what landed.

#### The rule, pinned

1. **Order: the order they suspended.** API, `event`'s `Signal` (line
   4346): "Tasks suspended in `Await` are resumed first, in the order they
   suspended, so the order the waits appear in your code is the order they
   come back"; the class (line 4341): "Suspended awaiters resume in the
   order they suspended"; `sticky_event`'s `Signal` (line 1020): "resumes
   the queued awaiters in the order they suspended". Every awaiter is
   woken, each given the value: line 4346, "Wakes everything waiting on the
   event, handing each one `Val`" (ch. 14 also says "each `Signal()` wakes
   exactly one awaiter", `:1486-1488`, against "Each signal delivers one
   value to each awaiting task", `:1451-1452`: the wiki's *How many
   awaiters one `Signal` wakes*; openverse keeps the API's, every awaiter).
2. **Each runs until it next waits or ends, before the next is resumed,
   and all of them before `Signal` returns.** Line 4346: "Each resumed task
   runs until it blocks again before the next one is given a turn"; line
   4341: "each runs until it blocks before the next is resumed"; line 4510
   (`signalable`): "Note that `Signal` returns before the resumed tasks have
   finished. They run only until they block, so control can come back to
   the signaller with awaiters still mid-flight". Tests:
   `Event.versetest:21-32` (one task's `sync`: an arm awaits four times
   while its sibling signals four times in a loop that never waits; the
   awaiter receives `(1, 2, 3, 4)`, so it runs inside each `Signal`, the
   same task's arm included); the four `Bugs/FORT-1088027-*` and
   `FORT-1126351-*` cases below, each checking the awaiters' effects right
   after the `Signal`s of an assertion.
3. **What the signaller sees.** Whatever the awaiters did before they
   waited again (line 4510: "any state the callbacks touched may be
   half-updated from the signaller's point of view");
   `when.versetest:179-188` checks `Z = 1` on the line after
   `Event.Signal()`, the awaiter having set its inputs inside the signal.
4. **An awaiter that awaits the same event again waits for the next
   signal.** Line 4346 (`Await`): "Calling it while a `Signal` is in the
   middle of resuming other tasks is safe but lands the new registration
   in a fresh frame, so it waits for the *next* signal rather than the one
   in progress"; (`Signal`) "A task that calls `Await` while this `Signal`
   is still running joins the next round rather than this one. Without that
   rule a task could wake itself in a loop and the signal would never
   finish"; line 4341: "awaits registered *during* a signal are moved into a
   separate frame and are deliberately not resumed by that same signal".
   A `sticky_event`'s new awaiter returns at once (line 1020: "Awaiters
   that appear during this drain ... return immediately, since the latch
   is now set").
5. **An awaiter that signals the same event again** starts a signal of its
   own, which resumes the awaits registered since the outer one began
   (the fresh round) and returns; the outer signal then goes on with the
   rest of its own round. `Bugs/FORT-1126351_reentrant_signal_probe.versetest:37-47`
   ("A nested Signal on E1 (while its drain is in flight) still resumes
   every parked awaiter": the outer round `[AwaitE1ThenReenterE1,
   OuterAwaitE1]`, a re-parked awaiter resumed by the nested signal, and
   every task done).
6. **Nested signals, depth first.** An awaiter that signals another event
   runs that event's awaiters, each to its next wait, before its own
   `Signal` returns and it goes on; the outer round goes on after it waits
   (rule 2 applied to the inner `Signal`).
   `Bugs/FORT-1126351_cross_event_reentrancy_probe.versetest:40-54` (X's
   awaiter signals Y, Y's signals Z, Z's re-parks on X, then Y's awaiter
   signals X again, nested in X's round: "Every parked awaiter is still
   resumed").
7. **An awaiter that ends, and a `race` it resolves.** An awaiter that
   ends its arm or task does so inside the `Signal`. When it completes an
   arm of a `race` whose code is running (the signaller is a sibling arm),
   the race is resolved there: ch. 14 `:412-417`, "An arm that is already
   executing when the race resolves is not cut off mid-statement: it
   continues to its next suspension point and is then cancelled along with
   the other leftover arms. When more than one arm could complete during
   that first pass, the first completer wins"; `:374-376`, "`race` starts
   its arms in order. If the race resolves before every arm has started ...
   the remaining arms never start at all". Tests:
   `Bugs/FORT-1126351-RaceArmsDoNotStartAfterResolution.versetest:22-37`
   (the signalling arm goes on to its next wait, `Arm2Continued = 1`, and
   the arm after it never starts, `Arm3Started = 0`),
   `Bugs/FORT-1088027-MultipleArmsCompleteDuringSpawn.versetest:24-42` (the
   first completer, arm 1, wins; arms 3 and 4 never start: `Hits = 1`),
   `Bugs/FORT-1126351-RaceArmSuspendedAfterResolution.versetest:33-54` and
   `Bugs/FORT-1088027-OldGenerationWakeDuringSpawn.versetest:32-54` (the
   race resolved during a loser's resumption; the leftover arm is cancelled,
   so the next round's awaiter gets the payload: `P.Score = 1`),
   `Bugs/FORT-1088027-UseOfNullInitializedDynamicallyTypedValue.versetest`
   65, 92, 116 (race, `branch` and `rush`, nested `sync`: `C0.Done = 1`).
   The value of such a race is its first completer's. A `rush` loser that
   went on after its `rush` is a task of its own, resumed like any (ch. 14
   `<!-- 09 -->`, `:438-485`: `Gate.Signal(0)` resumes the loser, which adds
   100 before the signaller's next line, `Trail.Trace = 102`).
8. **An awaiter that cancels the signaller.** Only the case of rule 7 has a
   test (a race's loser, cancelled when it next waits). Cancelling a
   running task otherwise follows `Task.Cancel` (line 1362: "Calling
   `Cancel()` on a task that is currently running ... will suspend the
   caller, until the target task reaches a cancellation point"), which the
   pinned Book labels unreleased; openverse keeps its recorded request,
   taken when the task's run returns (#253, #260).
9. **An awaiter cannot fail**: `<suspends>` excludes `<decides>`
   (`Effects.versetest:259-266`); a runtime error in it ends the program
   inside the `Signal` as anywhere.
10. **`Signal` from code that is not `<suspends>`.** Allowed: `Signal` is
    `(Val:t):void` with no effects (line 4346), and every test above
    signals from an assertion's body (immediate code), the awaiters having
    run when the next line checks them (FORT-1126351-RaceArmSuspendedAfterResolution
    `:50-54`, `C.E0.Signal()` ... `P.Score = 1`; `Coroutines/SpawnAndTask.versetest:1027-1041`,
    `verse_vm_only`, three spawned awaiters and one `Event.Signal()` from
    the assertion: `Z = 0 + 1 + 2`).
11. **`Signal` in a failure context, and its rollback.** Allowed: the
    assertions above are failure contexts; `Event.versetest:64-85` and
    `:91-111` signal in `<decides>` functions and expect success. A context
    that fails undoes what the awaiters did inside its `Signal`:
    `Coroutines/Concurrency.versetest:1562-1580` ("Resume the for loop body,
    let it add an array element, then abort the transaction" in `if:
    CoroUtils.SignalTransacts(Event, ()); false?`, then "Resume the for
    loop body again from the same place and let it finish": the awaiter is
    back at its wait). `Effects.versetest` and
    `SoftwareTransactionalMemory.versetest` have no `Signal`. The API's
    `event.Signal` (line 4346) carries no `<no_rollback>`: that effect is
    in the API only on `subscribable_event_intrnl` and agent groups (line
    1070, the wiki's *`Signal` in a failure context*) and on Epic's
    published `event` pages (Sources, above). So the default is the tests':
    allowed, and undone with its context.
12. **Subscribers after awaiters.** Line 4346: "Subscribers, on
    implementations that have them, are invoked only after every waiting
    task has been resumed" (openverse's `subscribable_event` already calls
    them after `signalAll`; the API's random order of subscribers is not
    followed).

What else resumes code inside the code that causes it:

13. **A task's end resumes its awaiters, in the order they registered.**
    API (`task`'s `Await`, line 1362): "Multiple awaiters are allowed and
    are resumed in the order they registered";
    `Coroutines/SpawnAndTask.versetest:293-321` (`TestAwait3`: three arms
    of a `sync` await one task, A and C at once, B after a tick; when the
    task ends the log reads `ZA2C2B3`, registration order, not the arms'
    `A2B3C2`). The FORT comments name the mechanism ("`event::Signal →
    task::Complete → ResumeAt → task::Update`"). Every such test needs
    `CoroUtils` (not translatable).
14. **`Sleep` expiry resumes nothing inside anything.** Line 3939:
    "resumption is driven by the world's timer manager ... a sleep resumes
    on the first update at or after its deadline". The order of sleepers
    waking at one update is not given; openverse keeps its pass order
    (`Main`, then the roots in start order, arms in source order).
15. **An arm runs to its first wait before the next arm starts**
    (`race`: ch. 14 `:374`, "`race` starts its arms in order"; `<!-- 08
    -->`, `:409`, "Arm two wins on the first pass through the arm list,
    before arm three has been entered even once"; `sync`: `<!-- 03 -->`,
    `:138-167`). openverse already does this.
16. **`spawn{F()}` runs `F` up to its first wait before `spawn` returns**
    (ch. 14 `:1729-1731`, "a spawned body runs up to its first suspension
    point immediately"; the FORT tests check the spawned listener's
    effects on the next line). openverse already does this, as it does for
    a `branch`'s first run.

**`spawn` in a failure context.** The Book accepts it: assertions spawn
(every FORT case above, `Event.versetest:54`, `SpawnAndTask.versetest:1027`),
and `LiveVariables.versetest:450-545` spawn inside `if: ...; false?` and
check that the task never runs (`Y = 0` after the rollback, the awaited
variable set again). Only `SoftwareTransactionalMemory.versetest:503-508`
refuses `spawn` in a `<transacts><decides>` function, inside
`bp_vm_only{…}` ("STM doesn't support spawn, don't allow in decides"): the
older VM's rule. openverse refused every `spawn` in a failure context
(#156; the survey's cause `spawn-in-failure-context`, 28 cases).

**openverse before this change.** `Signal` marked its awaiters woken and
returned; they went on when the scheduler next polled them, in its order
(`Main`, then the roots in start order, arms in source order), once the
signalling task waited, or, with `--event-fifo` (#513), in the order they
suspended, also once the signalling task waited. A `Signal` from immediate
code woke awaiters that only a suspends `Main`'s scheduler ever ran. Task
awaiters went on in the same pass order (rule 13 not followed). Rules 4,
5, 10 (allowed), 11 (allowed, rolled back), 12, 14, 15 and 16 held.

**The obstacle.** A suspended task is resumed only from its root, down
its chain of frames (DESIGN, "Concurrency: suspends functions as
frames"); a frame's suspension point is stored when it suspends. Inside
a `Signal`, the signalling task's own frames are running: the points
they hold are the old ones, so resuming its root again would re-run
what ran since. The awaiters of `Event.versetest:27` and FORT-1126351 are
arms of that same task, whose code (the `race`'s or `sync`'s) is running
the signaller.

