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
| Event wake order | The Book's API and Epic specify suspension order. | Waiters resume in the order they began waiting: B waits first and resumes first in [event order](../../tests/verse/scheduler_audit_event_order.verse). | The Book's ([awaiters inside `Signal`](#awaiters-run-inside-signal), #513). |
| Signal boundary and re-await | The Book drops signals with no waiter; its API resumes the waiters inside `Signal`, each until it waits again, and an await made meanwhile waits for the next signal. | Each waiter runs inside the `Signal`, to its next wait. Consecutive signals 1 and 2 deliver 1 and then, to the waits made inside the first, 2; signal 3 finds no one. [Re-await](../../tests/verse/scheduler_audit_event_reawait.verse). | The Book's ([awaiters inside `Signal`](#awaiters-run-inside-signal), #513). |
| Subscriptions and event transactions | The Book describes transactional Subscribe/Cancel; its tests signal in `<decides>` functions; its API invokes subscribers after every waiting task resumed. Epic's Signal pages render no_rollback. | Waiters run inside the Signal, then callbacks in subscription order. A failed Signal restores what the waiters and callbacks did, output included, and the waiters wait again. Failed Subscribe/Cancel restores the subscriber list. [Transactions](../../tests/verse/scheduler_audit_transactions.verse) counts exactly `2+3+4=9`; the waiter receives 2, never rolled-back 1. | The Book's tests (default); `--signal-no-rollback` for Epic's pages ([#515](https://github.com/rudi-cilibrasi/openverse/issues/515)). |
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

- [#513](https://github.com/rudi-cilibrasi/openverse/issues/513): FIFO
  resumption and the Signal-return boundary, including nested arms,
  cancellation and re-await: now the Book's rule, the default
  ([awaiters inside `Signal`](#awaiters-run-inside-signal)); `--event-fifo`
  is gone.
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

#### Design

Concurrency lives in the front end: Verse Core has no suspension, and the
front end lowers `<suspends>` code to frames and resume functions over a
scheduler written in Verse (`Front/Suspend.lean`, `Elab/Lowering.lean`'s
`lowerConcurrency`, the prelude in `Front/ConcurrencyPrelude.lean`). Tasks,
events, `Signal` and `Await` are prelude code and lowering output, not Core
primitives. So the rule is built in the lowering and the prelude; Verse
Core, OVBC, `runtime/include/openverse.h`, `runtime/src/load.c` and the
C interpreter do not move.

**Which programs change.** A program whose source uses an event type
(`event`, `sticky_event`, `subscribable_event`) is compiled in *event
mode*: its prelude has the drain below. Other programs compile byte for
byte as before. In event mode, the suspends functions from which the
prelude's `signalAll` is reachable through calls (an arm's or `branch`'s
code and a spawned call's first run included, a method's dispatch and a
function value's call conservatively, as for `--signal-no-rollback`) are
*marked*: their regions keep the running markers below. Only a marked
function's regions can be running while a `Signal` runs, as the code
under the `Signal` is theirs. The other functions compile as before.

**Running markers.** A region (a function's body, or an arm) keeps its
suspension point in a frame field: 0 not started, `k ≥ 1` at site `k`
(waiting there, or running the callee of a call there), -1 done. A marked
region also writes -2 while it runs code between sites (when it starts,
and after each site it passes) and `-(k+2)` while the code of its `sync`,
`race` or `rush` at site `k` runs the arms; back to `k` when it waits
there. Entering a marked region whose point is -2 gives 0 at once (it is
the code running the `Signal`, or above it); one at `-(k+2)` runs its
arms *partially* (below) and gives 0; one at `k` seeks it as before. A
call whose region runs at site `k` has a running callee, which by the
same rule gives 0. So resuming a task's root while its code runs walks
down the running code and returns, touching only what waits beside it.

**Partial arms.** At a running `sync`, `race` or `rush`, each arm that
started and is pending is resumed in order: a running one gives 0 at
once; a waiting one runs to its next wait or its end, as rule 2 wants. An
arm that ends there is marked done; the first such end or `return` of
the site is recorded in a field of the frame (`2i` an end, `2i+1` a
`return`; for a `sync`, only returns). The code that runs the arms, after
each arm's run, honours it: a `return` there makes the function return
(the pending arms that started are cancelled, last first, the defers
run); an end there wins a `race` or `rush`, so the later arms never start
and the started ones are cancelled (or go on, for a `rush`) when the
signalling arm next waits (rule 7). A race's value is the first
completer's: in a marked function each arm writes a value slot of its
own, and the winner's is the race's.

**The drain.** `signalAll(E, X)` takes the event's list (the current
round) and leaves the event an empty one, which awaits made from now on
join (rule 4). It marks each record of the round not already done (a
wait cancelled before marks its own): its value, done, *pending*. Then,
in the list's order, each record still pending is unmarked and its task
resumed: the scheduler's `Drain` depth goes up by one, `$wakeRoot`
resumes the root the record was last polled in (#513's `WaitRoot`,
recorded by `waitResume` from the scheduler's `CurRoot`; a `rush` loser
that goes on as a task of its own is probed once, as #513 did, so its
waiters record it), and the depth goes down. A pending record is reported
as waiting, so a task resumed for one record goes on only there. A
`Signal` made inside runs its own round first (rules 5 and 6); `Signal`
returns when its round is done.

**Waking a root.** `$wakeRoot` dispatches on the root's class (`Main`'s
frame, a spawned call's root, a branch's or `rush` loser's wrapper). A
root that is done is left. A root whose code is running (its own flag:
a field of each root's frame and wrapper in event mode, and the
scheduler's for `Main`) has its root region resumed directly, which the
markers make a walk down the running code (the waiting arms beside it
run); its recorded waiting frame (#362) is forgotten; a request to cancel
it found in that walk (it awaits a cancelled task) is dropped and the
scheduler asked for another pass, whose poll asks again. Any other root
runs as a spawn's first run does: the scheduler's cancel request saved
and cleared, `CurRoot` set, its trampoline run, what it recorded
forgotten, a request taken for it unless it ended, and marked done (and,
for `Main`, its frame's point set to -1, which `$Run` reads after each
root's run) if it ended. A trampoline saves its task's `Running` and
takes a cancel request of its task only if it was not running before
(as a branch's already did), so that running it inside another run of
the same task leaves that run's bookkeeping alone.

**Held waits.** Inside a drain, only an event record's turn goes on:
`sleepResume` reports a sleep that expired as waiting, and `waitResume`
a task wait that was already polled (a fresh one on a done task still
completes at once), asking for another pass; each goes on at its root's
turn in the scheduler's pass, as before (rules 13 and 14: task awaiters
keep the pass order). A rule-13 drain is the same machinery with a list
of records in each task; it is designed here and left (no translatable
case needs it).

**Branches stopped while they run.** A function resumed inside a
`Signal` that its own `branch` made can end and stop that branch. In
event mode each wrapper records that its arm is running; stopping it then
marks the wrapper done without cancelling the arm, and the wrapper's
trampoline, finding it stopped when the arm's run returns pending,
cancels the arm then.

**Rollback.** A drain is ordinary Verse Core run inside the `Signal`'s
caller: in a failure context that fails, Core's rollback undoes what the
awaiters did with everything else (rule 11): the records go back to
waiting, the tasks to where they waited. No primitive changes.

**`spawn` in a failure context** is allowed: a `spawn` is a call of its
root's `start`, which links the root and runs it to its first wait; in a
context that fails, the link and the run are undone with it, so the task
never runs again (`LiveVariables.versetest:450-545`). In a suspends
function, a `spawn` in a condition or filter is started in place (it is
not a suspension point). A `spawn` in a `defer:` stays refused (a
separate rule), as do a spawned call whose arguments suspend and the
`bp_vm_only` refusal of `SoftwareTransactionalMemory.versetest:503-508`
(the older VM's).

**Flags.** `--event-fifo` (#513) goes: the Book's order and timing are
the default, and FIFO order without the timing is no reading of the
Book. Its tests become tests of the default. `--signal-no-rollback`
(#515) stays an opt-in for the reading of Epic's published `event` pages;
the default, allowed and undone with its context, is the Book's tests'
(rule 11).

**Models first.** The scheduler models (`scripts/models/sched_gen.py`,
`sched_gen2.py`, `event_fifo.py`) are changed to the rule before the
lowering: a `Signal` resumes each awaiter in order, a running task by
walking its running code (`partial`), any other by a poll; arms that end
there are honoured by the code that runs the arms; sleeps and task waits
are held inside a drain.

#### Awaiters inside `Signal`: as built

As designed above; the pieces and where they are:

- **Event mode** (`Admitted.usesEvents`, `concurrencyHelpers`): a program
  that uses `event`, `sticky_event` or `subscribable_event` gets
  `concPreludeEvents` (`Front/ConcurrencyPrelude.lean`): the scheduler's
  `CurRoot`, `Probe`, `Drain` and `MainTask`; a task's `WaitRoot`,
  `Pending` and `Ev`; `signalAll`'s mark-then-resume round; `$wakeRoot`'s
  stub; `waitResume` and `sleepResume` holding a task wait and an expired
  sleep inside a `Signal`.
- **Marked functions** (`SignalAdmission.reaching`, `Suspend.Env.marks`):
  the region markers (`runningPc`, `armsPc`, `passed`, the entry code in
  `region`), `concAtMarked` (the out-of-turn field, the partial code, a
  race's per-arm value slots).
- **Wake functions** (`lowerConcurrency`, event mode): `$Main$wake`,
  `$spawnK$wake`, `$branchK$wake`, and `$wakeRoot`'s body; the roots' and
  wrappers' run records; the reentrant spawn trampoline; a stopped running
  arm cancelled by its wrapper's trampoline; `$Run` reading `Main`'s end
  after each root.
- **`spawn` in a failure context** (`Elab/Expr.lean`, `Suspend.inlineSpawns`).
- **`--event-fifo`** removed (`Main.lean`, `Options`), with
  `concPreludeFifo` and `$Run`'s FIFO drain.

Verse Core, OVBC, `runtime/include/openverse.h`, `runtime/src/load.c` and
the C interpreter are unchanged (`git diff origin/main -- OpenVerse/Core
runtime docs/FORMAT.md` is empty).

**What changed for programs** (every suite and the corpus `corpus2`, 5,951
programs, against main `dca5ad1`): 5,792 the same in bytecode, output,
messages and exit code; 158 programs' bytecode changed, every one of them a
program that uses an event type (two only in their `do` expression), 120 of
them with the same output; 38 with another output: the 22 tests whose
expected output changed (each re-derived by hand under the rule), the 8
FIFO upper-bound fixtures (likewise), and 8 corpus programs; one program
that was refused is accepted (a `spawn` in a failure context). No program
without an event type changed.

**Code size.** In the 144 changed programs compiled in the default mode,
bytecode grew by 13% at the median (7.5% to 41%; 14.16 MB to 16.19 MB in
all): the prelude's larger `signalAll`, `waitResume` and `sleepResume`, one
wake function per kind of root, the running markers in marked functions
(one write per site passed, three per `sync`, `race` or `rush` and the code
that runs its arms partially) and a race's per-arm value slots. The
largest growth is in small programs with many roots (the FIFO upper-bound
fixtures). The gate's size checks (`test-choice-size.sh`,
`test-frontend-c-size.sh`) pass unchanged.

**Models.** `sched_gen.py` and `sched_gen2.py` predict the Book's order:
over seeds 1-2,000, the new predictions differ from main's on 535 seeds;
the compiler matches the new predictions on all 2,000 (Lean, and C equal to
Lean), and main's predictions fail on exactly those 535. `event_fifo.py`
keeps its programs and predicts each round inside its `Signal` (every one
of its programs differs from the FIFO prediction, as each ends with
signals that wake every actor).

**What is left.**
- Rule 13: the tasks awaiting one task's end go on in the scheduler's
  order, not in the order they registered inside the end. Designed, and
  left: see [rule 13, pinned and designed](#rule-13-a-tasks-end-pinned-and-designed).
- Two arms that both `return` inside one walk: the first's value is kept;
  an in-turn `return` after an out-of-turn end of a `race` returns, as an
  arm's `return` leaves the function (no test of the Book has either).
- `SoftwareTransactionalMemory.versetest:503-508`, inside `bp_vm_only`,
  refuses a `spawn` in a `<transacts><decides>` function; the VerseVM's
  tests (`LiveVariables.versetest:450-545`, `verse_vm_only`) and the
  untagged assertions spawn in failure contexts, so openverse accepts it:
  the tests split by virtual machine, and openverse follows the VerseVM's
  and the untagged ones.

#### Rule 13, a task's end: pinned and designed

**When.** Inside the ending task's last step, before anything else runs:
the API (`task`'s `Await`, line 1362) fixes the order, "Multiple awaiters
are allowed and are resumed in the order they registered", and the Book's
tests name the mechanism: `Bugs/FORT-1088027-UseOfNullInitializedDynamicallyTypedValue.versetest:6-9`,
"a bytecode-issued Signal during `task::Update` synchronously re-enters
Update for the same task via `event::Signal → task::Complete → ResumeAt →
task::Update`": a task that completes resumes what awaits it at once,
synchronously, as a `Signal` does. `Coroutines/SpawnAndTask.versetest:293-321`
(`TestAwait3`, "ZA2C2B3": the awaiters' lines follow the task's last in
the same tick, in registration order) agrees with this and cannot tell it
from a resumption at the scheduler's pass; no test has another task run
between a task's end and its awaiters.

**Design, on the machinery above.** Each task keeps a round of awaiter
records, as an event does; `T.Await()` on a task not done appends one and
waits on it (a task done gives its result at once, as now); a spawned
call's root, after it sets the task's result and done, runs the round
inside its last step, as `signalAll` does: each record marked, then each
one's root woken in order (`$wakeRoot`), the scheduler's `Drain` raised.
Programs that await a task would be compiled in event mode too.

**Why it is left.** Measured on the scheduler model (a copy with task
awaiters resumed so), 40 of seeds 1-400 predict another output; 162 of the
suite's programs spawn and await a task (all of them would change bytecode,
by the measure, a tenth or more their output, each to be derived again by
hand), and 13 other models generate task awaits (`call_packing.py`, twelve `gadt_*`). And it needs a reading the
Book contradicts openverse on: the API says "a *cancelled* task never
resumes its awaiters, so the call does not fail, does not error, and simply
stays suspended for ever", where openverse cancels the task that awaits a
cancelled one (an extension, `Task.Cancel` being unreleased in the pinned
Book): with records, a cancellation must reach the awaiters through them,
and when it does (at the cancel, inside it, or at the awaiter's next poll)
is a decision for the owner before the rule can be built as carefully as
the event rule was.

### A task's end resumes its awaiters

Rule 13, with the Book's rule for a cancelled task, which the owner's
standing rule ("for everything we go by the book") decides: openverse
follows the Book on both. This section pins every consequence (the API
reference `docs/api/verse_runtime_api.html` by line, ch. 14
`docs/14_concurrency.md` by line, tests under `Tests/` by file and line),
says what openverse did before, and gives the design and what was built.

#### The rules, pinned

The API's `task` (line 1362), its `Await`: "Returns immediately only when
the task has already reached the "completed" phase. Every other phase
suspends, and that includes both directions of the obvious hazard: a
cancelled task never resumes its awaiters, so the call does not fail, does
not error, and simply stays suspended for ever. [...] Multiple awaiters
are allowed and are resumed in the order they registered. If the awaiting
task is itself cancelled it deregisters automatically, so the completed
task will not try to resume a dead caller."

1. **Order: the order they registered.** Line 1362, above.
   `Coroutines/SpawnAndTask.versetest:292-321` (`TestAwait3`): three arms
   of one `sync` await one task; A and C register as the `sync` starts, B a
   tick later; the log `aYbA1B1C1,B2,ZA2C2B3,C3c,d,` has A2, C2, B3, the
   order they registered, not the arms' (A, B, C).
2. **When: inside the ending task's last step, each awaiter until it waits
   again or ends before the next.** The task's end resumes them before the
   code that ran that step goes on, and before any other task runs.
   `Bugs/FORT-1088027-UseOfNullInitializedDynamicallyTypedValue.versetest:6-9`:
   "a bytecode-issued Signal during `task::Update` synchronously re-enters
   Update for the same task via `event::Signal → task::Complete → ResumeAt
   → task::Update`": completing a task (`task::Complete`) resumes what
   awaits it (`ResumeAt`, then its `Update`) synchronously, inside the call
   that completed it. `SpawnAndTask.versetest:292-321`: the task logs Z
   and ends; in the same tick A2, then C2, whose arm then waits a tick
   (`Wait(1)`), then B3: C ran to its next wait before B went on.
   `:269-288` (`TestAwait`, `aYb,cA,ZCd,e,`): the awaiter's `C` and `d`
   right after the task's last `Z`. `:688-737` (`TestYieldToCanceling`,
   `verse_vm_only`, `,UabXcVWdfhYZ`): `E2.Signal(0)` resumes a spawned
   task, which ends inside that `Signal` (`V`, its defer's `W`) and, as the
   test's comment says, "Complete spawned task to resume parent via yield
   (no-op)": its end resumes its awaiter at once (a no-op: the awaiter is
   being cancelled, and its `g` never comes), before the signaller's `d`.
   Checked: in every test with a task's awaiters
   (`SpawnAndTask.versetest` 269-321, 688-737, 895-913,
   `Coroutines/Concurrency.versetest:1528-1540`), no other task is ready to
   run at the tick the task ends, so none can tell "inside the end" from
   "at once after it", and none contradicts the first.
3. **What the code that ran the ending task sees.** That code (the
   scheduler's pass, a `Signal` that resumed the task, another task's end
   that did) goes on only once every awaiter has run to its next wait or
   end, and sees what they did (`TestYieldToCanceling`: `d` after `VW` and
   the awaiter's turn). The task's parent, the code that spawned it, is not
   involved as such: "Awaiting is not owning. The awaited task is not
   registered as a subtask of the awaiting one, so cancelling the awaiter
   leaves the task running" (line 1349); it sees the end as an awaiter if
   it is one.
4. **The value.** Each awaiter gets the task's result, the same one: ch. 14
   `:920-921`, "suspends the calling context until the task completes,
   then returns the task's result"; `:926-927`, "the result is sticky. It
   can therefore be called multiple times, and awaiting the same task
   repeatedly always gives the same result" (`<!-- 19 -->`, `:931-949`,
   `Pair(0) = Pair(1)`).
5. **A task that has ended** gives its result at once, without suspending:
   line 1362 ("Returns immediately only when the task has already reached
   the "completed" phase"); ch. 14 `:924-925`; `SpawnAndTask.versetest:325-338`
   (`Zcd`: the second `Await` lets no tick pass); `<!-- 21 -->`
   (`:977-1001`: awaits of tasks that ended in their first runs, checked
   right after the `spawn`).
6. **Several awaits of one task by one task** (arms of a `sync`, `race` or
   `rush`, a branch and its function): each is an awaiter of its own,
   registered when it waits, resumed in that order among the others
   (`TestAwait3`: A and C, arms of one `sync`).
7. **A task awaiting itself, or a cycle** (A awaits B, B awaits A): the
   awaited task is active, so the `Await` suspends ("Every other phase
   suspends", line 1362), and the task cannot complete while its own code
   waits there: the await waits for ever, unless it is cancelled (a `race`
   it loses, the exit of the function whose branch or `rush` arm it is in),
   when it deregisters. No test.
8. **What ends a task, and its awaiters.**
   - *Its function returns*: the task completes; its awaiters resume as
     above, with its result.
   - *`T.Cancel()`*: the task is cancelled; its awaiters are never resumed
     (line 1362, `Await` above, and `Cancel`: "If this task has a caller or
     calls to Await(), they will not be notified (or canceled) and will
     appear to take forever"): [the cancelled task](#the-cancelled-task),
     below.
   - *A `race` or `rush` loser*: an arm is no `task(t)` ("the only way to
     obtain a task is from a spawn expression", line 1349), so nothing
     awaits it. An awaiter that is a losing arm is cancelled as the race
     resolves and deregisters (line 1362, "If the awaiting task is itself
     cancelled it deregisters automatically"); the task it awaited goes on
     (line 1349). A `rush` loser that goes on is an awaiter like any.
   - *The program's end*: a standalone program ends when `Main` does, and
     an unfinished task neither completes nor is cancelled then (openverse's
     host rule, [Creator and host lifetime](#observable-rules)), so its
     awaiters are not resumed: nothing runs after. The Book has no program
     end: its tests spawn, tick a fixed number of times, check, and leave
     what still waits as it is (`SpawnAndTask.versetest:342-355`, below).
9. **Rollback.** A task's step runs inside a failure context only (a) as
   its first run, in a `spawn` in a failure context, when nothing can
   await it yet (the task is given out when `spawn` returns), and the
   whole first run, its end included, is undone with the context; or (b)
   inside a `Signal` made in one (rule 11), or inside another task's end
   that such a `Signal` reached: its end and the awaiters it resumed are
   then undone with the context, the task and its awaiters back where they
   waited, as a `Signal`'s awaiters are (`Coroutines/Concurrency.versetest:1562-1580`).
   `Concurrency.versetest:1528-1540` (`TestRollbackNativeDefer`, an
   awaiter resumed by a task's end calls `Err()`) is an
   `assert_runtime_error` with `CoroUtils` (not translatable).
10. **Inside the `Signal` machinery.** A task that ends inside a
    `Signal`'s round (an awaiter that ends there), or inside another task's
    end, resumes its own awaiters there, depth first, before the round it
    is in goes on (rule 6, applied to an end: the FORT comment's
    `event::Signal → task::Complete → ResumeAt`; `TestYieldToCanceling`). An
    awaiter that signals an event inside a task's end runs that event's
    round inside its turn. As inside a `Signal`, only the awaiters go on: a
    sleep that expired meanwhile keeps its turn in the scheduler's pass
    (rule 14). An `Await` made inside the end, of the task that ends, gives
    its result at once (5).

**openverse before this change.** A task's end marked it done; its
awaiters went on when the scheduler polled them, in its order (`Main`, then
the roots in start order, arms in source order): later in the same pass
for a root after the task's, in another pass of the same tick for one
before it (`ZA2B3C2` for `TestAwait3`). An await of a cancelled task, made
before the cancel or after it, asked for the root it ran in to be
cancelled (#156, #253): the whole task, or a `branch` or `rush` loser
alone, or `Main`, which ended the program after its defers ran, exit 0.
Rules 4, 5 and 7 held; 9 and 10 held for the `Signal`s, the end itself
resuming nothing.

#### The cancelled task

- **The API** (line 1362): `Await`, above ("a cancelled task never resumes
  its awaiters, so the call does not fail, does not error, and simply
  stays suspended for ever"), and `Cancel` ("If this task has a caller or
  calls to Await(), they will not be notified (or canceled) and will appear
  to take forever"). The first is in the entry of `Await`, the one public
  member ("Of its members only Await is public. The phase predicates
  (Active[], Completed[], Canceling[], Canceled[] and their groupings) and
  Cancel() are all epic_internal", line 1349), under no "unreleased" label;
  but only `Cancel` makes a task cancelled, and `Cancel` is
  `Cancel<native><epic_internal>()<suspends>:void` in the API (line 1362)
  and, in ch. 14, "Unreleased Feature: The Cancel() method has not been
  released at this time" (`:873-876`). openverse has `T.Cancel()` as an
  extension (Sources, above): the rule says what its awaiters do.
- **Ch. 14 disagrees** (`:927-929`): "And it propagates cancellation: if
  the awaited task was canceled, `Await()` passes that cancellation on to
  the caller", openverse's extension until now.
- **The tests decide neither.** `SpawnAndTask.versetest:342-355`
  (`TestAwaitCanceled`): a task cancels a task it spawned, then awaits it;
  `aYbc,,,`, its `d` never logged, under either reading (no defer, nothing
  else to tell them apart). The wiki's *Where the Book disagrees with
  itself* has no entry for it (checked: one to add).
- **openverse follows the API**, as the owner decided, and as for how many
  awaiters one `Signal` wakes, where ch. 14 conflicts and the API decides:
  an await of a cancelled task, made before the cancel or after it, stays
  suspended for ever. It does not fail, error or cancel anything.
- **The awaiter can still be cancelled**: a `race` arm awaiting a cancelled
  task is a loser like any other when another arm resolves the race (it is
  cancelled then, its defers run, and it deregisters); a branch is stopped
  when its function exits; a task by `T.Cancel()`.
- **A program whose `Main` awaits a cancelled task.** `Main` never goes on.
  The other tasks go on while they can; when none can run again, the
  scheduler's rule for a `Main` that waits with no task able to run
  applies (LANGUAGE.md, "The program"; [deadlock](../../tests/verse/scheduler_audit_deadlock.verse)):
  the program ends as `Err()` does, `error: user`, exit 2, `Main`'s defers
  not run. So no program hangs that would not hang without the rule: a
  stalled `Main` is found as after `Sleep(Inf)`, and a program that runs
  for ever has a task that never stops waking, rule or no rule. With an
  immediate `Main` the program ends when `Main` does, as always, the
  awaiter left where it waits. The Book's test runner has no such end: an
  assertion runs its code, ticks (`Tick(3)`), checks its log, and leaves
  the tasks that still wait (`TestAwaitCanceled`'s task stays at its
  `Await`).

#### openverse's tests of the retired extension

The suite's tests whose subject is that an await of a cancelled task
cancels the awaiter (#156, #253, #261), by name in `tests/verse`:
`task_cancel` (one of its four parts), `task_cancel_main`,
`task_cancel_imm_main`, `task_cancel_first_run`, `task_cancel_first_run_chain`,
`task_cancel_first_run_generic`, `task_cancel_first_run_branch`,
`task_cancel_branch_generic`, `task_cancel_nested_first_runs`,
`task_cancel_race_arm`, `task_cancel_race_loser_then_end`,
`task_cancel_rush_loser`, `task_cancel_rush_loser_later`,
`task_cancel_sync_arm_then_spawn_main`, `task_cancel_sync_arm_then_spawn_task`,
`task_cancel_siblings_after_arm_await`, `task_cancel_await_during_unwind`;
and `task_cancel_branch_defer_recancel`, which uses it to cancel a branch
before testing #261. Each is rewritten to the Book's behaviour or deleted
([as built](#a-tasks-end-as-built) lists which).

