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
| Clock and positive delays | The Book uses simulation updates. Epic permits variable update durations, independent of rendering. Neither cited timing description specifies a fixed 30 Hz rounding rule. | A virtual 30 Hz clock skips idle ticks. Supported nonnegative finite delays use `max(1, Round(30*S))` after binary64 multiplication and ties-to-even rounding. In [sleep](../../tests/verse/scheduler_audit_sleep.verse), `Sleep(0.04)` completes with the first one-tick sleeper. | Explicit reference timing policy; no engine-rate claim. The previous language-table attribution of upward rounding to the Book was unsupported and is removed. |
| Zero delay | The pinned Book's NextTick discussion permits same-tick resumption for `Sleep(0.0)`. Epic's Sleep page specifies the next update. | Zero always yields and resumes in the next virtual tick; a peer runs before resumption in [sleep](../../tests/verse/scheduler_audit_sleep.verse). | Matches the published Sleep description; the Book snapshot differs. |
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
`max(1, RoundEven(P))` ticks. The guard precedes integer conversion: a finite
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
reference behavior; both signed zeros and positive subnormals yield at
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
