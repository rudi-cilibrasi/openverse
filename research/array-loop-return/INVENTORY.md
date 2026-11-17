# Array loop return slice — unvalidated working artifact

Integration base: PR #697 at `1fb802acc1d52684ae5f0811de623947f029ff54`. The array code remains local and has yet to be built or tested. The original research branch remains available at `2f082273`.

## Existing isolated research

- general309b: ordinary `loop` return/break protocol, definite-exit backedge omission, initializer return-arm exposure, plus nested `$then` detection. It is NOT an array-iteration implementation. Eight target/control fixture pairs; prior research evidence does not validate the ac-based feature.
- nested a0c509: nested ordinary returning loops over the general slice; 27 Choice lines and two target/control pairs. It is not part of this patch.
- nested-range ebe664: nested scalar integer-range failure boundaries; 18 Choice lines and three target/control pairs. It is not part of this patch.
- None of those commits is cherry-picked here: they inherit an older metadata foundation. In particular, no old metadata or effect implementation replaces ac.

## Actual new patch

`Choice.lean` extends the existing typed-site lazy range protocol to ONE ordinary array generator (`for (Item : Source)`), where Source and normal body have no multi-valued operation. A checking-only block inside the original header notes the source's selected array type using the existing `$noteTypes` protocol. Source still occurs once there. The generated runtime code evaluates Source once in its header failure context, then passes an immutable array snapshot to the recursive helper. An indexed, locally failable lookup binds the original item name; the last element ends before incrementing. Operand saving, logical mutable cells, reached cleanup, inference/evidence captures and source admission remain the existing ac machinery.

This is not yet a compiled implementation. In particular, inspect/check:

- the checking-only source value block must preserve original header effect/failure/selected-world admission;
- empty or failing Source must match ordinary `for` rollback/exhaustion. The array length guard in the generated header keeps the source's writes on the failing path for an empty array. Compare this against the measured control trace;
- source snapshot versus mutable source binding and heap elements, branch/function cleanup between return alternatives, first success, rejection and unused `Err()` alternatives;
- generic element/return types and transitive bounds, selected-world captures, real/dummy evidence and callable/object payload roles;
- source `<computes>` permissions, Signal policy, lexical shadowing/default/method scope, existing invalid returns;
- exact native 15s/4GiB 17/32/64 growth, reader18 controls, full gate, pinned Book and independent review after the quiet window.

Map/string/indexed-generator forms, multiple generator/filter clauses, multi-valued source expressions, nested returning loops, arbitrary normal multi-valued bodies and mutable implicit proof captures remain out of this finite slice. They are valid remaining implementation obligations, not newly invalid source. #686 stays open.

## Prepared controls

`cases/basic*` has noncontiguous values (4,7,9) so confusing cursor with item is observable; target/control cover hit, normal exhaustion, empty array, all/first/reject/option/first. Its scalar-array control is independent of the new helper and has no stateful operands.

Both profiles on main `07ae0c6f` produce the same basic and source-failure control traces in Lean and C. The files ending `.control.expected` record those traces for use when validating the array helper. They are research fixtures. The helper itself has yet to run.

The source-failure control distinguishes a failed source, a successful empty array, a selected return and an all-rejected search. In both the failed and empty cases, the suffix yields 99 and 100 with the source write rolled back. The selected return commits one write. The all-rejected search rolls it back.

`cases/empty_operand*` are source-admission controls. Main `07ae0c6f` and PR #697 at `1fb802ac` both reject these cases in both profiles because the return in a `<decides>` function is outside tail position.

## Integration hold

The isolated integration branch includes the newer #697 corrections. Its array code needs a native build and focused comparisons against the controls before it is ready for review. PR #697's own validation runs in a different worktree.
