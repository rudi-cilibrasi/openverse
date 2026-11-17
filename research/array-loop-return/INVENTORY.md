# Array loop return slice — unvalidated working artifact

Base: ac7963b5a312082d480e13bc7094d0e0895ddefe (the reviewed #697 implementation, including actual private-cell metadata, source-effect, ownership and #699 packet fixes). This tree has no copied cache and has not been built or tested. The Source patch is local only. No PR or issue has been published.

## Existing isolated research

- general309b: ordinary `loop` return/break protocol, definite-exit backedge omission, initializer return-arm exposure, plus nested `$then` detection. It is NOT an array-iteration implementation. Eight target/control fixture pairs; prior research evidence does not validate the ac-based feature.
- nested a0c509: nested ordinary returning loops over the general slice; 27 Choice lines and two target/control pairs. It is not part of this patch.
- nested-range ebe664: nested scalar integer-range failure boundaries; 18 Choice lines and three target/control pairs. It is not part of this patch.
- None of those commits is cherry-picked here: they inherit an older metadata foundation. In particular, no old metadata or effect implementation replaces ac.

## Actual new patch

`Choice.lean` extends the existing typed-site lazy range protocol to ONE ordinary array generator (`for (Item : Source)`), where Source and normal body have no multi-valued operation. A checking-only block inside the original header notes the source's selected array type using the existing `$noteTypes` protocol. Source still occurs once there. The generated runtime code evaluates Source once in its header failure context, then passes an immutable array snapshot to the recursive helper. An indexed, locally failable lookup binds the original item name; the last element ends before incrementing. Operand saving, logical mutable cells, reached cleanup, inference/evidence captures and source admission remain the existing ac machinery.

This is not yet a compiled implementation. In particular, inspect/check:

- the checking-only source value block must preserve original header effect/failure/selected-world admission;
- empty or failing Source must match ordinary `for` rollback/exhaustion; successful empty arrays with source effects require an actual old-main oracle;
- an owned return with zero operands must abort the producer, not become normal exhaustion;
- source snapshot versus mutable source binding and heap elements, branch/function cleanup between return alternatives, first success, rejection and unused `Err()` alternatives;
- generic element/return types and transitive bounds, selected-world captures, real/dummy evidence and callable/object payload roles;
- source `<computes>` permissions, Signal policy, lexical shadowing/default/method scope, existing invalid returns;
- exact native 15s/4GiB 17/32/64 growth, reader18 controls, full gate, pinned Book and independent review after the quiet window.

Map/string/indexed-generator forms, multiple generator/filter clauses, multi-valued source expressions, nested returning loops, arbitrary normal multi-valued bodies and mutable implicit proof captures remain out of this finite slice. They are valid remaining implementation obligations, not newly invalid source. #686 stays open.

## Prepared controls

`cases/basic*` has noncontiguous values (4,7,9) so confusing cursor with item is observable; target/control cover hit, normal exhaustion, empty array, all/first/reject/option/first. Its scalar-array control is independent of the new helper and has no stateful operands.

`cases/empty_operand*` uses an empty failable operand and `Err()` sentinels in the next row and suffix. The independent ordinary return control must confirm termination even when zero values are produced.

`cases/source_failure*` pairs the new form with an existing scalar-return array loop, preserving the original header rather than assuming that a successful empty source commits or rolls back effects. NO expected trace is asserted until old-main controls run after the quiet window.

Files ending `.expected.unverified` are proposed hand oracles only, not passing evidence or registered regression fixtures. Nothing has run.

## Integration hold

The ac foundation is now held on an independently reproduced existing-source compilation regression (`multi_nested_groups`), reported during its full gate. This array artifact must rebase onto the corrected, validated #697 implementation before any final candidate or gates. It does not work around that regression or replace any metadata code.
