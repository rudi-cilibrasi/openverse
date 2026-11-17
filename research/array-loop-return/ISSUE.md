# Proposed finite issue: lazy return operands in one ordinary array generator

This is a proposed narrower follow-up within open #686, after #697's integer-range slice. Do not close #686 or reopen #283.

Valid source to support:

```verse
ArrayReturn(Items:[]int)<computes>:int=
    for(Item:Items):
        if(Item=7):return Item*10|Item*10+1
    99|100
Main():void=
    for(V:=ArrayReturn(array{4,7,9})){Print("value {V}")}
    if(V:=ArrayReturn(array{4,7,9}),V=71)then Print("first {V}")else Print("bad")
```

Proposed complete oracle (to verify on an independent control before publishing):

```text
value 70
value 71
first 71
```

An independent scalar-return control returns `[]int`, uses the same ordinary array `for`, returns `array{Item*10,Item*10+1}`, and falls through to `array{99,100}`. Its callers iterate that array or use `K:=0|1, V:=Control(...)[K]` for first-success search. Full source/control files and proposed oracles are under `cases/`.

Finish when one single-valued array Source and one generator with an ordinary single-valued normal body support lazy multi-valued owned return operands. Source evaluates once in its original header failure context; a failed or empty source permits ordinary exhaustion/fallback with the same rollback as the scalar control. Once an owned return is reached, even an EMPTY operand terminates that invocation: no later row or suffix. Save each value before reached cleanup; reevaluate the next operand after preceding row/function cleanup, and skip unused alternatives after first success. Preserve storage, lexical scope, registration reach, cleanup LIFO, selected types/evidence, metadata roles and source effect/failure/Signal policies.

Require permanent complete Lean/C all/first/reject/option controls in both source profiles; independent mutable/cleanup/rollback and failing-source controls; unchanged 15-second/4GiB resource checks at 17/32/64; all18 reader controls; full native gate, pinned Book and independent review. Keep nested/multiple/choice-source loop obligations open separately. This artifact and patch have NOT been built or tested; no passing claim is made.
