# openverse_store: harness check

By `tools/qp check` on 2026-11-04 20:28: upstream 7c0444b2117b, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `store_rollback_model` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `store_rollback_model` | ok (20 runs, no stop; 5 timed out) |

## Mutants (300 runs per harness and mutant)

40 mutation sites in the code under test; 40 mutants run (0 skipped as dead code, 0 not compiling).
Killed by some harness: **26/40**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `store_rollback_model` | 26/40 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `runtime/src/store.c:72` in `vx_store_put`: `if (slot >= s->nslots)` with `>`
- `runtime/src/store.c:181` in `vx_store_move_out`: `if (ocap < s->olen)` with `<=`
- `runtime/src/store.c:154` in `vx_store_move_slots`: `for (i = 0; i < s->nslots; i++) {` with `<=`
- `runtime/src/store.c:166` in `vx_store_move_journal`: `if (jcap < s->jlen)` with `<=`
- `runtime/src/store.c:101` in `vx_store_rollback`: `if (s->olen > m->olen)` with `>=`
- `runtime/src/store.c:183` in `vx_store_move_out`: `for (i = 0; i < s->olen; i++)` with `<=`
- `runtime/src/store.c:128` in `vx_store_forget`: `if (jlen < s->jlen)` with `<=`
- `runtime/src/store.c:154` in `vx_store_move_slots`: `for (i = 0; i < s->nslots; i++) {` with `1`
- `runtime/src/store.c:168` in `vx_store_move_journal`: `for (i = 0; i < s->jlen; i++) {` with `<=`
- `runtime/src/store.c:183` in `vx_store_move_out`: `for (i = 0; i < s->olen; i++)` with `1`
- `runtime/src/store.c:96` in `vx_store_rollback`: `if (sl < s->nslots) {` with `<=`
- `runtime/src/store.c:85` in `vx_store_mark`: `s->depth = s->depth + 1;` with `2`
- `runtime/src/store.c:152` in `vx_store_move_slots`: `if (nslots < s->nslots)` with `<=`
- `runtime/src/store.c:168` in `vx_store_move_journal`: `for (i = 0; i < s->jlen; i++) {` with `1`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
