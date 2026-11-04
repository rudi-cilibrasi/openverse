# Reading the mutants of store_rollback_model

`qp check` kills 26 of 40 mutants of `runtime/src/store.c` (`CHECK.md`). The
law went through three rounds, all before any proof. The first, with uniform
operations and an assume inside the loop, killed 18. Then a model of the
journal length pinned exactly when `VX_EFULL` may occur, and a check that
`vx_store_get` rejects an index out of range was added. Finally the run was
lengthened to 32 operations, with an operation mix that nests contexts more
often (`project/env/store_rollback_model.c`). A mutant that clears the
journal on leaving an *inner* context was killed by a native run of 2
million inputs before the change, and is killed by `qp check` after it.

| Survivors | Reading |
|---|---|
| 11 in `vx_store_move_slots`, `vx_store_move_journal`, `vx_store_move_out`, `vx_store_put`, `vx_store_forget` | not claimed: the law does not call them (they are the interpreter's frame and buffer management) |
| `vx_store_rollback`: `olen > m->olen` → `>=` | equivalent: at equality the assignment changes nothing |
| `vx_store_rollback`: `sl < s->nslots` → `<=` | equivalent under the store invariant: every journal entry has `slot < nslots` (`vx_store_set` checks it) |
| `vx_store_mark`: `depth + 1` → `depth + 2` | equivalent: `depth` is only compared with 0 and restored from marks |
