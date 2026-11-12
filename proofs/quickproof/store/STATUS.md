# Status of openverse_store

- Law: `project/harness/store_rollback_model.c`, pinned to openverse commit 805fd2194515 (scalar float math, #490). That commit changed only `openverse.h` among the pinned files (hyperbolic prim codes 59-64); the
  proof replays unchanged.
- `qp check`: native runs (ASan/UBSan, 3,000) ok; CompCert interpreter (20 runs) no stop; VST lint clean;
  mutants 26/40 killed (`CHECK.md`, read in `CHECK-NOTES.md`).
- **Proof: `store_rollback_model` PROVED, `qp verify` PASS** (`VERIFY.md`); axioms: 12, standard + VST
  malloc.
- Proof sources: `proof/src/` — 2,287 lines of Rocq in 19 files, written by an AI agent in about 6 h:
  - `Model.v`: the rollback rule as a pure invariant (`chain`). A functional `undo` replays the journal
    newest first. Each open context's snapshot is the current state with the journal undone back to its
    mark, and each outer context's snapshot relates to the state at that mark in the same way.
  - `StoreSpecs.v`, `StoreSimple.v`, `StoreSet.v`, `StoreRollback.v` and `StoreAppend.v`: one
    specification for each store function the law reaches, over `store_rep` (the struct, slots and
    journal) and `out_rep` (the output buffer), together with the body proofs.
  - `Law.v`, `MainLib.v`, `MainInv.v`, `Step*.v` and `MainProof.v`: one lemma for each operation and
    one for the checks after a step, joined by the invariant of the 32-step loop.
  - `contracts/store_rollback_model.v`: the theorem.

  `qp verify` checks them in about 12 minutes with 4 build jobs.
- Coverage, noted by the proof: every journal entry names a slot below `nslots`, so under this law the
  `sl < s->nslots` test in `vx_store_rollback` is never false. The test only defends against a corrupted
  journal, and the theorem says nothing about that branch.

So `vx_store_mark`, `vx_store_set`, `vx_store_out_append`, `vx_store_rollback` and `vx_store_commit` keep the
transactional state of `Eval.ite_fail` and `EvalFor.skip` for every sequence of 32
operations on up to 3 nested contexts and 4 slots with any initial contents, and journal and output
capacities up to 8, with every memory access in
bounds.
