# Status of openverse_arith

- Law: `project/harness/arith_exact.c`, pinned to openverse commit 7c0444b2117b.
- `qp check`: native runs (ASan/UBSan, 3,000) ok; CompCert interpreter (20 runs) no stop; VST lint clean;
  mutants 29/40 killed (`CHECK.md`, read in `CHECK-NOTES.md`: 10 equivalent, 1 reachable only at
  `(INT64_MIN, -1)`).
- **Proof: `arith_exact` PROVED, `qp verify` PASS** (`VERIFY.md`); axioms: 10, standard + VST malloc.
- Proof sources: `proof/src/` — 1,338 lines of Coq in 7 files (pure Z lemmas `ArithZ.v`, the nine
  function specifications `ArithSpecs.v`, body proofs `ArithBasic.v`/`ArithDiv.v`, the harness helpers
  `Helpers.v`, and `main` with the theorem in `contracts/arith_exact.v`), written by an AI agent in
  about 1 h 13 min. `qp verify` checks them in about 5 minutes.

Together with `OpenVerse/Core/Seams.lean` (`docs/SEAMS.md`), this proves that `vx_add`, …, `vx_modulo`
compute `Prim.apply` on every pair of 64-bit inputs.
