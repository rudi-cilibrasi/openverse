# Status of openverse_loader

- Law: `project/harness/loader_wellscoped.c`, pinned to openverse commit 7c0444b2117b.
- `qp check`: native runs (ASan/UBSan, 3,000) ok; CompCert interpreter (20 runs) no stop; VST lint clean;
  mutants 8/40 killed (`CHECK.md`, read in `CHECK-NOTES.md`).
- **Proof: `loader_wellscoped` PROVED, `qp verify` PASS** (`VERIFY.md`); axioms: 13, standard + VST
  malloc.
- Proof sources: `proof/src/` — 3,707 lines of Coq in 18 files, written by an AI agent in about 9 h 20 min:
  - `Specs.v`: one specification for each function of `load.c`. The readers return some value with
    its range facts; the node checks give `node_ok`, `check_calls` gives `call_ok`, and a `freeable`
    predicate describes a partly built program on the error paths.
  - `Readers.v`, `Fields.v`, `Args.v`, `Lit.v`, `Node.v`, `Nodes.v`, `Pools.v`, `Trim.v`, `Check.v`,
    `Fn.v`, `Header.v`, `Free.v` and `LoadAll.v`: the body proofs, with `Lemmas.v`, `LoadLemmas.v` and
    `NodeLemmas.v`.
  - `contracts/loader_wellscoped.v`: the proof of the law's `main` and the theorem.

  `qp verify` checks them in about 43 minutes with 4 build jobs.
- Limits of the law, as its first comment says:
  - it covers buffers of up to 4096 bytes;
  - it does not claim completeness (that every well-formed buffer is accepted);
  - on an error it asserts only `nfns == 0` and that the three pointers are NULL, not that `nargs`,
    `nbytes` and `entry` are 0. `cverse` never runs a program that failed to load: it exits with code 4.
- Practical note: the law's Clight (`harness/.../code.v`) and `load.c`'s Clight (`load/code.v`) name the
  same structs separately. The proof of `main` converts between them with `change`; without it one step
  took over 25 minutes to check.

So for every input of up to 4 KiB, `vx_load` reads only inside the buffer. When it accepts, the program
satisfies every condition of `docs/FORMAT.md`, which includes `Prog.WellScoped`, so by `Eval.scoped_ok`
its Verse Core semantics raises no slot or call error. In every case `vx_free_program` frees only live blocks.
