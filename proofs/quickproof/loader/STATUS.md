# Status of openverse_loader

- Law: `project/harness/loader_wellscoped.c`, pinned to openverse commit 7336cd864b97 (float math,
  #132). That commit left `load.c` unchanged and raised `VX_P_LAST` in `openverse.h` from 46 to 58 (the
  mathematical functions of floats), as the float commit (4006a49d863c, #127) had from 28 to 46 (a
  float literal is `PRIM fofBits` of an INT literal, so the literal kinds are unchanged); the
  specification's bound on a PRIM code in `proof/src/proof/Specs.v` follows, and the rest of the proof
  replays unchanged. The heap commit (8faa3ffa5a6e, #31) before it added HEAP nodes
  (tag 12) and REF literals (kind 6) to `load.c`; the law claims for a HEAP node an op `<= VX_H_LAST`,
  `k == 0` for tag, its arguments as for PRIM and CALL, and for an isTag at most `VX_MAX_TAGS` class
  tags whose 4m bytes lie inside the bytes pool.
- `qp check`: native runs (ASan/UBSan, 3,000) ok; CompCert interpreter (20 runs) no stop; VST lint clean;
  mutants 6/40 killed (`CHECK.md`, read in `CHECK-NOTES.md`).
- **Proof: `loader_wellscoped` PROVED, `qp verify` PASS** (`VERIFY.md`); axioms: 13, standard + VST
  malloc.
- Proof sources: `proof/src/` — 3,910 lines of Coq in 18 files, written by an AI agent in about 9 h 20 min
  and extended for the heap commit in about 4 h:
  - `Specs.v`: one specification for each function of `load.c`. The readers return some value with
    its range facts; the node checks give `node_ok`, `check_calls` gives `call_ok`, and a `freeable`
    predicate describes a partly built program on the error paths. `load_heap_spec` has the shape of
    `load_prim_spec`; its body proof (in `Args.v`) also adds an isTag's tags to the bytes pool, as
    `load_lit`'s adds a string's bytes.
  - `Readers.v`, `Fields.v`, `Args.v`, `Lit.v`, `Node.v`, `Nodes.v`, `Pools.v`, `Trim.v`, `Check.v`,
    `Fn.v`, `Header.v`, `Free.v` and `LoadAll.v`: the body proofs, with `Lemmas.v`, `LoadLemmas.v` and
    `NodeLemmas.v`.
  - `contracts/loader_wellscoped.v`: the proof of the law's `main` and the theorem.

  `qp verify` checks them in about 33 minutes with 6 build jobs.
- Limits of the law, as its first comment says:
  - it covers buffers of up to 4096 bytes;
  - it does not claim completeness (that every well-formed buffer is accepted);
  - on an error it asserts only `nfns == 0` and that the three pointers are NULL, not that `nargs`,
    `nbytes` and `entry` are 0. `cverse` never runs a program that failed to load: it exits with code 4.
- Practical notes: the law's Clight (`harness/.../code.v`) and `load.c`'s Clight (`load/code.v`) name the
  same structs separately. The proof of `main` converts between them with `change`; without it one step
  took over 25 minutes to check. The proof of `main` also wraps the ten facts of `node_ok` in `hide`
  before it uses them: `lia`, which VST's tactics call at every step, splits cases on each implication in
  the context. With the HEAP fact added and nothing hidden, one `qp_assert` step took about 7 minutes and
  `main` up to the end of its SEQ branch 22 minutes (in `coqtop`); hidden, a few seconds and 4 minutes.

So for every input of up to 4 KiB, `vx_load` reads only inside the buffer. When it accepts, the program
satisfies every condition of `docs/FORMAT.md` (HEAP nodes and REF literals included), which includes
`Prog.WellScoped`, so by `Eval.scoped_ok` its Verse Core semantics raises no slot or call error. In every
case `vx_free_program` frees only live blocks.
