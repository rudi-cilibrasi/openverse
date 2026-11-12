# qp verify of openverse_store

Replayed on 2026-11-12 by `scripts/check-quickproof.sh --check store`,
with the published image pinned in the script. The C contract is assembled
from `805fd2194515789c7ad0f43689071113031e75f2` (scalar float math #490).
Only `openverse.h` changed among this law's C dependencies; the primitive
range now ends at 64. This law does not prove libm accuracy.

# Verification of <work> at d7323acdfa91

- date: 2026-11-12 01:10
- framework: quickproof/ at fab76ef826ae (not a release tag of this verifier's repository)
- framework trusted files (16: the statement, the libc, the translation chain): identical to this verifier (/opt/quickproof)
- contract commit: aa1e4723df8a (`contract`)
- files changed since the contract: 19; frozen files changed: none
- regenerated code.v: identical to the committed files
- the statements compared with: the contract commit's own files with no proof in them (none) and its unit files (src/units.v or src/units/*.v); generated again: src/contracts/store_rollback_model.v
- elaborated statement and whole_prog of `store_rollback_model`: identical to the contract
- `Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture` in the Coq sources of the proof (src/ and the other files of _CoqProject; comments excluded): none
- `Print Assumptions` was printed once for all theorems together (of a definition that names each of them): the axioms given for each theorem are those of all of them, an upper bound of its own
- the framework after the translation and the builds: unchanged
- the run: 4 build jobs on 12 CPUs, load 6.7 at the start; checks before the build 0 min, the build and probes 9 min, the contract commit 0 min, in all 10 min

| theorem | result | Print Assumptions |
|---|---|---|
| `store_rollback_model` | PROVED | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token_local_facts, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq, library.create_mem_mgr, Classical_Prop.classic, Ensembles.Extensionality_Ensembles |

PASS means: the frozen files, the regenerated Clight and every statement are those of the contract, every statement is QuickProof.Contract.harness_safe on this verifier's framework, and every claimed theorem is proved.

**Verdict: PASS (exit 0).**
