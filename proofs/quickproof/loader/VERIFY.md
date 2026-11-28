# qp verify of openverse_loader

Replayed on 2026-11-28 by `scripts/check-quickproof.sh --check loader`,
with the published image pinned in the script. The C contract is assembled
from `92b862fa4f5fffe7e9b753448e5619b82e076bfe` (a map's lookups, mapGet and mapFind, #795).
The loader source is unchanged; the header and the proof specification
now permit primitive codes through 66.

# Verification of <work> at 0dea9f32a575

- date: 2026-11-28 03:41
- framework: quickproof/ at fab76ef826ae (not a release tag of this verifier's repository)
- framework trusted files (16: the statement, the libc, the translation chain): identical to this verifier (/opt/quickproof)
- contract commit: 07059c010130 (`contract`)
- files changed since the contract: 18; frozen files changed: none
- regenerated code.v: identical to the committed files
- the statements compared with: the contract commit's own files with no proof in them (none) and its unit files (src/units.v or src/units/*.v); generated again: src/contracts/loader_wellscoped.v
- elaborated statement and whole_prog of `loader_wellscoped`: identical to the contract
- `Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture` in the Coq sources of the proof (src/ and the other files of _CoqProject; comments excluded): none
- `Print Assumptions` was printed once for all theorems together (of a definition that names each of them): the axioms given for each theorem are those of all of them, an upper bound of its own
- the framework after the translation and the builds: unchanged
- the run: 12 build jobs on 24 CPUs, load 28.1 at the start; checks before the build 0 min, the build and probes 35 min, the contract commit 0 min, in all 35 min

| theorem | result | Print Assumptions |
|---|---|---|
| `loader_wellscoped` | PROVED | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token_valid_pointer, library.malloc_token_local_facts, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq, library.create_mem_mgr, Classical_Prop.classic, Ensembles.Extensionality_Ensembles |

PASS means: the frozen files, the regenerated Clight and every statement are those of the contract, every statement is QuickProof.Contract.harness_safe on this verifier's framework, and every claimed theorem is proved.

**Verdict: PASS (exit 0).**
