# qp verify of openverse_loader

Run by `scripts/check-quickproof.sh loader` (with `QP_JOBS=4`) on 2026-11-04: a contract freshly assembled from the
pinned openverse commit, with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_loader-proof at 3925480cce52
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 18 files changed since the contract (`contract`), none of them frozen
[0:01] Clight generated again: identical to the committed files
[1:21] build: 10/26 files
[1:21] build: 11/26 files
[1:33] build: 13/26 files
[2:55] build: 16/26 files
[4:44] build: 19/26 files
[6:14] build: 21/26 files
[10:25] build: 24/26 files
[18:35] build: 26/26 files
[42:38] build: 26/26 files, 2557 s
[42:39] statements and axioms: 1 theorem probed
[43:05] the contract commit f46de0595406: a clone, its statements built without the proof
[43:11] build of the contract commit: 7/7 files, 5 s
[43:12] statements and axioms of the contract commit: 1 theorem probed
[43:18] statements compared with the contract: identical
[43:18] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem            result  axioms
loader_wellscoped  PROVED  13: standard + VST malloc

The full report: <work>/home/.cache/quickproof/verify/openverse_loader-proof-3925480cce/VERIFY.md
Verdict: PASS (exit 0).
```

Axioms (`Print Assumptions`): ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec,
Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token_valid_pointer,
library.malloc_token_local_facts, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep,
Eqdep.Eq_rect_eq.eq_rect_eq, library.create_mem_mgr, Classical_Prop.classic, Ensembles.Extensionality_Ensembles:
the standard ones and the declarations of VST's malloc library.
