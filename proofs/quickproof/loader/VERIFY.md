# qp verify of openverse_loader

Run by `scripts/check-quickproof.sh --check loader` (with `QP_JOBS=3`) on 2026-11-04: a contract freshly assembled from the
pinned openverse commit, with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_loader-proof at a0ec73636132
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 18 files changed since the contract (`contract`), none of them frozen
[0:01] Clight generated again: identical to the committed files
[1:33] build: 10/26 files
[1:33] build: 11/26 files
[1:46] build: 13/26 files
[3:11] build: 16/26 files
[6:27] build: 19/26 files
[10:27] build: 21/26 files
[11:32] build: 24/26 files
[18:18] build: 26/26 files
[44:46] build: 26/26 files, 2685 s
[44:47] statements and axioms: 1 theorem probed
[45:13] the contract commit 243bc47265c2: a clone, its statements built without the proof
[45:20] build of the contract commit: 7/7 files, 5 s
[45:20] statements and axioms of the contract commit: 1 theorem probed
[45:26] statements compared with the contract: identical
[45:26] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem            result  axioms
loader_wellscoped  PROVED  13: standard + VST malloc

The full report: <work>/home/.cache/quickproof/verify/openverse_loader-proof-a0ec736361/VERIFY.md
Verdict: PASS (exit 0).
```

Axioms (`Print Assumptions`): ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec,
Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token_valid_pointer,
library.malloc_token_local_facts, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep,
Eqdep.Eq_rect_eq.eq_rect_eq, library.create_mem_mgr, Classical_Prop.classic, Ensembles.Extensionality_Ensembles:
the standard ones and the declarations of VST's malloc library.
