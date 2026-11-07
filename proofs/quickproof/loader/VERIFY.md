# qp verify of openverse_loader

Run by `scripts/check-quickproof.sh --check loader` (with `QP_JOBS=6`) on 2026-11-07: a contract freshly assembled from the
pinned openverse commit, with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_loader-proof at d699f21622f6
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 18 files changed since the contract (`contract`), none of them frozen
[0:00] Clight generated again: identical to the committed files
[1:10] build: 10/26 files
[1:10] build: 11/26 files
[4:20] build: 13/26 files
[4:20] build: 16/26 files
[6:13] build: 19/26 files
[7:26] build: 21/26 files
[10:58] build: 24/26 files
[19:58] build: 26/26 files
[32:10] build: 26/26 files, 1929 s
[32:11] statements and axioms: 1 theorem probed
[32:46] the contract commit 2fd6d3d0a280: a clone, its statements built without the proof
[32:54] build of the contract commit: 7/7 files, 6 s
[32:55] statements and axioms of the contract commit: 1 theorem probed
[33:02] statements compared with the contract: identical
[33:02] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem            result  axioms
loader_wellscoped  PROVED  13: standard + VST malloc

The full report: <work>/home/.cache/quickproof/verify/openverse_loader-proof-d699f21622/VERIFY.md
Verdict: PASS (exit 0).
```

Axioms (`Print Assumptions`): ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec,
Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token_valid_pointer,
library.malloc_token_local_facts, library.malloc_token, FunctionalExtensionality.functional_extensionality_dep,
Eqdep.Eq_rect_eq.eq_rect_eq, library.create_mem_mgr, Classical_Prop.classic, Ensembles.Extensionality_Ensembles:
the standard ones and the declarations of VST's malloc library.
