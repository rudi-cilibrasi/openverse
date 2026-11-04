# qp verify of openverse_store

Run by `scripts/check-quickproof.sh store` (with `QP_JOBS=3`) on 2026-11-04: a contract freshly assembled from the
pinned openverse commit, with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_store-proof at 8a450d262fc6
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 19 files changed since the contract (`contract`), none of them frozen
[0:02] Clight generated again: identical to the committed files
[3:06] build: 16/28 files
[3:28] build: 17/28 files
[3:56] build: 20/28 files
[7:04] build: 23/28 files
[10:11] build: 26/28 files
[15:34] build: 28/28 files
[15:43] build: 28/28 files, 940 s
[15:44] statements and axioms: 1 theorem probed
[16:26] the contract commit a28f06c47540: a clone, its statements built without the proof
[16:39] build of the contract commit: 7/7 files, 12 s
[16:41] statements and axioms of the contract commit: 1 theorem probed
[16:52] statements compared with the contract: identical
[16:52] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem               result  axioms
store_rollback_model  PROVED  12: standard + VST malloc

The full report: <work>/home/.cache/quickproof/verify/openverse_store-proof-8a450d262f/VERIFY.md
Verdict: PASS (exit 0).
```

Axioms (`Print Assumptions`): ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec,
Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token_local_facts,
library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq,
library.create_mem_mgr, Classical_Prop.classic, Ensembles.Extensionality_Ensembles: the standard ones and
the declarations of VST's malloc library (two more than `arith_exact`, because this law allocates the
store's arrays with `malloc`).
