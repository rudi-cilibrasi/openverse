# qp verify of openverse_store

Run by `scripts/check-quickproof.sh --check store` (with `QP_JOBS=3`) on 2026-11-04: a contract freshly assembled from the
pinned openverse commit, with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_store-proof at 51d12cc87e0b
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 19 files changed since the contract (`contract`), none of them frozen
[0:00] Clight generated again: identical to the committed files
[1:17] build: 16/28 files
[1:28] build: 17/28 files
[1:45] build: 20/28 files
[3:06] build: 23/28 files
[4:57] build: 26/28 files
[8:24] build: 28/28 files
[8:29] build: 28/28 files, 508 s
[8:30] statements and axioms: 1 theorem probed
[8:53] the contract commit 230cf5a1dc16: a clone, its statements built without the proof
[9:01] build of the contract commit: 7/7 files, 6 s
[9:01] statements and axioms of the contract commit: 1 theorem probed
[9:09] statements compared with the contract: identical
[9:09] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem               result  axioms
store_rollback_model  PROVED  12: standard + VST malloc

The full report: <work>/home/.cache/quickproof/verify/openverse_store-proof-51d12cc87e/VERIFY.md
Verdict: PASS (exit 0).
```

Axioms (`Print Assumptions`): ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec,
Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token_local_facts,
library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq,
library.create_mem_mgr, Classical_Prop.classic, Ensembles.Extensionality_Ensembles: the standard ones and
the declarations of VST's malloc library (two more than `arith_exact`, because this law allocates the
store's arrays with `malloc`).
