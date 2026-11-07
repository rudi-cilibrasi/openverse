# qp verify of openverse_store

Run by `scripts/check-quickproof.sh --check arith store` (with `QP_JOBS=4`) on 2026-11-07: a contract freshly assembled from the
pinned openverse commit, with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_store-proof at 3b068da4fe24
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 19 files changed since the contract (`contract`), none of them frozen
[0:01] Clight generated again: identical to the committed files
[1:05] build: 18/28 files
[1:10] build: 20/28 files
[1:38] build: 23/28 files
[5:32] build: 26/28 files
[10:29] build: 28/28 files
[10:40] build: 28/28 files, 639 s
[10:42] statements and axioms: 1 theorem probed
[11:32] the contract commit c3d2fd4521e3: a clone, its statements built without the proof
[11:47] build of the contract commit: 7/7 files, 13 s
[11:49] statements and axioms of the contract commit: 1 theorem probed
[12:03] statements compared with the contract: identical
[12:04] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem               result  axioms
store_rollback_model  PROVED  12: standard + VST malloc

The full report: <work>/home/.cache/quickproof/verify/openverse_store-proof-3b068da4fe/VERIFY.md
Verdict: PASS (exit 0).
```

Axioms (`Print Assumptions`): ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec,
Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token_local_facts,
library.malloc_token, FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq,
library.create_mem_mgr, Classical_Prop.classic, Ensembles.Extensionality_Ensembles: the standard ones and
the declarations of VST's malloc library (two more than `arith_exact`, because this law allocates the
store's arrays with `malloc`).
