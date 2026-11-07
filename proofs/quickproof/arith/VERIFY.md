# qp verify of openverse_arith

Run by `scripts/check-quickproof.sh --check arith store` (with `QP_JOBS=4`) on 2026-11-07: a contract freshly assembled from the
pinned openverse commit, with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_arith-proof at 7880ec881c73
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 7 files changed since the contract (`contract`), none of them frozen
[0:00] Clight generated again: identical to the committed files
[1:02] build: 16/16 files
[3:13] build: 16/16 files, 192 s
[3:14] statements and axioms: 1 theorem probed
[3:30] the contract commit 4d888b8036ef: a clone, its statements built without the proof
[3:35] build of the contract commit: 7/7 files, 4 s
[3:36] statements and axioms of the contract commit: 1 theorem probed
[3:46] statements compared with the contract: identical
[3:46] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem      result  axioms
arith_exact  PROVED  10: standard + VST malloc

The full report: <work>/home/.cache/quickproof/verify/openverse_arith-proof-7880ec881c/VERIFY.md
Verdict: PASS (exit 0).
```

Axioms (`Print Assumptions`): ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec,
Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token,
FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq, Classical_Prop.classic,
Ensembles.Extensionality_Ensembles: the standard ones and the declarations of VST's malloc library.
