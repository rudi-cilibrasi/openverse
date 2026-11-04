# qp verify of openverse_arith

Run by `scripts/check-quickproof.sh arith` on 2026-11-03: a contract freshly assembled from the pinned
openverse commit, with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_arith-proof at 6a9b4511015e
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 7 files changed since the contract (`contract`), none of them frozen
[0:00] Clight generated again: identical to the committed files
[1:50] build: 16/16 files
[4:09] build: 16/16 files, 248 s
[4:11] statements and axioms: 1 theorem probed
[4:29] the contract commit 506258ac3db1: a clone, its statements built without the proof
[4:36] build of the contract commit: 7/7 files, 6 s
[4:38] statements and axioms of the contract commit: 1 theorem probed
[4:47] statements compared with the contract: identical
[4:47] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem      result  axioms
arith_exact  PROVED  10: standard + VST malloc

The full report: <work>/home/.cache/quickproof/verify/openverse_arith-proof-6a9b451101/VERIFY.md
Verdict: PASS (exit 0).
```

Axioms (`Print Assumptions`): ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec,
Axioms.prop_ext, lib.Axioms.proof_irr, library.mem_mgr, library.malloc_token,
FunctionalExtensionality.functional_extensionality_dep, Eqdep.Eq_rect_eq.eq_rect_eq, Classical_Prop.classic,
Ensembles.Extensionality_Ensembles: the standard ones and the declarations of VST's malloc library.
