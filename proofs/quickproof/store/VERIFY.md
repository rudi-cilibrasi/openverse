# qp verify of openverse_store

Run by `scripts/check-quickproof.sh --check loader arith store` on 2026-11-07: a contract freshly assembled from the
pinned openverse commit (4006a49d863c, floats #127), with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_store-proof at 567267d31cac
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 19 files changed since the contract (`contract`), none of them frozen
[0:00] Clight generated again: identical to the committed files
[1:28] build: 23/28 files
[3:07] build: 26/28 files
[6:41] build: 28/28 files
[6:45] build: 28/28 files, 404 s
[6:46] statements and axioms: 1 theorem probed
[7:05] the contract commit 5e280721855e: a clone, its statements built without the proof
[7:11] build of the contract commit: 7/7 files, 5 s
[7:12] statements and axioms of the contract commit: 1 theorem probed
[7:18] statements compared with the contract: identical
[7:18] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem               result  axioms
store_rollback_model  PROVED  12: standard + VST malloc
```

The full report: <work>/home/.cache/quickproof/verify/openverse_store-proof-567267d31c/VERIFY.md
Verdict: PASS (exit 0).
