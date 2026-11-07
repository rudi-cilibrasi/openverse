# qp verify of openverse_store

Run by `scripts/check-quickproof.sh --check loader arith store` on 2026-11-07: a contract freshly assembled from the
pinned openverse commit (7336cd864b97, float math #132), with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_store-proof at 4ce75d0efa9c
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 19 files changed since the contract (`contract`), none of them frozen
[0:00] Clight generated again: identical to the committed files
[1:52] build: 23/28 files
[3:56] build: 26/28 files
[7:22] build: 28/28 files
[7:27] build: 28/28 files, 446 s
[7:28] statements and axioms: 1 theorem probed
[7:50] the contract commit 09f8e5640c2c: a clone, its statements built without the proof
[8:00] build of the contract commit: 7/7 files, 9 s
[8:02] statements and axioms of the contract commit: 1 theorem probed
[8:13] statements compared with the contract: identical
[8:14] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem               result  axioms
store_rollback_model  PROVED  12: standard + VST malloc
```

The full report: <work>/home/.cache/quickproof/verify/openverse_store-proof-4ce75d0efa/VERIFY.md
Verdict: PASS (exit 0).
