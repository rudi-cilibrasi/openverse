# qp verify of openverse_loader

Run by `scripts/check-quickproof.sh --check loader arith store` on 2026-11-07: a contract freshly assembled from the
pinned openverse commit (7336cd864b97, float math #132), with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_loader-proof at 176d6ee6db9a
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 18 files changed since the contract (`contract`), none of them frozen
[0:01] Clight generated again: identical to the committed files
[1:51] build: 10/26 files
[1:51] build: 11/26 files
[5:57] build: 13/26 files
[5:57] build: 16/26 files
[9:01] build: 19/26 files
[10:49] build: 21/26 files
[15:46] build: 24/26 files
[28:08] build: 26/26 files
[38:15] build: 26/26 files, 2294 s
[38:16] statements and axioms: 1 theorem probed
[38:49] the contract commit 7a22d9796f6b: a clone, its statements built without the proof
[38:56] build of the contract commit: 7/7 files, 6 s
[38:57] statements and axioms of the contract commit: 1 theorem probed
[39:04] statements compared with the contract: identical
[39:04] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem            result  axioms
loader_wellscoped  PROVED  13: standard + VST malloc
```

The full report: <work>/home/.cache/quickproof/verify/openverse_loader-proof-176d6ee6db/VERIFY.md
Verdict: PASS (exit 0).
