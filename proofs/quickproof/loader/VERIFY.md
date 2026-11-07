# qp verify of openverse_loader

Run by `scripts/check-quickproof.sh --check loader arith store` on 2026-11-07: a contract freshly assembled from the
pinned openverse commit (4006a49d863c, floats #127), with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_loader-proof at fd9f4e809125
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 18 files changed since the contract (`contract`), none of them frozen
[0:01] Clight generated again: identical to the committed files
[1:16] build: 10/26 files
[1:16] build: 11/26 files
[4:00] build: 13/26 files
[4:00] build: 16/26 files
[5:39] build: 19/26 files
[6:45] build: 21/26 files
[9:34] build: 24/26 files
[17:06] build: 26/26 files
[27:20] build: 26/26 files, 1638 s
[27:21] statements and axioms: 1 theorem probed
[27:52] the contract commit 840f15c494b6: a clone, its statements built without the proof
[27:59] build of the contract commit: 7/7 files, 5 s
[27:59] statements and axioms of the contract commit: 1 theorem probed
[28:06] statements compared with the contract: identical
[28:06] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem            result  axioms
loader_wellscoped  PROVED  13: standard + VST malloc
```

The full report: <work>/home/.cache/quickproof/verify/openverse_loader-proof-fd9f4e8091/VERIFY.md
Verdict: PASS (exit 0).
