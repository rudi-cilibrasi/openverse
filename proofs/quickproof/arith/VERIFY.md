# qp verify of openverse_arith

Run by `scripts/check-quickproof.sh --check loader arith store` on 2026-11-07: a contract freshly assembled from the
pinned openverse commit (7336cd864b97, float math #132), with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_arith-proof at 5e2e7b1e2542
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 7 files changed since the contract (`contract`), none of them frozen
[0:00] Clight generated again: identical to the committed files
[2:39] build: 16/16 files, 158 s
[2:40] statements and axioms: 1 theorem probed
[2:53] the contract commit 36f9e28308a5: a clone, its statements built without the proof
[2:58] build of the contract commit: 7/7 files, 4 s
[2:59] statements and axioms of the contract commit: 1 theorem probed
[3:06] statements compared with the contract: identical
[3:06] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem      result  axioms
arith_exact  PROVED  10: standard + VST malloc
```

The full report: <work>/home/.cache/quickproof/verify/openverse_arith-proof-5e2e7b1e25/VERIFY.md
Verdict: PASS (exit 0).
