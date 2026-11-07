# qp verify of openverse_arith

Run by `scripts/check-quickproof.sh --check loader arith store` on 2026-11-07: a contract freshly assembled from the
pinned openverse commit (4006a49d863c, floats #127), with `proof/src/` copied over it and committed, checked by `qp verify --brief`.

```
[0:00] qp verify: a fresh clone of <work>/openverse_arith-proof at b45f44335719
[0:00] framework: the 16 trusted files are identical to this verifier's
[0:00] frozen files: 7 files changed since the contract (`contract`), none of them frozen
[0:00] Clight generated again: identical to the committed files
[1:03] build: 16/16 files
[2:48] build: 16/16 files, 167 s
[2:49] statements and axioms: 1 theorem probed
[3:01] the contract commit f25f52e246df: a clone, its statements built without the proof
[3:06] build of the contract commit: 7/7 files, 3 s
[3:06] statements and axioms of the contract commit: 1 theorem probed
[3:12] statements compared with the contract: identical
[3:12] Admitted, admit, Axiom, Parameter, Conjecture in the sources of the proof: none

theorem      result  axioms
arith_exact  PROVED  10: standard + VST malloc
```

The full report: <work>/home/.cache/quickproof/verify/openverse_arith-proof-b45f443357/VERIFY.md
Verdict: PASS (exit 0).
