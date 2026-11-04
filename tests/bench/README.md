# Benchmarks

Programs too slow for the default test suite. Run one on both implementations:

```sh
.lake/build/bin/openverse run tests/bench/tictactoe.verse
.lake/build/bin/openverse emit tests/bench/tictactoe.verse -o /tmp/t.vbc && runtime/build/cverse /tmp/t.vbc
```

| Program | Result | Lean reference interpreter | C runtime |
|---|---|---|---|
| `tictactoe.verse`: full minimax over tic-tac-toe (549,946 positions) | draw, as a Python model of the same search agrees | 45 s | 7 s |

(2026-11-03, 12-core x86-64; both outputs are identical byte for byte.)
