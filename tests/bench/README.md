# Benchmarks

Programs too slow for the default test suite. Run one on both implementations:

```sh
.lake/build/bin/openverse run tests/bench/tictactoe.verse
.lake/build/bin/openverse emit tests/bench/tictactoe.verse -o /tmp/t.vbc && runtime/build/cverse /tmp/t.vbc
```

| Program | Result | Lean reference interpreter | C runtime |
|---|---|---|---|
| `tictactoe.verse`: full minimax over tic-tac-toe (549,946 positions) | draw, as a Python model of the same search agrees | 45 s | 7 s |
| `cancel_many.verse`: 4,000 tasks cancelled one after another (#270) | `unwound 0`, `all cancelled` | 0.4–0.6 s (0.9–1.2 s before #270) | 0.2 s |
| `generic_waiters.verse`: 4,000 tasks spawned from generic code awaiting one event (#256) | `done` | 0.6 s (4.1 s before #256, when compiled without copies at closed types) | 0.1 s |

(2026-11-03 and 2026-11-08, 12-core x86-64; both outputs are identical byte for byte.)
