# openverse_arith: harness check

By `tools/qp check` on 2026-11-07 07:23: upstream 8faa3ffa5a6e, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `arith_exact` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `arith_exact` | ok (20 runs, no stop) |

## Mutants (300 runs per harness and mutant)

83 mutation sites in the code under test; 40 mutants run (0 skipped as dead code, 0 not compiling).
Killed by some harness: **29/40**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `arith_exact` | 29/40 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `runtime/src/arith.c:90` in `vx_floordiv`: `if (r != 0 && ((r < 0) != (b < 0)))` with `1`
- `runtime/src/arith.c:149` in `vx_modulo`: `if (b > 0)` with `1`
- `runtime/src/arith.c:33` in `vx_sub`: `if (b > 0 ? a < INT64_MIN + b : a > INT64_MAX + b)` with `>=`
- `runtime/src/arith.c:107` in `vx_ceildiv`: `if (r != 0 && ((r < 0) == (b < 0)))` with `1`
- `runtime/src/arith.c:149` in `vx_modulo`: `if (b > 0)` with `>=`
- `runtime/src/arith.c:52` in `vx_mul`: `else if (b < 0)` with `1`
- `runtime/src/arith.c:73` in `vx_abs`: `if (a < 0)` with `1`
- `runtime/src/arith.c:86` in `vx_floordiv`: `if (b == -1)` with `0`
- `runtime/src/arith.c:44` in `vx_mul`: `if (a > 0) {` with `1`
- `runtime/src/arith.c:90` in `vx_floordiv`: `if (r != 0 && ((r < 0) != (b < 0)))` with `1`
- `runtime/src/arith.c:50` in `vx_mul`: `if (b > 0)` with `1`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
