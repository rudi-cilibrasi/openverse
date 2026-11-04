# Reading the mutants of arith_exact

`qp check` mutates `runtime/src/arith.c` (comparisons, logical operators,
off-by-one constants) and runs `arith_exact` 300 times against each mutant,
with the edge-biased values of `project/env/arith_exact.c`. A mutant that
survives is equivalent to the original, changes something no law checks, or
fails only on inputs the runs did not draw. Ten survivors were classified by
hand in the dry run, before the runtime was committed (29/40 killed):

| Mutant | Reading |
|---|---|
| `vx_sub`: `b > 0` → `b >= 0` | equivalent: at `b = 0` both branches test a condition that is false |
| `vx_floordiv`, `vx_ceildiv`: `r < 0` → `r < 1`, `b < 0` → `b < 1` (under `r != 0`) | equivalent: `r != 0` and integers; `b = 0` returned earlier |
| `vx_modulo`: `b > 0` → `b > 1`, `b >= 0` | equivalent: for `b = 1`, `r = 0`, and `b = 0` returned earlier |
| `vx_mul`: `a > 0` → `a > 1`, `b > 0` → `b > 1`, `b < 0` → `b < 1` | equivalent: the overflow check that is skipped cannot fire for operand 1 or 0 |
| `vx_abs`: `a < 0` → `a < 1` | equivalent: `vx_neg(0) = 0` |
| `vx_floordiv`: `b == -1` → `b == 0` | **not equivalent**: drops the special case, so `INT64_MIN / -1` is evaluated (undefined, SIGFPE natively). The env now draws `-1` and `INT64_MIN` often; the proof rules this mutant out regardless. |
