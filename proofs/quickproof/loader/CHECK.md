# openverse_loader: harness check

By `tools/qp check` on 2026-11-07 20:48: upstream 4006a49d863c, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `loader_wellscoped` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `loader_wellscoped` | ok (20 runs, no stop) |

## Mutants (300 runs per harness and mutant)

228 mutation sites in the code under test; 40 mutants run (0 skipped as dead code, 0 not compiling).
Killed by some harness: **6/40**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `loader_wellscoped` | 6/40 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `runtime/src/load.c:208` in `load_prim`: `if (rd_u8(r, &code) != VX_LOAD_OK)` with `==`
- `runtime/src/load.c:451` in `load_header`: `p->args = malloc((rest / 4) * sizeof(uint32_t));` with `5`
- `runtime/src/load.c:526` in `prog_clear`: `p->nargs = 0;` with `1`
- `runtime/src/load.c:176` in `load_lit`: `if (rd_i64(r, &i) != VX_LOAD_OK)` with `==`
- `runtime/src/load.c:96` in `rd_bytes`: `if (n > VX_MAX_STR)` with `>=`
- `runtime/src/load.c:295` in `load_for`: `if (rc != VX_LOAD_OK)` with `==`
- `runtime/src/load.c:214` in `load_prim`: `if (k != 0 && code != VX_P_TUPGET)` with `==`
- `runtime/src/load.c:469` in `load_header`: `p->fns[f].root = 0;` with `1`
- `runtime/src/load.c:394` in `load_fn`: `if (root >= nnodes)` with `>`
- `runtime/src/load.c:428` in `load_header`: `if (rd_u8(r, &m0) != VX_LOAD_OK || rd_u8(r, &m1) != VX_LOAD_OK ||` with `&&`
- `runtime/src/load.c:468` in `load_header`: `p->fns[f].nnodes = 0;` with `1`
- `runtime/src/load.c:451` in `load_header`: `p->args = malloc((rest / 4) * sizeof(uint32_t));` with `3`
- `runtime/src/load.c:240` in `load_heap`: `if (k > VX_MAX_TAGS)` with `>=`
- `runtime/src/load.c:264` in `load_call`: `if (fn >= p->nfns)` with `>`
- `runtime/src/load.c:67` in `rd_u32`: `v = v | ((uint32_t)r->buf[r->pos + 2] << 16);` with `3`
- `runtime/src/load.c:439` in `load_header`: `if (nfns == 0)` with `1`
- `runtime/src/load.c:85` in `rd_i64`: `if (u <= (uint64_t)INT64_MAX)` with `<`
- `runtime/src/load.c:445` in `load_header`: `if (entry_fn >= nfns)` with `>`
- `runtime/src/load.c:464` in `load_header`: `p->fns[f].nslots = 0;` with `1`
- `runtime/src/load.c:88` in `rd_i64`: `*out = -(int64_t)(~u) - 1;` with `- 0`
- `runtime/src/load.c:576` in `vx_free_program`: `for (i = 0; i < p->nfns; i++) {` with `1`
- `runtime/src/load.c:66` in `rd_u32`: `v = v | ((uint32_t)r->buf[r->pos + 1] << 8);` with `7`
- `runtime/src/load.c:84` in `rd_i64`: `r->pos = r->pos + 8;` with `7`
- `runtime/src/load.c:243` in `load_heap`: `rc = rd_bytes(r, p, 4 * k, &nd->a);` with `5`
- `runtime/src/load.c:247` in `load_heap`: `if (k != 0 && op == VX_H_TAG)` with `==`
- `runtime/src/load.c:435` in `load_header`: `if (ver != 1)` with `0`
- `runtime/src/load.c:66` in `rd_u32`: `v = v | ((uint32_t)r->buf[r->pos + 1] << 8);` with `9`
- `runtime/src/load.c:437` in `load_header`: `if (rd_u32(r, &nfns) != VX_LOAD_OK)` with `==`
- `runtime/src/load.c:454` in `load_header`: `r->acap = rest / 4;` with `3`
- `runtime/src/load.c:68` in `rd_u32`: `v = v | ((uint32_t)r->buf[r->pos + 3] << 24);` with `2`
- `runtime/src/load.c:161` in `node_clear`: `nd->lit = 0;` with `1`
- `runtime/src/load.c:232` in `load_heap`: `if (rd_u8(r, &op) != VX_LOAD_OK)` with `==`
- `runtime/src/load.c:431` in `load_header`: `if (m0 != 0x4fu || m1 != 0x56u || m2 != 0x42u || m3 != 0x43u)   /* "OVBC" */` with `&&`
- `runtime/src/load.c:82` in `rd_i64`: `for (k = 0; k < 8; k++)` with `7`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
