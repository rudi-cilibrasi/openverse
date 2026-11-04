# openverse_loader: harness check

By `tools/qp check` on 2026-11-04 05:34: upstream e89f1940b539, quickproof fab76ef.

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

212 mutation sites in the code under test; 40 mutants run (0 skipped as dead code, 0 not compiling).
Killed by some harness: **8/40**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `loader_wellscoped` | 8/40 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `runtime/src/load.c:416` in `load_header`: `if (p->bytes == NULL)` with `!=`
- `runtime/src/load.c:87` in `rd_i64`: `*out = -(int64_t)(~u) - 1;` with `- 0`
- `runtime/src/load.c:523` in `vx_load`: `r.acap = 0;` with `1`
- `runtime/src/load.c:83` in `rd_i64`: `r->pos = r->pos + 8;` with `7`
- `runtime/src/load.c:397` in `load_header`: `if (rd_u32(r, &nfns) != VX_LOAD_OK)` with `==`
- `runtime/src/load.c:160` in `node_clear`: `nd->lit = 0;` with `1`
- `runtime/src/load.c:207` in `load_prim`: `if (rd_u32(r, &k) != VX_LOAD_OK)` with `==`
- `runtime/src/load.c:414` in `load_header`: `r->acap = rest / 4;` with `3`
- `runtime/src/load.c:522` in `vx_load`: `r.pos = 0;` with `1`
- `runtime/src/load.c:84` in `rd_i64`: `if (u <= (uint64_t)INT64_MAX)` with `<`
- `runtime/src/load.c:95` in `rd_bytes`: `if (n > VX_MAX_STR)` with `>=`
- `runtime/src/load.c:66` in `rd_u32`: `v = v | ((uint32_t)r->buf[r->pos + 2] << 16);` with `3`
- `runtime/src/load.c:542` in `vx_free_program`: `if (p->args != NULL)` with `==`
- `runtime/src/load.c:414` in `load_header`: `r->acap = rest / 4;` with `5`
- `runtime/src/load.c:442` in `trim_args`: `if (p->nargs == 0) {` with `1`
- `runtime/src/load.c:337` in `load_fn`: `if (nnodes == 0)` with `!=`
- `runtime/src/load.c:65` in `rd_u32`: `v = v | ((uint32_t)r->buf[r->pos + 1] << 8);` with `9`
- `runtime/src/load.c:369` in `check_calls`: `if (nd->tag == VX_N_CALL && p->fns[nd->a].arity != nd->b)` with `==`
- `runtime/src/load.c:275` in `load_node`: `if (tag == VX_N_ASSIGN) {` with `!=`
- `runtime/src/load.c:175` in `load_lit`: `if (rd_i64(r, &i) != VX_LOAD_OK)` with `==`
- `runtime/src/load.c:209` in `load_prim`: `if (k != 0 && code != VX_P_TUPGET)` with `1`
- `runtime/src/load.c:391` in `load_header`: `if (m0 != 0x4fu || m1 != 0x56u || m2 != 0x42u || m3 != 0x43u)   /* "OVBC" */` with `==`
- `runtime/src/load.c:412` in `load_header`: `if (p->args == NULL)` with `!=`
- `runtime/src/load.c:65` in `rd_u32`: `v = v | ((uint32_t)r->buf[r->pos + 1] << 8);` with `7`
- `runtime/src/load.c:367` in `check_calls`: `for (j = 0; j < p->fns[f].nnodes; j++) {` with `1`
- `runtime/src/load.c:500` in `load_all`: `for (f = 0; f < p->nfns; f++) {` with `1`
- `runtime/src/load.c:67` in `rd_u32`: `v = v | ((uint32_t)r->buf[r->pos + 3] << 24);` with `2`
- `runtime/src/load.c:399` in `load_header`: `if (nfns == 0)` with `!=`
- `runtime/src/load.c:81` in `rd_i64`: `for (k = 0; k < 8; k++)` with `7`
- `runtime/src/load.c:67` in `rd_u32`: `v = v | ((uint32_t)r->buf[r->pos + 3] << 24);` with `25`
- `runtime/src/load.c:389` in `load_header`: `rd_u8(r, &m2) != VX_LOAD_OK || rd_u8(r, &m3) != VX_LOAD_OK)` with `==`
- `runtime/src/load.c:401` in `load_header`: `if (nfns > VX_MAX_FNS)` with `>=`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
