# Reading the mutants of loader_wellscoped

`loader_wellscoped` is a safety law. It claims that `vx_load` reads in
bounds for every buffer, and that whatever it accepts is well formed and
well scoped. It does not claim that every valid buffer is accepted
(completeness), nor that the values decoded are the encoded ones
(exactness): the differential tests cover those, because they compare the C
runtime with the Lean interpreter on every program they load
(`scripts/test-verse.sh --c`, `scripts/fuzz-diff.sh`). `qp check` kills 8 of
40 mutants (`CHECK.md`). Under the input distribution of
`project/env/loader_wellscoped.c`, 58% of buffers are accepted, and every
rejection reason except out-of-memory occurs (measured over 200,000 native
runs).

| Survivors | Reading |
|---|---|
| `nfns == 0` → `!=`, `nnodes == 0` → `!=`, the magic test `!=` → `==`, `rd_u32(...) != OK` → `==` in `load_header`/`load_prim`/`load_lit`, `p->args == NULL` → `!=`, `p->bytes == NULL` → `!=`, `nfns > VX_MAX_FNS` → `>=`, `n > VX_MAX_STR` → `>=` | not claimed (completeness): the mutant rejects buffers the original accepts |
| the shifts and the loop bound of `rd_u32`/`rd_i64`, its sign conversion, `node_clear`'s `lit = 0` → `1`, `r.pos = 0` → `1`, `r.acap = 0` → `1`, `acap = rest / 4` → `/3`, `/5` | not claimed (exactness): the mutant decodes other values, which are then checked as usual; the theorem still holds of the values decoded |
| `check_calls`: `!=` → `==`, `j < nnodes` → `j < 1`; `load_prim`: `k != 0` → `k != 1`; `load_node`: `tag == VX_N_ASSIGN` → `!=`; `load_all`'s loop bound | claimed, but each needs a rare corruption (a call whose argument count is wrong while its arguments still parse, a `k` field of exactly 2 or more on another primitive) that the 300 runs per mutant did not draw; a proof of the law rules each of them out for every input |
| `trim_args`: `nargs == 0` → `== 1`; `vx_free_program`: `args != NULL` → `==` | not claimed: these leak the args pool; the law does not claim the absence of leaks (QuickProof proves partial correctness and memory safety, not freedom from leaks) |
