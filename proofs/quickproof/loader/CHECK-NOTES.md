# Reading the mutants of loader_wellscoped

`loader_wellscoped` is a safety law. It claims that `vx_load` reads in
bounds for every buffer, and that whatever it accepts is well formed and
well scoped. It does not claim that every valid buffer is accepted
(completeness), nor that the values decoded are the encoded ones
(exactness): the differential tests cover those, because they compare the C
runtime with the Lean interpreter on every program they load
(`scripts/test-verse.sh --c`, `scripts/fuzz-diff.sh`). `qp check` kills 6 of
40 mutants (`CHECK.md`). The heap commit added mutation sites (228, from
212), so these 40 are another sample than those of the previous pin. Under
the input distribution of `project/env/loader_wellscoped.c`, 58% of buffers
are accepted; about half of the accepted ones hold a HEAP node, a fifth an
isTag and a fifth a REF literal. Every rejection reason except out-of-memory
occurs, `VX_LOAD_HEAP` included (measured over 200,000 native runs).

| Survivors | Reading |
|---|---|
| `rd_u8(...) != OK` → `==` in `load_prim`/`load_heap`, `rd_u32(...) != OK` → `==` in `load_header`, `rd_i64(...) != OK` → `==` in `load_lit`, an `\|\|` of the magic reads → `&&`, `nfns == 0` → `== 1`, `n > VX_MAX_STR` → `>=`, `k > VX_MAX_TAGS` → `>=` | not claimed (completeness): the mutant rejects buffers the original accepts (the last two only buffers of 16 MiB or more) |
| the magic test `\|\|` → `&&`, `ver != 1` → `!= 0` | not claimed: the mutant accepts a wrong magic or version, which the law does not check; the program is then checked as usual |
| the byte indices and shifts of `rd_u32`, the loop bound, `pos + 8` and the sign conversion of `rd_i64`, `node_clear`'s `lit = 0` → `1`, `prog_clear`'s `nargs = 0` → `1`, `load_heap`'s `4 * k` → `5 * k` | not claimed (exactness): the mutant decodes other values (or starts the args pool at entry 1, or stores 5 bytes per class tag), which are then checked as usual; the theorem still holds of the values decoded |
| `load_header`: the initial `nslots`, `nnodes` and `root` of each function → `1`; the args pool `malloc((rest / 4) * …)` → `rest / 3`; `acap = rest / 4` → `/3` | equivalent under the law: `load_fn` sets the three fields before a program is accepted, and `vx_free_program` reads none of them; the pool is only larger; an argument takes 4 input bytes, so the pool never holds more than `rest / 4` entries |
| `load_fn`: `root >= nnodes` → `>`; `load_call`: `fn >= p->nfns` → `>`; `load_header`: `entry_fn >= nfns` → `>`; `load_for`: the test after the second child `!=` → `==`; `load_prim`: `k != 0 && code != VX_P_TUPGET` and `load_heap`: `k != 0 && op == VX_H_TAG`, each with an `==`; the args pool `malloc((rest / 4) * …)` → `rest / 5` | claimed, but each needs a rare corruption that the 300 runs per mutant did not draw (a root, callee or entry index equal to its count; a FOR whose second child is out of range while its third parses; a nonzero `k` on a primitive other than tupGet or on the heap op tag; argument lists filling more than four fifths of the input); a proof of the law rules each of them out for every input |
| `vx_free_program`: the loop over the node tables from `1` | not claimed: it leaks the node table of function 0; the law does not claim the absence of leaks (QuickProof proves partial correctness and memory safety, not freedom from leaks) |
