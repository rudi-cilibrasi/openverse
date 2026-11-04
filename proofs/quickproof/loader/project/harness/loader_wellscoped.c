/* Law loader_wellscoped.
 *
 * Take an input buffer of up to 4096 bytes with any contents, passed to vx_load
 * (runtime/src/load.c) with its exact length. Then:
 *   - vx_load reads only inside the buffer (as every access of the theorem is in bounds)
 *     and returns one of its result codes, 0 to VX_LOAD_LAST;
 *   - when it returns VX_LOAD_OK, the program it built satisfies every condition of
 *     docs/FORMAT.md "What the loader accepts":
 *       nfns >= 1 and entry < nfns (the index of Main);
 *       every function has arity <= nslots, nnodes >= 1, root < nnodes, and its name lies
 *       inside the bytes pool;
 *       every node j has a tag <= VX_N_LAST, and every child index it holds is < j;
 *       every slot of a LOCAL, ASSIGN or FOR node is < nslots of its function;
 *       every CALL names a function < nfns whose arity is the call's argument count;
 *       every PRIM has a code <= VX_P_LAST and k == 0 unless it is tupGet;
 *       every argument list lies inside the args pool, and every string literal inside the
 *       bytes pool; every literal kind is <= VX_LIT_LAST, and a LOGIC literal is 0 or 1;
 *     the slot, arity and call conditions are Prog.WellScoped of OpenVerse/Core/Scoping.lean,
 *     under which Eval.scoped_ok proves that no slot or call error can happen;
 *   - when it returns anything else, the program is empty: nfns == 0 and all three pointers
 *     are NULL;
 *   - in both cases vx_free_program then releases it (each free is of a live block).
 * Not claimed: that every well-formed buffer is accepted (completeness), and anything about
 * buffers longer than 4096 bytes.
 */
#include <stdint.h>
#include <stdlib.h>
#include "quickproof.h"
#include "openverse.h"

#define MAXLEN 4096

int main(void) {
    size_t n;
    uint8_t *buf;
    vx_program p;
    int rc;
    uint32_t f, j, k;

    n = nondet_size();
    qp_assume(n <= MAXLEN);
    buf = (uint8_t *) malloc(n);
    if (n > 0 && buf == NULL)
        return 0;
    nondet_bytes(buf, n);

    rc = vx_load(buf, n, &p);
    qp_assert(rc >= 0 && rc <= VX_LOAD_LAST);
    if (rc == VX_LOAD_OK) {
        qp_assert(p.nfns >= 1);
        qp_assert(p.entry < p.nfns);
        for (f = 0; f < p.nfns; f++) {
            vx_fn *fn = &p.fns[f];
            qp_assert(fn->arity <= fn->nslots);
            qp_assert(fn->nnodes >= 1);
            qp_assert(fn->root < fn->nnodes);
            qp_assert(fn->name_len <= p.nbytes);
            qp_assert(fn->name_off <= p.nbytes - fn->name_len);
            for (j = 0; j < fn->nnodes; j++) {
                vx_node *nd = &fn->nodes[j];
                uint32_t t = nd->tag;
                qp_assert(t <= VX_N_LAST);
                if (t == VX_N_LIT) {
                    qp_assert(nd->op <= VX_LIT_LAST);
                    if (nd->op == VX_LIT_LOGIC)
                        qp_assert(nd->lit == 0 || nd->lit == 1);
                    if (nd->op == VX_LIT_STR) {
                        qp_assert(nd->b <= p.nbytes);
                        qp_assert(nd->a <= p.nbytes - nd->b);
                    }
                } else if (t == VX_N_LOCAL) {
                    qp_assert(nd->a < fn->nslots);
                } else if (t == VX_N_ASSIGN) {
                    qp_assert(nd->a < fn->nslots);
                    qp_assert(nd->b < j);
                } else if (t == VX_N_SEQ) {
                    qp_assert(nd->a < j);
                    qp_assert(nd->b < j);
                } else if (t == VX_N_PRIM || t == VX_N_CALL) {
                    if (t == VX_N_PRIM) {
                        qp_assert(nd->op <= VX_P_LAST);
                        qp_assert(nd->a == 0 || nd->op == VX_P_TUPGET);
                    } else {
                        qp_assert(nd->a < p.nfns);
                        qp_assert(p.fns[nd->a].arity == nd->b);
                    }
                    qp_assert(nd->b <= p.nargs);
                    qp_assert(nd->c <= p.nargs - nd->b);
                    for (k = 0; k < nd->b; k++)
                        qp_assert(p.args[nd->c + k] < j);
                } else if (t == VX_N_ITE) {
                    qp_assert(nd->a < j);
                    qp_assert(nd->b < j);
                    qp_assert(nd->c < j);
                } else if (t == VX_N_FOR) {
                    qp_assert(nd->a < fn->nslots);
                    qp_assert(nd->b < j);
                    qp_assert(nd->c < j);
                    qp_assert(nd->d < j);
                } else if (t == VX_N_LOOP || t == VX_N_RET || t == VX_N_PRINT) {
                    qp_assert(nd->a < j);
                }
            }
        }
    } else {
        qp_assert(p.nfns == 0);
        qp_assert(p.fns == NULL);
        qp_assert(p.args == NULL);
        qp_assert(p.bytes == NULL);
    }
    vx_free_program(&p);
    free(buf);
    return 0;
}
