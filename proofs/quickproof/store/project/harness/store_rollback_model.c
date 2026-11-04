/* Law store_rollback_model.
 *
 * The transactional store of the C runtime (runtime/src/store.c) rolls back failure contexts
 * exactly as the semantics of Verse Core says (OpenVerse/Core/Semantics.lean: Eval.ite_fail,
 * EvalFor.skip; OpenVerse/Core/Derived.lean: ite_rollback): a failure context that fails
 * leaves the slots and the output exactly as they were when it was entered, at any nesting
 * depth, and one that succeeds keeps every effect.
 *
 * Take a store of up to 4 slots with any initial contents, a journal of any capacity up to 8
 * entries and an output buffer of any capacity up to 8 bytes (each allocated with exactly its
 * size). Then run 32 operations, each chosen freely:
 *   0  vx_store_mark: enter a failure context (at most 3 nested);
 *   1  vx_store_set: write any value to any slot index, including indices out of range;
 *   2  vx_store_out_append: append 0, 1 or 2 arbitrary bytes;
 *   3  vx_store_rollback: leave the innermost context, which failed;
 *   4  vx_store_commit: leave the innermost context, which succeeded.
 * The harness keeps a naive model: the slot contents, the output bytes and length, and a full
 * copy of all three taken when each context was entered. After every operation:
 *   - vx_store_set returned VX_ESLOT exactly when the index is out of range, VX_EFULL exactly
 *     when it is inside a context and the journal holds jcap entries (the model counts the
 *     entries: one per successful write inside a context, back to the count at the mark on a
 *     rollback, none once the outermost context is left), and VX_OK otherwise; it changed the
 *     slot exactly when it returned VX_OK;
 *   - vx_store_out_append returned VX_EFULL exactly when the bytes do not fit, and then
 *     changed nothing;
 *   - a rollback restored the model's copy taken at the matching mark; a commit changed
 *     nothing visible;
 *   - every slot, the output length and every output byte below it equal the model's.
 *   - at the end, vx_store_get of an index out of range returns VX_ESLOT.
 * Not claimed: the vx_store_move_* functions, vx_store_put and vx_store_forget (the
 * interpreter's frame management), and anything about the journal capacity the interpreter
 * chooses.
 */
#include <stdint.h>
#include <stdlib.h>
#include "quickproof.h"
#include "openverse.h"

#define MAXS 4
#define MAXJ 8
#define MAXO 8
#define MAXD 3
#define STEPS 32

int main(void) {
    vx_store st;
    vx_mark marks[MAXD];
    uint64_t mtag[MAXS], mbits[MAXS];          /* the model */
    uint8_t mout[MAXO];
    size_t molen;
    size_t mjlen;                               /* the model's journal length */
    uint64_t ctag[MAXD][MAXS], cbits[MAXD][MAXS]; /* the copies taken at each mark */
    uint8_t cout[MAXD][MAXO];
    size_t colen[MAXD];
    size_t cjlen[MAXD];
    size_t depth, nslots, jcap, ocap, i, k;
    vx_val *slots;
    vx_undo *jour;
    uint8_t *out;

    nslots = nondet_size(); qp_assume(nslots <= MAXS);
    jcap = nondet_size(); qp_assume(jcap <= MAXJ);
    ocap = nondet_size(); qp_assume(ocap <= MAXO);
    slots = (vx_val *) malloc(nslots * sizeof(vx_val));
    jour = (vx_undo *) malloc(jcap * sizeof(vx_undo));
    out = (uint8_t *) malloc(ocap);
    if ((nslots > 0 && slots == NULL) || (jcap > 0 && jour == NULL) || (ocap > 0 && out == NULL))
        return 0;
    for (i = 0; i < nslots; i++) {
        pick(mtag[i]);
        pick(mbits[i]);
        slots[i].tag = mtag[i];
        slots[i].bits = mbits[i];
    }
    vx_store_init(&st, slots, nslots, jour, jcap, out, ocap);
    molen = 0;
    mjlen = 0;
    depth = 0;

    for (k = 0; k < STEPS; k++) {
        uint8_t op = nondet_u8();
        if (op == 0) {
            if (depth < MAXD) {
                vx_store_mark(&st, &marks[depth]);
                for (i = 0; i < nslots; i++) { ctag[depth][i] = mtag[i]; cbits[depth][i] = mbits[i]; }
                for (i = 0; i < molen; i++) cout[depth][i] = mout[i];
                colen[depth] = molen;
                cjlen[depth] = mjlen;
                depth = depth + 1;
            }
        } else if (op == 1) {
            size_t sl = nondet_size();
            uint64_t tg, bt;
            int r;
            pick(tg);
            pick(bt);
            r = vx_store_set(&st, sl, tg, bt);
            if (sl >= nslots) {
                qp_assert(r == VX_ESLOT);
            } else if (depth > 0 && mjlen >= jcap) {
                qp_assert(r == VX_EFULL);
            } else {
                qp_assert(r == VX_OK);
                mtag[sl] = tg;
                mbits[sl] = bt;
                if (depth > 0) mjlen = mjlen + 1;
            }
        } else if (op == 2) {
            uint8_t bs[2];
            size_t n = nondet_size() % 3;
            int r;
            nondet_bytes(bs, 2);
            r = vx_store_out_append(&st, bs, n);
            if (n > ocap - molen) {
                qp_assert(r == VX_EFULL);
            } else {
                qp_assert(r == VX_OK);
                for (i = 0; i < n; i++) mout[molen + i] = bs[i];
                molen = molen + n;
            }
        } else if (op == 3) {
            if (depth > 0) {
                depth = depth - 1;
                vx_store_rollback(&st, &marks[depth]);
                for (i = 0; i < nslots; i++) { mtag[i] = ctag[depth][i]; mbits[i] = cbits[depth][i]; }
                for (i = 0; i < colen[depth]; i++) mout[i] = cout[depth][i];
                molen = colen[depth];
                mjlen = cjlen[depth];
            }
        } else if (op == 4) {
            if (depth > 0) {
                depth = depth - 1;
                vx_store_commit(&st, &marks[depth]);
                if (depth == 0) mjlen = 0;
            }
        }
        /* the store agrees with the model */
        qp_assert(vx_store_out_len(&st) == molen);
        for (i = 0; i < nslots; i++) {
            vx_val v;
            qp_assert(vx_store_get(&st, i, &v) == VX_OK);
            qp_assert(v.tag == mtag[i]);
            qp_assert(v.bits == mbits[i]);
        }
        for (i = 0; i < molen; i++) qp_assert(out[i] == mout[i]);
    }
    {
        vx_val v;
        qp_assert(vx_store_get(&st, nslots, &v) == VX_ESLOT);
    }
    free(out);
    free(jour);
    free(slots);
    return 0;
}
