/*
 * store.c -- the machine state St of OpenVerse/Core/Semantics.lean: the
 * frame slots and the output, made transactional with an undo journal.
 *
 * The rules this implements:
 *   Eval.ite_fail  -- a failed `if` condition: the else branch starts from
 *                     the state before the condition (slots AND output);
 *   EvalFor.skip   -- a failed `for` filter: the next element starts from
 *                     the state after binding the element.
 * The interpreter takes a mark when it enters such a failure context and
 * then either rolls back to it (the context failed) or commits it (any
 * other outcome: the effects stay, see Eval.ite_stop / EvalFor.filt_stop).
 *
 * Writes are logged only while depth > 0: outside every failure context
 * nothing can be rolled back.  When the outermost context commits, no mark
 * can refer to the journal any more and it is cleared.
 *
 * Values are two opaque words; the store copies them and never interprets
 * them.  QuickProof subset: no goto, no struct assignment, no struct
 * arguments or results, no switch, no recursion, no allocation.
 */
#include "openverse.h"

void vx_store_init(vx_store *s, vx_val *slots, size_t nslots,
                   vx_undo *jour, size_t jcap, uint8_t *out, size_t ocap)
{
    s->slots = slots;
    s->nslots = nslots;
    s->jour = jour;
    s->jcap = jcap;
    s->jlen = 0;
    s->out = out;
    s->ocap = ocap;
    s->olen = 0;
    s->depth = 0;
}

int vx_store_get(const vx_store *s, size_t slot, vx_val *v)
{
    if (slot >= s->nslots)
        return VX_ESLOT;
    v->tag = s->slots[slot].tag;
    v->bits = s->slots[slot].bits;
    return VX_OK;
}

/* Write a slot, logging its old value when inside a failure context.
 * On VX_EFULL nothing changes (the caller may move to a larger journal
 * and retry). */
int vx_store_set(vx_store *s, size_t slot, uint64_t tag, uint64_t bits)
{
    if (slot >= s->nslots)
        return VX_ESLOT;
    if (s->depth > 0) {
        if (s->jlen >= s->jcap)
            return VX_EFULL;
        s->jour[s->jlen].slot = slot;
        s->jour[s->jlen].tag = s->slots[slot].tag;
        s->jour[s->jlen].bits = s->slots[slot].bits;
        s->jlen = s->jlen + 1;
    }
    s->slots[slot].tag = tag;
    s->slots[slot].bits = bits;
    return VX_OK;
}

/* Write a slot without logging.  Only for slots that no live mark can see:
 * the interpreter uses it to fill a fresh callee frame (frameOf), which
 * lies above every frame that existed when any current mark was taken. */
int vx_store_put(vx_store *s, size_t slot, uint64_t tag, uint64_t bits)
{
    if (slot >= s->nslots)
        return VX_ESLOT;
    s->slots[slot].tag = tag;
    s->slots[slot].bits = bits;
    return VX_OK;
}

/* Enter a failure context. */
void vx_store_mark(vx_store *s, vx_mark *m)
{
    m->jlen = s->jlen;
    m->olen = s->olen;
    m->depth = s->depth;
    s->depth = s->depth + 1;
}

/* Leave a failure context that failed: undo every write logged since the
 * mark, newest first, and drop the output written since the mark. */
void vx_store_rollback(vx_store *s, const vx_mark *m)
{
    size_t sl;
    while (s->jlen > m->jlen) {
        s->jlen = s->jlen - 1;
        sl = s->jour[s->jlen].slot;
        if (sl < s->nslots) {
            s->slots[sl].tag = s->jour[s->jlen].tag;
            s->slots[sl].bits = s->jour[s->jlen].bits;
        }
    }
    if (s->olen > m->olen)
        s->olen = m->olen;
    s->depth = m->depth;
    if (s->depth == 0)
        s->jlen = 0;
}

/* Leave a failure context keeping its effects.  The entries stay in the
 * journal for the enclosing contexts; leaving the outermost clears it. */
void vx_store_commit(vx_store *s, const vx_mark *m)
{
    s->depth = m->depth;
    if (s->depth == 0)
        s->jlen = 0;
}

size_t vx_store_journal_len(const vx_store *s)
{
    return s->jlen;
}

/* Drop the journal entries above jlen.  The interpreter calls this when a
 * call returns, with the journal length at the call: every entry logged by
 * the callee is for a slot of a frame that no longer exists (a callee
 * cannot write its caller's frame), so restoring it could not be observed. */
void vx_store_forget(vx_store *s, size_t jlen)
{
    if (jlen < s->jlen)
        s->jlen = jlen;
}

/* Append n bytes to the output, all or nothing. */
int vx_store_out_append(vx_store *s, const uint8_t *b, size_t n)
{
    size_t i;
    if (n > s->ocap - s->olen)
        return VX_EFULL;
    for (i = 0; i < n; i++)
        s->out[s->olen + i] = b[i];
    s->olen = s->olen + n;
    return VX_OK;
}

size_t vx_store_out_len(const vx_store *s)
{
    return s->olen;
}

int vx_store_move_slots(vx_store *s, vx_val *slots, size_t nslots)
{
    size_t i;
    if (nslots < s->nslots)
        return VX_EFULL;
    for (i = 0; i < s->nslots; i++) {
        slots[i].tag = s->slots[i].tag;
        slots[i].bits = s->slots[i].bits;
    }
    s->slots = slots;
    s->nslots = nslots;
    return VX_OK;
}

int vx_store_move_journal(vx_store *s, vx_undo *jour, size_t jcap)
{
    size_t i;
    if (jcap < s->jlen)
        return VX_EFULL;
    for (i = 0; i < s->jlen; i++) {
        jour[i].slot = s->jour[i].slot;
        jour[i].tag = s->jour[i].tag;
        jour[i].bits = s->jour[i].bits;
    }
    s->jour = jour;
    s->jcap = jcap;
    return VX_OK;
}

int vx_store_move_out(vx_store *s, uint8_t *out, size_t ocap)
{
    size_t i;
    if (ocap < s->olen)
        return VX_EFULL;
    for (i = 0; i < s->olen; i++)
        out[i] = s->out[i];
    s->out = out;
    s->ocap = ocap;
    return VX_OK;
}
