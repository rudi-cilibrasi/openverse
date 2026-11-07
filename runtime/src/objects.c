/*
 * objects.c -- the object store: class instances, `Glob.heap` of
 * OpenVerse/Core/Semantics.lean (#20, #31).  See vx_runtime.h.
 *
 * Lean's failure contexts restart from the state before the context, heap
 * included.  Here a context takes a mark; rollback undoes the field writes
 * logged since the mark (newest first, so each cell gets back the value it
 * had at the mark) and drops the objects allocated since it, so the next
 * allocation gets the index Lean gives it (`g.heap.length`).
 */
#include <stdlib.h>
#include <string.h>
#include "vx_runtime.h"

void vx_objs_init(vx_objs *h, size_t max, size_t max_log)
{
    memset(h, 0, sizeof *h);
    h->max = max;
    h->max_log = max_log;
}

void vx_objs_free(vx_objs *h)
{
    free(h->objs);
    free(h->cells);
    free(h->log);
    {
        size_t i;
        for (i = 0; i < h->nbufs; i++)
            free(h->bufs[i].cells);
    }
    free(h->bufs);
    free(h->freeb);
    free(h->atdepth);
    free(h->rbuf);
    free(h->rindex);
    memset(h, 0, sizeof *h);
}

/* Room for `need` elements of `size` bytes in *buf (capacity *cap, at most max). */
/* The per-call arrays (a list and a buffer per active call) grow with the
   recursion depth, which the interpreter bounds itself: not with the heap. */
#define DEPTH_MAX ((size_t)(SIZE_MAX < (UINT64_C(1) << 40) ? SIZE_MAX : (UINT64_C(1) << 40)))

static int reserve(void **buf, size_t *cap, size_t need, size_t size, size_t max)
{
    size_t ncap;
    void *b;
    if (max > SIZE_MAX / size)
        max = SIZE_MAX / size;
    if (need <= *cap)
        return 1;
    if (need > max)
        return 0;
    ncap = *cap ? *cap : 64;
    while (ncap < need)
        ncap = ncap > max / 2 ? max : ncap * 2;
    b = realloc(*buf, ncap * size);
    if (b == NULL)
        return 0;
    *buf = b;
    *cap = ncap;
    return 1;
}

int vx_objs_new(vx_objs *h, uint64_t tag, const vx_val *f, size_t n, size_t *a)
{
    size_t used = h->nobjs + h->ncells;
    if (used > h->max || 1 + n > h->max - used)
        return VX_EFULL;
    if (!reserve((void **)&h->objs, &h->ocap, h->nobjs + 1, sizeof(vx_obj), h->max) ||
        !reserve((void **)&h->cells, &h->ccap, h->ncells + n, sizeof(vx_val), h->max))
        return VX_EFULL;
    if (n > 0)
        memcpy(&h->cells[h->ncells], f, n * sizeof(vx_val));
    h->objs[h->nobjs].tag = tag;
    h->objs[h->nobjs].off = h->ncells;
    h->objs[h->nobjs].n = n;
    *a = h->nobjs;
    h->nobjs = h->nobjs + 1;
    h->ncells = h->ncells + n;
    return VX_OK;
}

int vx_objs_set(vx_objs *h, uint64_t a, size_t k, const vx_val *v, int log)
{
    size_t cell = h->objs[a].off + k;
    if (log) {
        if (!reserve((void **)&h->log, &h->lcap, h->nlog + 1, sizeof(vx_oundo), h->max_log))
            return VX_EFULL;
        h->log[h->nlog].cell = cell;
        h->log[h->nlog].old = h->cells[cell];
        h->nlog = h->nlog + 1;
    }
    h->cells[cell] = *v;
    return VX_OK;
}

void vx_objs_mark(const vx_objs *h, vx_objmark *m)
{
    m->nobjs = h->nobjs;
    m->ncells = h->ncells;
    m->nlog = h->nlog;
}

/* Remove cell's entry from its list (swap with the last). */
static void unremember(vx_objs *h, size_t cell)
{
    vx_remlist *l;
    size_t i, last;
    if (cell >= h->pcap || h->rbuf[cell] == 0)
        return;
    l = &h->bufs[h->rbuf[cell] - 1];
    i = h->rindex[cell];
    last = l->cells[l->n - 1];
    l->cells[i] = last;
    h->rindex[last] = i;
    l->n = l->n - 1;
    h->rbuf[cell] = 0;
}

static int buf_push(vx_objs *h, size_t b, size_t cell)
{
    vx_remlist *l = &h->bufs[b];
    if (!reserve((void **)&l->cells, &l->cap, l->n + 1, sizeof(size_t), h->max))
        return 0;
    l->cells[l->n] = cell;
    h->rbuf[cell] = b + 1;
    h->rindex[cell] = l->n;
    l->n = l->n + 1;
    return 1;
}

void vx_objs_rollback(vx_objs *h, const vx_objmark *m)
{
    while (h->nlog > m->nlog) {
        h->nlog = h->nlog - 1;
        h->cells[h->log[h->nlog].cell] = h->log[h->nlog].old;
    }
    /* the cells of the objects dropped lose their entries; the others keep
       theirs (a value rollback restores is older than the context, and its
       entry is in a list at least as deep as its owner) */
    {
        size_t cell;
        for (cell = m->ncells; cell < h->ncells; cell++)
            unremember(h, cell);
    }
    h->nobjs = m->nobjs;
    h->ncells = m->ncells;
}

/* A buffer for the call at `depth` (from the free list, or a new one). */
static int buf_for(vx_objs *h, size_t depth)
{
    size_t b;
    if (h->nfree > 0) {
        h->nfree = h->nfree - 1;
        b = h->freeb[h->nfree];
    } else {
        /* a new buffer; the free list can then hold every buffer, so a
           return never needs memory to free one */
        size_t old = h->bcap;
        if (!reserve((void **)&h->bufs, &h->bcap, h->nbufs + 1, sizeof(vx_remlist), DEPTH_MAX) ||
            !reserve((void **)&h->freeb, &h->fbcap, h->nbufs + 1, sizeof(size_t), DEPTH_MAX))
            return 0;
        if (h->bcap > old)
            memset(&h->bufs[old], 0, (h->bcap - old) * sizeof(vx_remlist));
        b = h->nbufs;
        h->nbufs = h->nbufs + 1;
    }
    h->bufs[b].n = 0;
    h->bufs[b].depth = depth;
    h->atdepth[depth] = b;
    return 1;
}

static void buf_free(vx_objs *h, size_t b)
{
    h->bufs[b].n = 0;
    h->freeb[h->nfree] = b;
    h->nfree = h->nfree + 1;
}

int vx_objs_remember(vx_objs *h, size_t cell, size_t depth)
{
    if (depth >= h->nlists)
        return VX_OK;   /* not owned by an active call */
    if (cell >= h->pcap) {
        size_t old = h->pcap, cap1 = h->pcap;
        if (!reserve((void **)&h->rindex, &cap1, cell + 1, sizeof(size_t), h->max) ||
            !reserve((void **)&h->rbuf, &h->pcap, cell + 1, sizeof(size_t), h->max))
            return VX_EFULL;
        memset(&h->rbuf[old], 0, (h->pcap - old) * sizeof(size_t));
    }
    if (h->rbuf[cell] != 0 && h->bufs[h->rbuf[cell] - 1].depth >= depth)
        return VX_OK;   /* in a list at least as deep already */
    if (h->atdepth[depth] == VX_NOBUF && !buf_for(h, depth))
        return VX_EFULL;
    unremember(h, cell);
    return buf_push(h, h->atdepth[depth], cell) ? VX_OK : VX_EFULL;
}

int vx_objs_call(vx_objs *h)
{
    if (h->nlists == h->dcap &&
        !reserve((void **)&h->atdepth, &h->dcap, h->nlists + 1, sizeof(size_t), DEPTH_MAX))
        return VX_EFULL;
    h->atdepth[h->nlists] = VX_NOBUF;
    h->nlists = h->nlists + 1;
    return VX_OK;
}

int vx_objs_return(vx_objs *h)
{
    size_t top, b, p, big, small, i;
    if (h->nlists == 0)
        return VX_OK;
    top = h->nlists - 1;
    b = h->atdepth[top];
    h->nlists = top;
    if (b == VX_NOBUF)
        return VX_OK;
    if (top == 0) {
        for (i = 0; i < h->bufs[b].n; i++)
            h->rbuf[h->bufs[b].cells[i]] = 0;
        buf_free(h, b);
        return VX_OK;
    }
    p = h->atdepth[top - 1];
    if (p == VX_NOBUF) {
        /* the caller's list is the callee's */
        h->bufs[b].depth = top - 1;
        h->atdepth[top - 1] = b;
        return VX_OK;
    }
    /* the smaller list into the larger, which serves the caller */
    big = h->bufs[b].n >= h->bufs[p].n ? b : p;
    small = big == b ? p : b;
    for (i = 0; i < h->bufs[small].n; i++)
        if (!buf_push(h, big, h->bufs[small].cells[i]))
            return VX_EFULL;
    h->bufs[big].depth = top - 1;
    h->atdepth[top - 1] = big;
    buf_free(h, small);
    return VX_OK;
}

const vx_remlist *vx_objs_top(const vx_objs *h)
{
    size_t b = h->nlists > 0 ? h->atdepth[h->nlists - 1] : VX_NOBUF;
    return b == VX_NOBUF ? NULL : &h->bufs[b];
}

void vx_objs_drop_stale(vx_objs *h)
{
    vx_remlist *l;
    size_t i = 0;
    if (h->nlists == 0 || h->atdepth[h->nlists - 1] == VX_NOBUF)
        return;
    l = &h->bufs[h->atdepth[h->nlists - 1]];
    while (i < l->n) {
        size_t cell = l->cells[i];
        const vx_val *v = &h->cells[cell];
        if (!vx_isref(v) || v->bits == 0)
            unremember(h, cell);   /* the last entry moves to i */
        else
            i++;
    }
}

void vx_objs_forget(vx_objs *h)
{
    h->nlog = 0;
}
