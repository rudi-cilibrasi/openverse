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
    free(h->rem);
    free(h->rpos);
    memset(h, 0, sizeof *h);
}

/* Room for `need` elements of `size` bytes in *buf (capacity *cap, at most max). */
static int reserve(void **buf, size_t *cap, size_t need, size_t size, size_t max)
{
    size_t ncap;
    void *b;
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
    m->nrem = h->nrem;
}

void vx_objs_rollback(vx_objs *h, const vx_objmark *m)
{
    while (h->nlog > m->nlog) {
        h->nlog = h->nlog - 1;
        h->cells[h->log[h->nlog].cell] = h->log[h->nlog].old;
    }
    /* the entries made in the context go: a value rollback restores was
       written before it, and its entry is older */
    while (h->nrem > m->nrem) {
        size_t cell;
        h->nrem = h->nrem - 1;
        cell = h->rem[h->nrem];
        if (cell < h->pcap && h->rpos[cell] == h->nrem + 1)
            h->rpos[cell] = 0;
    }
    h->nobjs = m->nobjs;
    h->ncells = m->ncells;
}

int vx_objs_remember(vx_objs *h, size_t cell, size_t seg0)
{
    if (cell >= h->pcap) {
        size_t old = h->pcap;
        if (!reserve((void **)&h->rpos, &h->pcap, cell + 1, sizeof(size_t), h->max))
            return VX_EFULL;
        memset(&h->rpos[old], 0, (h->pcap - old) * sizeof(size_t));
    }
    if (h->rpos[cell] != 0 && h->rpos[cell] - 1 >= seg0)
        return VX_OK;   /* already in this call's entries */
    if (!reserve((void **)&h->rem, &h->rcap, h->nrem + 1, sizeof(size_t), h->max))
        return VX_EFULL;
    h->rem[h->nrem] = cell;
    h->nrem = h->nrem + 1;
    h->rpos[cell] = h->nrem;
    return VX_OK;
}

void vx_objs_forget(vx_objs *h)
{
    h->nlog = 0;
}
