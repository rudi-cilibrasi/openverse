/*
 * value.c -- the heap of Verse values: allocation, reclamation when a call
 * returns, and structural equality.  See vx_runtime.h for the layout.
 */
#include <stdlib.h>
#include <string.h>
#include "vx_runtime.h"

#define VX_HEAP_INIT 4096u
#define VX_MARKED    UINT64_MAX   /* header.bits during vx_heap_keep */

int vx_heap_init(vx_heap *h, size_t max_cells)
{
    size_t cap = VX_HEAP_INIT;
    if (max_cells < 1)
        max_cells = 1;
    if (cap > max_cells)
        cap = max_cells;
    h->cells = malloc(cap * sizeof(vx_val));
    h->len = 0;
    h->cap = 0;
    h->max = max_cells;
    if (h->cells == NULL)
        return VX_EFULL;
    h->cap = cap;
    h->cells[0].tag = 0;   /* the shared empty object */
    h->cells[0].bits = 0;
    h->len = 1;
    return VX_OK;
}

void vx_heap_free(vx_heap *h)
{
    free(h->cells);
    h->cells = NULL;
    h->len = h->cap = 0;
}

int vx_heap_alloc(vx_heap *h, size_t n, size_t *idx)
{
    size_t need;
    if (n == 0) {
        *idx = 0;
        return VX_OK;
    }
    if (n >= h->max || h->len > h->max - 1 - n)
        return VX_EFULL;
    need = h->len + 1 + n;
    if (need > h->cap) {
        size_t cap = h->cap * 2;
        vx_val *cells;
        if (cap < need)
            cap = need;
        if (cap > h->max)
            cap = h->max;
        cells = realloc(h->cells, cap * sizeof(vx_val));
        if (cells == NULL)
            return VX_EFULL;
        h->cells = cells;
        h->cap = cap;
    }
    *idx = h->len;
    h->cells[h->len].tag = n;
    h->cells[h->len].bits = 0;
    h->len = need;
    return VX_OK;
}

/* ----------------------------------------------------------- reclamation */

/* A growable stack of heap indices. */
typedef struct {
    size_t *a;
    size_t  n;
    size_t  cap;
} idxstack;

static int ix_push(idxstack *s, size_t x)
{
    if (s->n == s->cap) {
        size_t cap = s->cap ? s->cap * 2 : 64;
        size_t *a = realloc(s->a, cap * sizeof(size_t));
        if (a == NULL)
            return 0;
        s->a = a;
        s->cap = cap;
    }
    s->a[s->n++] = x;
    return 1;
}

/*
 * Sliding compaction of [mark, len): mark what the roots reach inside the
 * region, give each marked object its new index (header.bits), redirect the
 * references (the roots' too), then slide the objects down in order.
 * Objects below mark never refer into the region (they are older and
 * immutable), and the interpreter passes as roots everything else that may
 * (interp.c, call_fn), so everything unmarked is garbage.
 */
/* Mark what the stack's objects reach in the region; *count (if not NULL)
   gets the cells marked. */
static int mark_loop(vx_heap *h, size_t mark, idxstack *st, size_t *count)
{
    vx_val *cells = h->cells;
    size_t o, n, k;
    while (st->n > 0) {
        o = st->a[--st->n];
        if (cells[o].bits != 0)
            continue;
        cells[o].bits = VX_MARKED;
        n = (size_t)cells[o].tag;
        if (count != NULL)
            *count += 1 + n;
        for (k = 0; k < n; k++) {
            const vx_val *e = &cells[o + 1 + k];
            if (vx_isref(e) && e->bits >= mark && cells[e->bits].bits == 0) {
                if (!ix_push(st, (size_t)e->bits)) {
                    /* undo the marks so the heap stays consistent */
                    for (o = mark; o < h->len; o += 1 + (size_t)cells[o].tag)
                        cells[o].bits = 0;
                    return 0;
                }
            }
        }
    }
    return 1;
}

int vx_heap_keep_roots(vx_heap *h, size_t mark, vx_val **roots, size_t nr, size_t *fieldkept)
{
    idxstack st = { NULL, 0, 0 };
    vx_val *cells = h->cells;
    size_t o, n, k, dst, i, fk = 0;
    int any = 0;

    if (fieldkept != NULL)
        *fieldkept = 0;
    for (i = 0; i < nr; i++)
        if (vx_isref(roots[i]) && roots[i]->bits >= mark)
            any = 1;
    if (!any) {
        h->len = mark;
        return VX_OK;
    }
    /* 1. mark: from the fields (roots[1..]) first, counting what they reach,
          then from the result (roots[0]) */
    for (i = 1; i < nr; i++)
        if (vx_isref(roots[i]) && roots[i]->bits >= mark && !ix_push(&st, (size_t)roots[i]->bits)) {
            free(st.a);
            return VX_EFULL;
        }
    if (!mark_loop(h, mark, &st, &fk)) {
        free(st.a);
        return VX_EFULL;
    }
    if (nr > 0 && vx_isref(roots[0]) && roots[0]->bits >= mark) {
        if (!ix_push(&st, (size_t)roots[0]->bits)) {
            for (o = mark; o < h->len; o += 1 + (size_t)cells[o].tag)
                cells[o].bits = 0;
            free(st.a);
            return VX_EFULL;
        }
        if (!mark_loop(h, mark, &st, NULL)) {
            free(st.a);
            return VX_EFULL;
        }
    }
    free(st.a);
    if (fieldkept != NULL)
        *fieldkept = fk;
    /* 2. new indices (all >= mark >= 1, so nonzero) */
    dst = mark;
    for (o = mark; o < h->len; o += 1 + n) {
        n = (size_t)cells[o].tag;
        if (cells[o].bits == VX_MARKED) {
            cells[o].bits = dst;
            dst += 1 + n;
        }
    }
    /* 3. redirect references into the region, the roots' too */
    for (o = mark; o < h->len; o += 1 + n) {
        n = (size_t)cells[o].tag;
        if (cells[o].bits != 0) {
            for (k = 0; k < n; k++) {
                vx_val *e = &cells[o + 1 + k];
                if (vx_isref(e) && e->bits >= mark)
                    e->bits = cells[e->bits].bits;
            }
        }
    }
    for (i = 0; i < nr; i++)
        if (vx_isref(roots[i]) && roots[i]->bits >= mark)
            roots[i]->bits = cells[roots[i]->bits].bits;
    /* 4. slide down, in index order (destination <= source) */
    for (o = mark; o < h->len; o += 1 + n) {
        size_t to;
        n = (size_t)cells[o].tag;
        to = (size_t)cells[o].bits;
        if (to != 0) {
            memmove(&cells[to], &cells[o], (1 + n) * sizeof(vx_val));
            cells[to].bits = 0;
        }
    }
    h->len = dst;
    return VX_OK;
}

int vx_heap_keep(vx_heap *h, size_t mark, vx_val *root)
{
    return vx_heap_keep_roots(h, mark, &root, 1, NULL);
}

/* -------------------------------------------------------------- equality */

/* 0: different, 1: equal, 2: distinct objects of the same tag and length
 * (compare the elements). */
static int shallow_eq(const vx_heap *h, const vx_val *a, const vx_val *b)
{
    if (a->tag != b->tag)
        return 0;
    if (!vx_isref(a))
        return a->bits == b->bits;
    if (a->bits == b->bits)
        return 1;
    if (vx_obj_len(h, a->bits) != vx_obj_len(h, b->bits))
        return 0;
    return vx_obj_len(h, a->bits) == 0 ? 1 : 2;
}

typedef struct {
    size_t x, y, k, n;
} eqframe;

int vx_equal(const vx_heap *h, const vx_val *a, const vx_val *b, int *eq)
{
    eqframe *st = NULL;
    size_t sp = 0, cap = 0;
    int s = shallow_eq(h, a, b);
    if (s != 2) {
        *eq = s;
        return VX_OK;
    }
    for (;;) {
        if (s == 2) {
            const vx_val *x = sp == 0 ? a : &h->cells[st[sp - 1].x + st[sp - 1].k];
            const vx_val *y = sp == 0 ? b : &h->cells[st[sp - 1].y + st[sp - 1].k];
            if (sp == cap) {
                size_t ncap = cap ? cap * 2 : 32;
                eqframe *ns = realloc(st, ncap * sizeof(eqframe));
                if (ns == NULL) {
                    free(st);
                    return VX_EFULL;
                }
                st = ns;
                cap = ncap;
            }
            st[sp].x = (size_t)x->bits;
            st[sp].y = (size_t)y->bits;
            st[sp].k = 0;
            st[sp].n = vx_obj_len(h, x->bits);
            sp++;
        }
        /* advance to the next element pair of the innermost frame */
        while (sp > 0 && st[sp - 1].k == st[sp - 1].n)
            sp--;
        if (sp == 0)
            break;
        st[sp - 1].k++;   /* element k-1 is at cells[x + k] */
        s = shallow_eq(h, &h->cells[st[sp - 1].x + st[sp - 1].k],
                          &h->cells[st[sp - 1].y + st[sp - 1].k]);
        if (s == 0) {
            free(st);
            *eq = 0;
            return VX_OK;
        }
    }
    free(st);
    *eq = 1;
    return VX_OK;
}
