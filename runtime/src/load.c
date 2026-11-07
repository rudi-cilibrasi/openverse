/*
 * load.c -- the OVBC loader (docs/FORMAT.md).
 *
 * vx_load accepts a buffer exactly when it parses to the end with no bytes
 * left over and conditions 1-7 of FORMAT.md "What the loader accepts" hold:
 *
 *   1. magic "OVBC", version 1, nfns >= 1, entry < nfns   load_header
 *   2. arity <= nslots, nnodes >= 1, root < nnodes        load_fn
 *   3. every child index of node j is < j                 rd_child
 *   4. every slot (LOCAL, ASSIGN, FOR) is < nslots        rd_slot
 *   5. CALL fn < nfns                                     load_call
 *      ... and n == arity of fn                           check_calls
 *   6. prim code <= 28, k == 0 unless tupGet,             load_prim
 *      lit kind <= 6, LOGIC byte <= 1                     load_lit
 *      heap op <= 4, k == 0 for tag                       load_heap
 *   7. counts within the VX_MAX_* limits of openverse.h   throughout
 *
 * One forward pass over the input.  The arity half of condition 5 is
 * checked afterwards over the node tables, because a call may name a
 * function that comes later in the file.  Every read goes through rd_u8 /
 * rd_u32 / rd_i64 / rd_bytes, which check the remaining length first, so
 * the loader reads only inside buf[0..len) (invariant: pos <= len).
 *
 * Memory: the function table and each node table are malloc'd with the
 * exact count from the header, after checking the count against the limit
 * and against the bytes left.  Child lists and bytes go into two pools sized
 * by the input (an argument takes 4 input bytes, a string or isTag byte 1), which are
 * trimmed to their exact size at the end.  On any error everything is freed.
 *
 * QuickProof subset: no goto, no recursion, no switch, no struct assignment
 * or struct arguments/results, no casts between pointers and integers, no
 * free(NULL), libc limited to malloc/free.
 */
#include <stdlib.h>
#include "openverse.h"

/* The smallest encoded function: arity, nslots, decides, namelen, nnodes,
 * one 1-byte node (BRK), root. */
#define VX_MIN_FN_BYTES 22u

typedef struct vx_ld {
    const uint8_t *buf;
    size_t len;
    size_t pos;   /* next byte to read; pos <= len */
    size_t acap;  /* capacity of prog->args (entries) */
    size_t bcap;  /* capacity of prog->bytes */
} vx_ld;

/* ------------------------------------------------------------------ reads */

static int rd_u8(vx_ld *r, uint32_t *out)
{
    if (r->len - r->pos < 1)
        return VX_LOAD_TRUNCATED;
    *out = r->buf[r->pos];
    r->pos = r->pos + 1;
    return VX_LOAD_OK;
}

static int rd_u32(vx_ld *r, uint32_t *out)
{
    uint32_t v;
    if (r->len - r->pos < 4)
        return VX_LOAD_TRUNCATED;
    v = (uint32_t)r->buf[r->pos];
    v = v | ((uint32_t)r->buf[r->pos + 1] << 8);
    v = v | ((uint32_t)r->buf[r->pos + 2] << 16);
    v = v | ((uint32_t)r->buf[r->pos + 3] << 24);
    *out = v;
    r->pos = r->pos + 4;
    return VX_LOAD_OK;
}

/* Two's complement little-endian, converted without implementation-defined
 * behaviour: u > INT64_MAX encodes u - 2^64 = -(~u) - 1. */
static int rd_i64(vx_ld *r, int64_t *out)
{
    uint64_t u = 0;
    size_t k;
    if (r->len - r->pos < 8)
        return VX_LOAD_TRUNCATED;
    for (k = 0; k < 8; k++)
        u = u | ((uint64_t)r->buf[r->pos + k] << (8 * k));
    r->pos = r->pos + 8;
    if (u <= (uint64_t)INT64_MAX)
        *out = (int64_t)u;
    else
        *out = -(int64_t)(~u) - 1;
    return VX_LOAD_OK;
}

/* n bytes appended to the bytes pool; *off is where they start. */
static int rd_bytes(vx_ld *r, vx_program *p, uint32_t n, uint32_t *off)
{
    uint32_t i;
    if (n > VX_MAX_STR)
        return VX_LOAD_LIMIT;
    if ((size_t)n > r->len - r->pos)
        return VX_LOAD_TRUNCATED;
    if ((size_t)n > r->bcap - (size_t)p->nbytes)
        return VX_LOAD_LIMIT;   /* not reachable: bcap is the input size */
    *off = p->nbytes;
    for (i = 0; i < n; i++)
        p->bytes[p->nbytes + i] = r->buf[r->pos + i];
    p->nbytes = p->nbytes + n;
    r->pos = r->pos + n;
    return VX_LOAD_OK;
}

/* A child index of node j (condition 3). */
static int rd_child(vx_ld *r, uint32_t j, uint32_t *out)
{
    if (rd_u32(r, out) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (*out >= j)
        return VX_LOAD_CHILD;
    return VX_LOAD_OK;
}

/* A slot index (condition 4). */
static int rd_slot(vx_ld *r, uint32_t nslots, uint32_t *out)
{
    if (rd_u32(r, out) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (*out >= nslots)
        return VX_LOAD_SLOT;
    return VX_LOAD_OK;
}

/* n child indices of node j, appended to the args pool at *off. */
static int rd_args(vx_ld *r, vx_program *p, uint32_t j, uint32_t n, uint32_t *off)
{
    uint32_t k;
    uint32_t x;
    int rc;
    if (n > VX_MAX_ARGS)
        return VX_LOAD_LIMIT;
    *off = p->nargs;
    for (k = 0; k < n; k++) {
        rc = rd_child(r, j, &x);
        if (rc != VX_LOAD_OK)
            return rc;
        if ((size_t)p->nargs >= r->acap)
            return VX_LOAD_LIMIT;   /* not reachable: 4 input bytes per entry */
        p->args[p->nargs] = x;
        p->nargs = p->nargs + 1;
    }
    return VX_LOAD_OK;
}

/* ------------------------------------------------------------------ nodes */

static void node_clear(vx_node *nd)
{
    nd->tag = 0;
    nd->op = 0;
    nd->a = 0;
    nd->b = 0;
    nd->c = 0;
    nd->d = 0;
    nd->lit = 0;
}

/* LIT: kind, then the payload of FORMAT.md's Lit (condition 6). */
static int load_lit(vx_ld *r, vx_program *p, vx_node *nd)
{
    uint32_t kind;
    uint32_t x;
    int64_t i;
    if (rd_u8(r, &kind) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (kind > VX_LIT_LAST)
        return VX_LOAD_LIT;
    nd->op = kind;
    if (kind == VX_LIT_INT) {
        if (rd_i64(r, &i) != VX_LOAD_OK)
            return VX_LOAD_TRUNCATED;
        nd->lit = i;
    } else if (kind == VX_LIT_LOGIC) {
        if (rd_u8(r, &x) != VX_LOAD_OK)
            return VX_LOAD_TRUNCATED;
        if (x > 1)
            return VX_LOAD_LOGIC;
        nd->lit = (int64_t)x;
    } else if (kind == VX_LIT_CHAR) {
        if (rd_u8(r, &x) != VX_LOAD_OK)
            return VX_LOAD_TRUNCATED;
        nd->lit = (int64_t)x;
    } else if (kind == VX_LIT_STR) {
        if (rd_u32(r, &x) != VX_LOAD_OK)
            return VX_LOAD_TRUNCATED;
        nd->b = x;
        return rd_bytes(r, p, x, &nd->a);
    } else if (kind == VX_LIT_REF) {
        if (rd_u32(r, &x) != VX_LOAD_OK)
            return VX_LOAD_TRUNCATED;
        nd->lit = (int64_t)x;
    }
    return VX_LOAD_OK;   /* NONE, VOID: no payload */
}

/* PRIM: code, k, n, args (condition 6). */
static int load_prim(vx_ld *r, vx_program *p, uint32_t j, vx_node *nd)
{
    uint32_t code;
    uint32_t k;
    uint32_t n;
    if (rd_u8(r, &code) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (code > VX_P_LAST)
        return VX_LOAD_PRIM;
    if (rd_u32(r, &k) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (k != 0 && code != VX_P_TUPGET)
        return VX_LOAD_K;
    if (rd_u32(r, &n) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    nd->op = code;
    nd->a = k;
    nd->b = n;
    return rd_args(r, p, j, n, &nd->c);
}

/* HEAP: op, then k (for ISTAG: m and m tags, into the bytes pool), n, args
   (condition 6). */
static int load_heap(vx_ld *r, vx_program *p, uint32_t j, vx_node *nd)
{
    uint32_t op;
    uint32_t k;
    uint32_t n;
    int rc;
    if (rd_u8(r, &op) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (op > VX_H_LAST)
        return VX_LOAD_HEAP;
    if (rd_u32(r, &k) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    nd->op = op;
    if (op == VX_H_ISTAG) {
        if (k > VX_MAX_TAGS)
            return VX_LOAD_LIMIT;
        nd->d = k;
        rc = rd_bytes(r, p, 4 * k, &nd->a);
        if (rc != VX_LOAD_OK)
            return rc;
    } else {
        if (k != 0 && op == VX_H_TAG)
            return VX_LOAD_K;
        nd->a = k;
    }
    if (rd_u32(r, &n) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    nd->b = n;
    return rd_args(r, p, j, n, &nd->c);
}

/* CALL: fn, n, args.  fn < nfns here; the arity in check_calls. */
static int load_call(vx_ld *r, vx_program *p, uint32_t j, vx_node *nd)
{
    uint32_t fn;
    uint32_t n;
    if (rd_u32(r, &fn) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (fn >= p->nfns)
        return VX_LOAD_CALL;
    if (rd_u32(r, &n) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    nd->a = fn;
    nd->b = n;
    return rd_args(r, p, j, n, &nd->c);
}

/* ITE c t e: three children. */
static int load_three(vx_ld *r, uint32_t j, vx_node *nd)
{
    int rc = rd_child(r, j, &nd->a);
    if (rc != VX_LOAD_OK)
        return rc;
    rc = rd_child(r, j, &nd->b);
    if (rc != VX_LOAD_OK)
        return rc;
    return rd_child(r, j, &nd->c);
}

/* FOR slot it filt body. */
static int load_for(vx_ld *r, uint32_t nslots, uint32_t j, vx_node *nd)
{
    int rc = rd_slot(r, nslots, &nd->a);
    if (rc != VX_LOAD_OK)
        return rc;
    rc = rd_child(r, j, &nd->b);
    if (rc != VX_LOAD_OK)
        return rc;
    rc = rd_child(r, j, &nd->c);
    if (rc != VX_LOAD_OK)
        return rc;
    return rd_child(r, j, &nd->d);
}

/* Node j of a function with nslots slots. */
static int load_node(vx_ld *r, vx_program *p, uint32_t nslots, uint32_t j, vx_node *nd)
{
    uint32_t tag;
    int rc;
    node_clear(nd);
    if (rd_u8(r, &tag) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    nd->tag = tag;
    if (tag == VX_N_LIT)
        return load_lit(r, p, nd);
    if (tag == VX_N_LOCAL)
        return rd_slot(r, nslots, &nd->a);
    if (tag == VX_N_ASSIGN) {
        rc = rd_slot(r, nslots, &nd->a);
        if (rc != VX_LOAD_OK)
            return rc;
        return rd_child(r, j, &nd->b);
    }
    if (tag == VX_N_SEQ) {
        rc = rd_child(r, j, &nd->a);
        if (rc != VX_LOAD_OK)
            return rc;
        return rd_child(r, j, &nd->b);
    }
    if (tag == VX_N_PRIM)
        return load_prim(r, p, j, nd);
    if (tag == VX_N_CALL)
        return load_call(r, p, j, nd);
    if (tag == VX_N_ITE)
        return load_three(r, j, nd);
    if (tag == VX_N_FOR)
        return load_for(r, nslots, j, nd);
    if (tag == VX_N_LOOP || tag == VX_N_RET || tag == VX_N_PRINT)
        return rd_child(r, j, &nd->a);
    if (tag == VX_N_BRK)
        return VX_LOAD_OK;
    if (tag == VX_N_HEAP)
        return load_heap(r, p, j, nd);
    return VX_LOAD_TAG;
}

/* -------------------------------------------------------------- functions */

/* Function f: header, nodes, root (condition 2). */
static int load_fn(vx_ld *r, vx_program *p, uint32_t f)
{
    vx_fn *fn = &p->fns[f];
    uint32_t arity;
    uint32_t nslots;
    uint32_t dec;
    uint32_t namelen;
    uint32_t nnodes;
    uint32_t root;
    uint32_t j;
    int rc;
    if (rd_u32(r, &arity) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (rd_u32(r, &nslots) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (rd_u8(r, &dec) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (nslots > VX_MAX_SLOTS)
        return VX_LOAD_LIMIT;
    if (arity > nslots)
        return VX_LOAD_ARITY;
    fn->arity = arity;
    fn->nslots = nslots;
    fn->decides = dec;
    if (rd_u32(r, &namelen) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    rc = rd_bytes(r, p, namelen, &fn->name_off);
    if (rc != VX_LOAD_OK)
        return rc;
    fn->name_len = namelen;
    if (rd_u32(r, &nnodes) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (nnodes == 0)
        return VX_LOAD_NONODES;
    if (nnodes > VX_MAX_NODES)
        return VX_LOAD_LIMIT;
    if ((size_t)nnodes > r->len - r->pos)
        return VX_LOAD_TRUNCATED;   /* every node takes at least one byte */
    fn->nodes = malloc((size_t)nnodes * sizeof(vx_node));
    if (fn->nodes == NULL)
        return VX_LOAD_NOMEM;
    fn->nnodes = nnodes;
    for (j = 0; j < nnodes; j++) {
        rc = load_node(r, p, nslots, j, &fn->nodes[j]);
        if (rc != VX_LOAD_OK)
            return rc;
    }
    if (rd_u32(r, &root) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (root >= nnodes)
        return VX_LOAD_ROOT;
    fn->root = root;
    return VX_LOAD_OK;
}

/* The arity half of condition 5, over the finished node tables. */
static int check_calls(const vx_program *p)
{
    uint32_t f;
    uint32_t j;
    const vx_node *nd;
    for (f = 0; f < p->nfns; f++) {
        for (j = 0; j < p->fns[f].nnodes; j++) {
            nd = &p->fns[f].nodes[j];
            if (nd->tag == VX_N_CALL && p->fns[nd->a].arity != nd->b)
                return VX_LOAD_CALLARITY;
        }
    }
    return VX_LOAD_OK;
}

/* "OVBC", version, nfns, main (condition 1); then the allocations. */
static int load_header(vx_ld *r, vx_program *p)
{
    uint32_t m0;
    uint32_t m1;
    uint32_t m2;
    uint32_t m3;
    uint32_t ver;
    uint32_t nfns;
    uint32_t entry_fn;
    uint32_t f;
    size_t rest;
    if (rd_u8(r, &m0) != VX_LOAD_OK || rd_u8(r, &m1) != VX_LOAD_OK ||
        rd_u8(r, &m2) != VX_LOAD_OK || rd_u8(r, &m3) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (m0 != 0x4fu || m1 != 0x56u || m2 != 0x42u || m3 != 0x43u)   /* "OVBC" */
        return VX_LOAD_MAGIC;
    if (rd_u32(r, &ver) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (ver != 1)
        return VX_LOAD_VERSION;
    if (rd_u32(r, &nfns) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (nfns == 0)
        return VX_LOAD_NOFNS;
    if (nfns > VX_MAX_FNS)
        return VX_LOAD_LIMIT;
    if (rd_u32(r, &entry_fn) != VX_LOAD_OK)
        return VX_LOAD_TRUNCATED;
    if (entry_fn >= nfns)
        return VX_LOAD_MAIN;
    rest = r->len - r->pos;
    if ((size_t)nfns > rest / VX_MIN_FN_BYTES)
        return VX_LOAD_TRUNCATED;
    /* Here rest >= 22, so neither pool is empty. */
    p->args = malloc((rest / 4) * sizeof(uint32_t));
    if (p->args == NULL)
        return VX_LOAD_NOMEM;
    r->acap = rest / 4;
    p->bytes = malloc(rest);
    if (p->bytes == NULL)
        return VX_LOAD_NOMEM;
    r->bcap = rest;
    p->fns = malloc((size_t)nfns * sizeof(vx_fn));
    if (p->fns == NULL)
        return VX_LOAD_NOMEM;
    for (f = 0; f < nfns; f++) {
        p->fns[f].arity = 0;
        p->fns[f].nslots = 0;
        p->fns[f].decides = 0;
        p->fns[f].name_off = 0;
        p->fns[f].name_len = 0;
        p->fns[f].nnodes = 0;
        p->fns[f].root = 0;
        p->fns[f].nodes = NULL;
    }
    p->nfns = nfns;
    p->entry = entry_fn;
    return VX_LOAD_OK;
}

/* Replace the pools by exactly sized copies (NULL when empty). */
static int trim_args(vx_program *p)
{
    uint32_t *a;
    uint32_t i;
    if (p->nargs == 0) {
        if (p->args != NULL)
            free(p->args);
        p->args = NULL;
        return VX_LOAD_OK;
    }
    a = malloc((size_t)p->nargs * sizeof(uint32_t));
    if (a == NULL)
        return VX_LOAD_NOMEM;
    for (i = 0; i < p->nargs; i++)
        a[i] = p->args[i];
    if (p->args != NULL)
        free(p->args);
    p->args = a;
    return VX_LOAD_OK;
}

static int trim_bytes(vx_program *p)
{
    uint8_t *b;
    uint32_t i;
    if (p->nbytes == 0) {
        if (p->bytes != NULL)
            free(p->bytes);
        p->bytes = NULL;
        return VX_LOAD_OK;
    }
    b = malloc((size_t)p->nbytes);
    if (b == NULL)
        return VX_LOAD_NOMEM;
    for (i = 0; i < p->nbytes; i++)
        b[i] = p->bytes[i];
    if (p->bytes != NULL)
        free(p->bytes);
    p->bytes = b;
    return VX_LOAD_OK;
}

static void prog_clear(vx_program *p)
{
    p->nfns = 0;
    p->entry = 0;
    p->fns = NULL;
    p->args = NULL;
    p->nargs = 0;
    p->bytes = NULL;
    p->nbytes = 0;
}

static int load_all(vx_ld *r, vx_program *p)
{
    uint32_t f;
    int rc;
    if (r->len > VX_MAX_INPUT)
        return VX_LOAD_LIMIT;
    rc = load_header(r, p);
    if (rc != VX_LOAD_OK)
        return rc;
    for (f = 0; f < p->nfns; f++) {
        rc = load_fn(r, p, f);
        if (rc != VX_LOAD_OK)
            return rc;
    }
    if (r->pos != r->len)
        return VX_LOAD_TRAILING;
    rc = check_calls(p);
    if (rc != VX_LOAD_OK)
        return rc;
    rc = trim_args(p);
    if (rc != VX_LOAD_OK)
        return rc;
    return trim_bytes(p);
}

int vx_load(const uint8_t *buf, size_t len, vx_program *out)
{
    vx_ld r;
    int rc;
    r.buf = buf;
    r.len = len;
    r.pos = 0;
    r.acap = 0;
    r.bcap = 0;
    prog_clear(out);
    rc = load_all(&r, out);
    if (rc != VX_LOAD_OK)
        vx_free_program(out);
    return rc;
}

void vx_free_program(vx_program *p)
{
    uint32_t i;
    if (p->fns != NULL) {
        for (i = 0; i < p->nfns; i++) {
            if (p->fns[i].nodes != NULL)
                free(p->fns[i].nodes);
        }
        free(p->fns);
    }
    if (p->args != NULL)
        free(p->args);
    if (p->bytes != NULL)
        free(p->bytes);
    prog_clear(p);
}
