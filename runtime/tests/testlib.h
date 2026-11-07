/*
 * testlib.h -- CHECK macros, file reading and a small OVBC assembler for the
 * unit tests (header-only; each test is one translation unit).
 */
#ifndef VX_TESTLIB_H
#define VX_TESTLIB_H

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "vx_runtime.h"

static int t_checks, t_failures;

#define CHECK(c)                                                              \
    do {                                                                      \
        t_checks++;                                                           \
        if (!(c)) {                                                           \
            t_failures++;                                                     \
            fprintf(stderr, "%s:%d: CHECK failed: %s\n", __FILE__, __LINE__, #c); \
        }                                                                     \
    } while (0)

#define CHECK_EQ(a, b)                                                        \
    do {                                                                      \
        long long a_ = (long long)(a), b_ = (long long)(b);                   \
        t_checks++;                                                           \
        if (a_ != b_) {                                                       \
            t_failures++;                                                     \
            fprintf(stderr, "%s:%d: CHECK_EQ failed: %s = %lld, %s = %lld\n", \
                    __FILE__, __LINE__, #a, a_, #b, b_);                      \
        }                                                                     \
    } while (0)

static inline int t_report(const char *name)
{
    printf("%s: %d checks, %d failed\n", name, t_checks, t_failures);
    return t_failures ? 1 : 0;
}

static inline uint8_t *t_read_file(const char *path, size_t *len)
{
    FILE *f = fopen(path, "rb");
    uint8_t *b;
    long n;
    if (f == NULL)
        return NULL;
    fseek(f, 0, SEEK_END);
    n = ftell(f);
    fseek(f, 0, SEEK_SET);
    b = malloc(n > 0 ? (size_t)n : 1);
    if (b == NULL || fread(b, 1, (size_t)n, f) != (size_t)n) {
        free(b);
        fclose(f);
        return NULL;
    }
    fclose(f);
    *len = (size_t)n;
    return b;
}

/* ------------------------------------------------------------ assembler */

typedef struct {
    uint8_t *b;
    size_t   n, cap;
} tbuf;

static inline void tb_byte(tbuf *t, uint8_t x)
{
    if (t->n == t->cap) {
        t->cap = t->cap ? 2 * t->cap : 256;
        t->b = realloc(t->b, t->cap);
        if (t->b == NULL)
            abort();
    }
    t->b[t->n++] = x;
}
static inline void tb_u8(tbuf *t, uint32_t x) { tb_byte(t, (uint8_t)x); }
static inline void tb_u32(tbuf *t, uint32_t x)
{
    int k;
    for (k = 0; k < 4; k++)
        tb_byte(t, (uint8_t)(x >> (8 * k)));
}
static inline void tb_i64(tbuf *t, int64_t i)
{
    uint64_t u = (uint64_t)i;
    int k;
    for (k = 0; k < 8; k++)
        tb_byte(t, (uint8_t)(u >> (8 * k)));
}
static inline void tb_append(tbuf *t, const uint8_t *p, size_t n)
{
    size_t k;
    for (k = 0; k < n; k++)
        tb_byte(t, p[k]);
}

/* A function under construction: its nodes, numbered in emission order. */
typedef struct {
    tbuf     nodes;
    uint32_t count;
} tfn;

static inline uint32_t tn_begin(tfn *f, uint32_t tag)
{
    tb_u8(&f->nodes, tag);
    return f->count++;
}
static inline uint32_t n_int(tfn *f, int64_t v)
{
    uint32_t i = tn_begin(f, VX_N_LIT);
    tb_u8(&f->nodes, VX_LIT_INT);
    tb_i64(&f->nodes, v);
    return i;
}
static inline uint32_t n_logic(tfn *f, int b)
{
    uint32_t i = tn_begin(f, VX_N_LIT);
    tb_u8(&f->nodes, VX_LIT_LOGIC);
    tb_u8(&f->nodes, (uint32_t)b);
    return i;
}
static inline uint32_t n_char(tfn *f, uint8_t c)
{
    uint32_t i = tn_begin(f, VX_N_LIT);
    tb_u8(&f->nodes, VX_LIT_CHAR);
    tb_u8(&f->nodes, c);
    return i;
}
static inline uint32_t n_str(tfn *f, const char *s)
{
    uint32_t i = tn_begin(f, VX_N_LIT);
    tb_u8(&f->nodes, VX_LIT_STR);
    tb_u32(&f->nodes, (uint32_t)strlen(s));
    tb_append(&f->nodes, (const uint8_t *)s, strlen(s));
    return i;
}
static inline uint32_t n_none(tfn *f)
{
    uint32_t i = tn_begin(f, VX_N_LIT);
    tb_u8(&f->nodes, VX_LIT_NONE);
    return i;
}
static inline uint32_t n_void(tfn *f)
{
    uint32_t i = tn_begin(f, VX_N_LIT);
    tb_u8(&f->nodes, VX_LIT_VOID);
    return i;
}
static inline uint32_t n_local(tfn *f, uint32_t slot)
{
    uint32_t i = tn_begin(f, VX_N_LOCAL);
    tb_u32(&f->nodes, slot);
    return i;
}
static inline uint32_t n_assign(tfn *f, uint32_t slot, uint32_t e)
{
    uint32_t i = tn_begin(f, VX_N_ASSIGN);
    tb_u32(&f->nodes, slot);
    tb_u32(&f->nodes, e);
    return i;
}
static inline uint32_t n_seq(tfn *f, uint32_t a, uint32_t b)
{
    uint32_t i = tn_begin(f, VX_N_SEQ);
    tb_u32(&f->nodes, a);
    tb_u32(&f->nodes, b);
    return i;
}
/* n_prim(f, code, k, n, arg0, ..., argn-1) */
static inline uint32_t n_prim(tfn *f, uint32_t code, uint32_t k, uint32_t n, ...)
{
    uint32_t i = tn_begin(f, VX_N_PRIM), j;
    va_list ap;
    tb_u8(&f->nodes, code);
    tb_u32(&f->nodes, k);
    tb_u32(&f->nodes, n);
    va_start(ap, n);
    for (j = 0; j < n; j++)
        tb_u32(&f->nodes, va_arg(ap, uint32_t));
    va_end(ap);
    return i;
}
static inline uint32_t n_ref(tfn *f, uint32_t a)
{
    uint32_t i = tn_begin(f, VX_N_LIT);
    tb_u8(&f->nodes, VX_LIT_REF);
    tb_u32(&f->nodes, a);
    return i;
}
/* n_heap(f, op, k, n, arg0, ..., argn-1), for every op but ISTAG */
static inline uint32_t n_heap(tfn *f, uint32_t op, uint32_t k, uint32_t n, ...)
{
    uint32_t i = tn_begin(f, VX_N_HEAP), j;
    va_list ap;
    tb_u8(&f->nodes, op);
    tb_u32(&f->nodes, k);
    tb_u32(&f->nodes, n);
    va_start(ap, n);
    for (j = 0; j < n; j++)
        tb_u32(&f->nodes, va_arg(ap, uint32_t));
    va_end(ap);
    return i;
}
/* isTag us [e], with us = tags[0..m) */
static inline uint32_t n_istag(tfn *f, uint32_t m, const uint32_t *tags, uint32_t e)
{
    uint32_t i = tn_begin(f, VX_N_HEAP), j;
    tb_u8(&f->nodes, VX_H_ISTAG);
    tb_u32(&f->nodes, m);
    for (j = 0; j < m; j++)
        tb_u32(&f->nodes, tags[j]);
    tb_u32(&f->nodes, 1);
    tb_u32(&f->nodes, e);
    return i;
}
static inline uint32_t n_call(tfn *f, uint32_t fn, uint32_t n, ...)
{
    uint32_t i = tn_begin(f, VX_N_CALL), j;
    va_list ap;
    tb_u32(&f->nodes, fn);
    tb_u32(&f->nodes, n);
    va_start(ap, n);
    for (j = 0; j < n; j++)
        tb_u32(&f->nodes, va_arg(ap, uint32_t));
    va_end(ap);
    return i;
}
static inline uint32_t n_ite(tfn *f, uint32_t c, uint32_t t, uint32_t e)
{
    uint32_t i = tn_begin(f, VX_N_ITE);
    tb_u32(&f->nodes, c);
    tb_u32(&f->nodes, t);
    tb_u32(&f->nodes, e);
    return i;
}
static inline uint32_t n_for(tfn *f, uint32_t slot, uint32_t it, uint32_t filt, uint32_t body)
{
    uint32_t i = tn_begin(f, VX_N_FOR);
    tb_u32(&f->nodes, slot);
    tb_u32(&f->nodes, it);
    tb_u32(&f->nodes, filt);
    tb_u32(&f->nodes, body);
    return i;
}
static inline uint32_t n_one(tfn *f, uint32_t tag, uint32_t e)
{
    uint32_t i = tn_begin(f, tag);
    tb_u32(&f->nodes, e);
    return i;
}
static inline uint32_t n_loop(tfn *f, uint32_t b) { return n_one(f, VX_N_LOOP, b); }
static inline uint32_t n_ret(tfn *f, uint32_t e) { return n_one(f, VX_N_RET, e); }
static inline uint32_t n_print(tfn *f, uint32_t e) { return n_one(f, VX_N_PRINT, e); }
static inline uint32_t n_brk(tfn *f) { return tn_begin(f, VX_N_BRK); }

/* Print(ToString(e)) */
static inline uint32_t n_print_int(tfn *f, uint32_t e)
{
    return n_print(f, n_prim(f, VX_P_TOSTR, 0, 1, e));
}

static inline void t_prog_header(tbuf *p, uint32_t nfns, uint32_t main_fn)
{
    tb_append(p, (const uint8_t *)"OVBC", 4);
    tb_u32(p, 1);
    tb_u32(p, nfns);
    tb_u32(p, main_fn);
}

/* Append function f (and free its node buffer). */
static inline void t_fn(tbuf *p, tfn *f, uint32_t arity, uint32_t nslots, const char *name, uint32_t root)
{
    tb_u32(p, arity);
    tb_u32(p, nslots);
    tb_u8(p, 0);
    tb_u32(p, (uint32_t)strlen(name));
    tb_append(p, (const uint8_t *)name, strlen(name));
    tb_u32(p, f->count);
    tb_append(p, f->nodes.b, f->nodes.n);
    tb_u32(p, root);
    free(f->nodes.b);
    memset(f, 0, sizeof *f);
}

#endif /* VX_TESTLIB_H */
