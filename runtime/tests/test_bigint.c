/*
 * test_bigint.c -- bigint.c against Python's unbounded ints: the vectors of
 * scripts/gen-bigint-vectors.py (a file given as the argument), and the
 * representation of every result: INT exactly when the int fits in 64 bits,
 * else a BIG object of its sign and its magnitude's words, the last nonzero.
 */
#define _POSIX_C_SOURCE 200809L   /* getline */
#include "testlib.h"

#define MAXW 2048

typedef struct {
    int      neg;
    size_t   n;            /* magnitude words */
    uint64_t w[MAXW];
} tnum;

static int hexval(char c)
{
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

/* A number written [-]hex. */
static int parse(const char *s, tnum *x)
{
    size_t len, k;
    memset(x, 0, sizeof *x);
    if (*s == '-') {
        x->neg = 1;
        s++;
    }
    len = strlen(s);
    if (len == 0 || (len + 15) / 16 > MAXW)
        return 0;
    for (k = 0; k < len; k++) {
        int d = hexval(s[len - 1 - k]);
        if (d < 0)
            return 0;
        x->w[k / 16] |= (uint64_t)d << (4 * (k % 16));
    }
    x->n = (len + 15) / 16;
    while (x->n > 0 && x->w[x->n - 1] == 0)
        x->n--;
    if (x->n == 0)
        x->neg = 0;
    return 1;
}

static int fits(const tnum *x)
{
    return x->n == 0 || (x->n == 1 && x->w[0] <= (uint64_t)INT64_MAX + (x->neg ? 1 : 0));
}

/* The value of x, built cell by cell (not with bigint.c). */
static vx_val mk(vx_heap *h, const tnum *x)
{
    vx_val v;
    size_t o, k;
    if (fits(x)) {
        v.tag = VX_T_INT;
        v.bits = x->n == 0 ? 0 : x->neg ? (uint64_t)0 - x->w[0] : x->w[0];
        return v;
    }
    if (vx_heap_alloc(h, 1 + x->n, &o) != VX_OK)
        abort();
    vx_obj_elems(h, o)[0] = (vx_val){ VX_T_INT, (uint64_t)x->neg };
    for (k = 0; k < x->n; k++)
        vx_obj_elems(h, o)[1 + k] = (vx_val){ VX_T_INT, x->w[k] };
    v.tag = VX_T_BIG;
    v.bits = o;
    return v;
}

/* Whether v is the representation of x. */
static int is(const vx_heap *h, const vx_val *v, const tnum *x)
{
    size_t k;
    const vx_val *e;
    if (fits(x))
        return v->tag == VX_T_INT && v->bits == (x->n == 0 ? 0 : x->neg ? (uint64_t)0 - x->w[0] : x->w[0]);
    if (v->tag != VX_T_BIG || vx_obj_len(h, (size_t)v->bits) != 1 + x->n)
        return 0;
    e = vx_obj_elems(h, (size_t)v->bits);
    if (e[0].tag != VX_T_INT || e[0].bits != (uint64_t)x->neg)
        return 0;
    for (k = 0; k < x->n; k++)
        if (e[1 + k].tag != VX_T_INT || e[1 + k].bits != x->w[k])
            return 0;
    return 1;
}

static uint32_t opcode(const char *name)
{
    static const char *const names[] = { "add", "sub", "mul", "neg", "abs", "floordiv",
                                         "ceildiv", "quotient", "modulo" };
    static const uint32_t codes[] = { VX_P_ADD, VX_P_SUB, VX_P_MUL, VX_P_NEG, VX_P_ABS,
                                      VX_P_FLOORDIV, VX_P_CEILDIV, VX_P_QUOTIENT, VX_P_MODULO };
    size_t k;
    for (k = 0; k < sizeof codes / sizeof codes[0]; k++)
        if (strcmp(name, names[k]) == 0)
            return codes[k];
    return UINT32_MAX;
}

static tnum A, Bn, C, D, R, S;

static void fail_line(int line, const char *what)
{
    t_failures++;
    fprintf(stderr, "vector line %d: %s\n", line, what);
}

/* Hand cases: the representation at the 64-bit edges, and the size limit. */
static void hand_cases(void)
{
    vx_heap h;
    vx_val a, b, r;
    uint64_t w[2] = { 0, 1 };
    CHECK(vx_heap_init(&h, 1 << 20) == VX_OK);
    /* INT64_MAX + 1 is BIG, INT64_MIN - 0 is INT, -(INT64_MIN) is BIG */
    a = (vx_val){ VX_T_INT, (uint64_t)INT64_MAX };
    b = (vx_val){ VX_T_INT, 1 };
    CHECK(vx_big_op(&h, VX_P_ADD, &a, &b, &r) == VX_OK && r.tag == VX_T_BIG);
    CHECK(vx_big_cmp(&h, &r, &a) == 1 && vx_big_cmp(&h, &a, &r) == -1);
    CHECK(vx_big_op(&h, VX_P_SUB, &r, &b, &r) == VX_OK && r.tag == VX_T_INT && r.bits == (uint64_t)INT64_MAX);
    a = (vx_val){ VX_T_INT, (uint64_t)INT64_MIN };
    CHECK(vx_big_op(&h, VX_P_NEG, &a, &a, &r) == VX_OK && r.tag == VX_T_BIG);
    CHECK(vx_big_op(&h, VX_P_NEG, &r, &r, &r) == VX_OK && r.tag == VX_T_INT && r.bits == (uint64_t)INT64_MIN);
    /* a zero divisor fails, also for a BIG dividend */
    CHECK(vx_big_words(&h, 1, w, 2, &a) == VX_OK && a.tag == VX_T_BIG);
    b = (vx_val){ VX_T_INT, 0 };
    CHECK(vx_big_op(&h, VX_P_MODULO, &a, &b, &r) == VX_FAIL);
    CHECK(vx_big_op(&h, VX_P_FLOORDIV, &a, &b, &r) == VX_FAIL);
    /* words with zero high words normalise; zero has no sign */
    w[1] = 0;
    CHECK(vx_big_words(&h, 1, w, 2, &r) == VX_OK && r.tag == VX_T_INT && r.bits == 0);
    /* the length limit (IntBits.max): a magnitude of 2^20 bits is an int, one
       more bit the overflow error */
    {
        uint64_t *big = calloc(VX_BIG_MAX_WORDS + 1, sizeof(uint64_t));
        vx_val two = { VX_T_INT, 2 }, one = { VX_T_INT, 1 }, m;
        big[VX_BIG_MAX_WORDS - 1] = UINT64_C(1) << 63;          /* 2^(2^20 - 1) */
        CHECK(vx_big_words(&h, 0, big, VX_BIG_MAX_WORDS, &a) == VX_OK);
        CHECK(vx_big_op(&h, VX_P_MUL, &a, &two, &r) == VX_OVERFLOW);
        CHECK(vx_big_op(&h, VX_P_MUL, &a, &one, &r) == VX_OK);
        CHECK(vx_big_op(&h, VX_P_ADD, &a, &a, &r) == VX_OVERFLOW);
        CHECK(vx_big_op(&h, VX_P_SUB, &a, &a, &r) == VX_OK && r.tag == VX_T_INT && r.bits == 0);
        memset(big, 0xff, VX_BIG_MAX_WORDS * sizeof(uint64_t));  /* 2^(2^20) - 1 */
        CHECK(vx_big_words(&h, 1, big, VX_BIG_MAX_WORDS, &m) == VX_OK);
        CHECK(vx_big_op(&h, VX_P_SUB, &m, &one, &r) == VX_OVERFLOW);
        CHECK(vx_big_op(&h, VX_P_ADD, &m, &one, &r) == VX_OK);
        CHECK(vx_big_op(&h, VX_P_MUL, &a, &a, &r) == VX_OVERFLOW);
        big[VX_BIG_MAX_WORDS] = 1;
        CHECK(vx_big_words(&h, 0, big, VX_BIG_MAX_WORDS + 1, &r) == VX_OVERFLOW);
        free(big);
    }
    vx_heap_free(&h);
}

int main(int argc, char **argv)
{
    FILE *f;
    char *line = NULL;
    size_t cap = 0;
    int lineno = 0, cases = 0;
    hand_cases();
    if (argc < 2 || (f = fopen(argv[1], "r")) == NULL) {
        fprintf(stderr, "test_bigint: no vector file (scripts/gen-bigint-vectors.py)\n");
        return 1;
    }
    for (;;) {
        char kind[8], name[16], t1[4096], t2[4096], t3[4096], t4[4096], rc[16], t5[4096], t6[4096];
        vx_heap h;
        vx_val a, b, r, in[4], parts[2];
        ssize_t got = getline(&line, &cap, f);
        if (got < 0)
            break;
        lineno++;
        if (vx_heap_init(&h, (size_t)1 << 22) != VX_OK)
            abort();
        if (sscanf(line, "%7s", kind) != 1) {
            fail_line(lineno, "unreadable");
        } else if (strcmp(kind, "op") == 0) {
            uint32_t op;
            int e;
            if (sscanf(line, "op %15s %4095s %4095s %15s %4095s", name, t1, t2, rc, t3) != 5 ||
                (op = opcode(name)) == UINT32_MAX || !parse(t1, &A) || !parse(t2, &Bn) || !parse(t3, &R)) {
                fail_line(lineno, "unreadable op");
            } else {
                a = mk(&h, &A);
                b = mk(&h, &Bn);
                e = vx_big_op(&h, op, &a, &b, &r);
                t_checks++;
                if (strcmp(rc, "fail") == 0 ? e != VX_FAIL : (e != VX_OK || !is(&h, &r, &R)))
                    fail_line(lineno, "op: wrong result");
            }
        } else if (strcmp(kind, "cmp") == 0) {
            int want;
            if (sscanf(line, "cmp %4095s %4095s %d", t1, t2, &want) != 3 || !parse(t1, &A) || !parse(t2, &Bn)) {
                fail_line(lineno, "unreadable cmp");
            } else {
                a = mk(&h, &A);
                b = mk(&h, &Bn);
                t_checks++;
                if (vx_big_cmp(&h, &a, &b) != want)
                    fail_line(lineno, "cmp: wrong result");
            }
        } else if (strcmp(kind, "dbl") == 0 || strcmp(kind, "low") == 0) {
            unsigned long long want;
            if (sscanf(line, "%*s %4095s %llx", t1, &want) != 2 || !parse(t1, &A)) {
                fail_line(lineno, "unreadable dbl/low");
            } else {
                uint64_t got;
                a = mk(&h, &A);
                if (kind[0] == 'd') {
                    double d = vx_big_double(&h, &a);
                    memcpy(&got, &d, sizeof got);
                } else {
                    got = vx_big_low64(&h, &a);
                }
                t_checks++;
                if (got != (uint64_t)want)
                    fail_line(lineno, kind[0] == 'd' ? "dbl: wrong double" : "low: wrong bits");
            }
        } else if (strcmp(kind, "rat") == 0) {
            uint32_t op;
            int e;
            if (sscanf(line, "rat %15s %4095s %4095s %4095s %4095s %15s %4095s %4095s", name, t1, t2, t3, t4,
                       rc, t5, t6) != 8 ||
                (op = opcode(name)) == UINT32_MAX || !parse(t1, &A) || !parse(t2, &Bn) || !parse(t3, &C) ||
                !parse(t4, &D) || !parse(t5, &R) || !parse(t6, &S)) {
                fail_line(lineno, "unreadable rat");
            } else {
                in[0] = mk(&h, &A);
                in[1] = mk(&h, &Bn);
                in[2] = mk(&h, &C);
                in[3] = mk(&h, &D);
                e = vx_big_rational(&h, op, in, parts);
                t_checks++;
                if (strcmp(rc, "ok") == 0 ? e != VX_OK || !is(&h, &parts[0], &R) || !is(&h, &parts[1], &S)
                    : e != (strcmp(rc, "fail") == 0 ? VX_FAIL : VX_OVERFLOW))
                    fail_line(lineno, "rat: wrong result");
            }
        } else {
            fail_line(lineno, "unknown kind");
        }
        vx_heap_free(&h);
        cases++;
    }
    free(line);
    fclose(f);
    if (cases < 1000) {
        fprintf(stderr, "test_bigint: only %d vectors\n", cases);
        return 1;
    }
    printf("test_bigint: %d vectors\n", cases);
    return t_report("test_bigint");
}
