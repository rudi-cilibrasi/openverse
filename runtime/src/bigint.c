/*
 * bigint.c -- ints beyond 64 bits: the slow path of the int operations of
 * Prim.apply (OpenVerse/Core/Prims.lean), whose ints are Lean's Int, as
 * long as the Verse VM's (Book of Verse ch. 2, "Integers"; issue #724).
 *
 * Representation (vx_runtime.h).  An int in [INT64_MIN, INT64_MAX] is always
 * (INT, bits), the fast path of arith.c; any other is (BIG, o): heap object o
 * of 1 + n cells, cell 0 (INT, sign: 0 positive, 1 negative) and cells 1..n
 * (INT, word), the magnitude's 64-bit words, least significant first, the
 * last nonzero.  Each int has one representation, so vx_equal (structural
 * equality) is equality of ints, and the value heap's reclamation keeps a BIG
 * object as it keeps an array (its cells are no references).
 *
 * Arithmetic works on copies: an operand's magnitude is unpacked into 32-bit
 * limbs (malloc'd), the result is computed there and packed into a new heap
 * object.  Heap cells move when the heap grows, so no pointer into the heap
 * is kept across an allocation.  Multiplication is schoolbook, division
 * Knuth's algorithm D (TAOCP vol. 2, 4.3.1, as in Hacker's Delight's
 * divmnu), all in unsigned arithmetic, so nothing here is undefined or
 * implementation-defined behaviour.  Operands have at most VX_BIG_MAX_WORDS
 * words, so no intermediate result has more than four times as many.
 *
 * Ints are as long as the Verse VM's: a result whose magnitude has more than
 * 2^20 bits (VX_BIG_MAX_WORDS words) is the overflow error, as Res.ofInt
 * says (IntBits.max of OpenVerse/Core/Value.lean).
 *
 * Not proved: tested against Python's ints (runtime/tests/test_bigint.c,
 * scripts/fuzz-bigint.sh) and against the Lean interpreter.
 */
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include "vx_runtime.h"

/* A number being computed: sign and magnitude. */
typedef struct {
    uint32_t *d;    /* limbs, least significant first */
    size_t    n;    /* limbs in use: d[n - 1] != 0, or n == 0 for zero */
    int       neg;  /* 1 for a negative number, never for zero */
} bn;

#define BN0 { NULL, 0, 0 }

static void bn_free(bn *x)
{
    free(x->d);
    x->d = NULL;
    x->n = 0;
    x->neg = 0;
}

/* Room for `cap` limbs (at least one), the number zero. */
static int bn_room(bn *x, size_t cap)
{
    free(x->d);
    x->d = calloc(cap ? cap : 1, sizeof(uint32_t));
    x->n = 0;
    x->neg = 0;
    return x->d != NULL;
}

static void bn_trim(bn *x)
{
    while (x->n > 0 && x->d[x->n - 1] == 0)
        x->n--;
    if (x->n == 0)
        x->neg = 0;
}

/* ------------------------------------------------------- vx_val <-> bn */

/* The magnitude words of an int value (n words at *w, 0 for zero) and its
   sign.  An INT's one word is in *tmp. */
static const vx_val *big_words(const vx_heap *h, const vx_val *v, uint64_t *tmp, size_t *n, int *neg)
{
    if (v->tag == VX_T_INT) {
        int64_t i = vx_int_of(v->bits);
        *neg = i < 0;
        *tmp = i < 0 ? (uint64_t)0 - v->bits : v->bits;
        *n = *tmp != 0;
        return NULL;
    }
    *neg = vx_obj_elems(h, (size_t)v->bits)[0].bits != 0;
    *n = vx_obj_len(h, (size_t)v->bits) - 1;
    return vx_obj_elems(h, (size_t)v->bits) + 1;
}

static int bn_of(const vx_heap *h, const vx_val *v, bn *x)
{
    uint64_t one = 0;
    size_t n, k;
    int neg;
    const vx_val *w = big_words(h, v, &one, &n, &neg);
    if (!bn_room(x, 2 * n))
        return 0;
    for (k = 0; k < n; k++) {
        uint64_t u = w != NULL ? w[k].bits : one;
        x->d[2 * k] = (uint32_t)u;
        x->d[2 * k + 1] = (uint32_t)(u >> 32);
    }
    x->n = 2 * n;
    x->neg = neg;
    bn_trim(x);
    return 1;
}

/* The int ±Σ w[k]·2^(64k) as a value: INT when it fits, else a new BIG. */
int vx_big_words(vx_heap *h, int neg, const uint64_t *w, size_t n, vx_val *r)
{
    size_t o, k;
    vx_val *e;
    while (n > 0 && w[n - 1] == 0)
        n--;
    if (n == 0) {
        r->tag = VX_T_INT;
        r->bits = 0;
        return VX_OK;
    }
    if (n == 1 && (neg ? w[0] <= (uint64_t)INT64_MAX + 1 : w[0] <= (uint64_t)INT64_MAX)) {
        r->tag = VX_T_INT;
        r->bits = neg ? (uint64_t)0 - w[0] : w[0];
        return VX_OK;
    }
    if (n > VX_BIG_MAX_WORDS)
        return VX_OVERFLOW;
    if (vx_heap_alloc(h, 1 + n, &o) != VX_OK)
        return VX_EFULL;
    e = vx_obj_elems(h, o);
    e[0].tag = VX_T_INT;
    e[0].bits = neg ? 1 : 0;
    for (k = 0; k < n; k++) {
        e[1 + k].tag = VX_T_INT;
        e[1 + k].bits = w[k];
    }
    r->tag = VX_T_BIG;
    r->bits = o;
    return VX_OK;
}

static int bn_to(vx_heap *h, const bn *x, vx_val *r)
{
    size_t nw = (x->n + 1) / 2, k;
    uint64_t *w;
    int rc;
    if (nw > VX_BIG_MAX_WORDS)
        return VX_OVERFLOW;
    w = malloc((nw ? nw : 1) * sizeof(uint64_t));
    if (w == NULL)
        return VX_EFULL;
    for (k = 0; k < nw; k++) {
        uint64_t lo = x->d[2 * k];
        uint64_t hi = 2 * k + 1 < x->n ? x->d[2 * k + 1] : 0;
        w[k] = lo | hi << 32;
    }
    rc = vx_big_words(h, x->neg, w, nw, r);
    free(w);
    return rc;
}

/* ------------------------------------------------------------ magnitudes */

static int mag_cmp(const bn *a, const bn *b)
{
    size_t k;
    if (a->n != b->n)
        return a->n < b->n ? -1 : 1;
    for (k = a->n; k-- > 0;)
        if (a->d[k] != b->d[k])
            return a->d[k] < b->d[k] ? -1 : 1;
    return 0;
}

/* r = |a| + |b| (r not a or b). */
static int mag_add(const bn *a, const bn *b, bn *r)
{
    size_t n = a->n > b->n ? a->n : b->n, k;
    uint64_t carry = 0;
    if (!bn_room(r, n + 1))
        return 0;
    for (k = 0; k < n; k++) {
        uint64_t s = carry + (k < a->n ? a->d[k] : 0) + (k < b->n ? b->d[k] : 0);
        r->d[k] = (uint32_t)s;
        carry = s >> 32;
    }
    r->d[n] = (uint32_t)carry;
    r->n = n + 1;
    bn_trim(r);
    return 1;
}

/* r = |a| - |b|, for |a| >= |b| (r not a or b). */
static int mag_sub(const bn *a, const bn *b, bn *r)
{
    size_t k;
    uint32_t borrow = 0;
    if (!bn_room(r, a->n))
        return 0;
    for (k = 0; k < a->n; k++) {
        uint32_t x = a->d[k], y = k < b->n ? b->d[k] : 0;
        r->d[k] = x - y - borrow;
        borrow = x < y || x - y < borrow;
    }
    r->n = a->n;
    bn_trim(r);
    return 1;
}

/* r = |a| * |b|, schoolbook (r not a or b). */
static int mag_mul(const bn *a, const bn *b, bn *r)
{
    size_t i, j;
    if (a->n == 0 || b->n == 0)
        return bn_room(r, 1);
    if (!bn_room(r, a->n + b->n))
        return 0;
    for (i = 0; i < a->n; i++) {
        uint64_t carry = 0;
        for (j = 0; j < b->n; j++) {
            uint64_t t = (uint64_t)a->d[i] * b->d[j] + r->d[i + j] + carry;
            r->d[i + j] = (uint32_t)t;
            carry = t >> 32;
        }
        r->d[i + b->n] = (uint32_t)carry;
    }
    r->n = a->n + b->n;
    bn_trim(r);
    return 1;
}

static int leading_zeros(uint32_t x)
{
    int s = 0;
    while (!(x & 0x80000000u)) {
        x <<= 1;
        s++;
    }
    return s;
}

/* q = |u| / |v|, r = |u| mod |v|, for v != 0 (q, r not u or v). */
static int mag_divmod(const bn *u, const bn *v, bn *q, bn *r)
{
    size_t m, n = v->n, i, j;
    uint32_t *un, *vn;
    int s;
    if (mag_cmp(u, v) < 0) {
        if (!bn_room(q, 1) || !bn_room(r, u->n))
            return 0;
        memcpy(r->d, u->d, u->n * sizeof(uint32_t));
        r->n = u->n;
        return 1;
    }
    m = u->n - n;
    if (!bn_room(q, m + 1) || !bn_room(r, n))
        return 0;
    if (n == 1) {
        uint64_t rem = 0;
        for (j = u->n; j-- > 0;) {
            uint64_t cur = rem << 32 | u->d[j];
            q->d[j] = (uint32_t)(cur / v->d[0]);
            rem = cur % v->d[0];
        }
        q->n = m + 1;
        r->d[0] = (uint32_t)rem;
        r->n = 1;
        bn_trim(q);
        bn_trim(r);
        return 1;
    }
    /* normalize: shift so that the divisor's top limb has its high bit set */
    s = leading_zeros(v->d[n - 1]);
    un = malloc((u->n + 1) * sizeof(uint32_t));
    vn = malloc(n * sizeof(uint32_t));
    if (un == NULL || vn == NULL) {
        free(un);
        free(vn);
        return 0;
    }
    for (i = n - 1; i > 0; i--)
        vn[i] = s ? v->d[i] << s | v->d[i - 1] >> (32 - s) : v->d[i];
    vn[0] = v->d[0] << s;
    un[u->n] = s ? u->d[u->n - 1] >> (32 - s) : 0;
    for (i = u->n - 1; i > 0; i--)
        un[i] = s ? u->d[i] << s | u->d[i - 1] >> (32 - s) : u->d[i];
    un[0] = u->d[0] << s;
    for (j = m + 1; j-- > 0;) {
        /* estimate the quotient digit from the top two limbs */
        uint64_t num = (uint64_t)un[j + n] << 32 | un[j + n - 1];
        uint64_t qhat = num / vn[n - 1], rhat = num % vn[n - 1];
        uint64_t carry = 0;
        uint32_t borrow = 0, top;
        while (qhat >> 32 != 0 || qhat * vn[n - 2] > (rhat << 32 | un[j + n - 2])) {
            qhat--;
            rhat += vn[n - 1];
            if (rhat >> 32 != 0)
                break;
        }
        /* un[j .. j + n] -= qhat * vn */
        for (i = 0; i < n; i++) {
            uint64_t p = qhat * vn[i] + carry;
            uint32_t lo = (uint32_t)p, x = un[i + j];
            carry = p >> 32;
            un[i + j] = x - lo - borrow;
            borrow = x < lo || x - lo < borrow;
        }
        top = un[j + n];
        un[j + n] = (uint32_t)(top - carry - borrow);
        if ((uint64_t)top < carry + borrow) {
            /* qhat was one too large: add the divisor back */
            uint64_t c2 = 0;
            qhat--;
            for (i = 0; i < n; i++) {
                uint64_t t = (uint64_t)un[i + j] + vn[i] + c2;
                un[i + j] = (uint32_t)t;
                c2 = t >> 32;
            }
            un[j + n] = (uint32_t)(un[j + n] + c2);
        }
        q->d[j] = (uint32_t)qhat;
    }
    q->n = m + 1;
    /* the remainder, unnormalized */
    for (i = 0; i < n; i++)
        r->d[i] = s ? un[i] >> s | un[i + 1] << (32 - s) : un[i];
    r->n = n;
    free(un);
    free(vn);
    bn_trim(q);
    bn_trim(r);
    return 1;
}

/* ---------------------------------------------------- signed arithmetic */

/* r = a + b, with b's sign flipped when `negb` (r not a or b). */
static int bn_addsub(const bn *a, const bn *b, int negb, bn *r)
{
    int bneg = b->n != 0 && (b->neg ^ negb);
    if (a->neg == bneg) {
        if (!mag_add(a, b, r))
            return 0;
        r->neg = r->n != 0 && a->neg;
        return 1;
    }
    if (mag_cmp(a, b) >= 0) {
        if (!mag_sub(a, b, r))
            return 0;
        r->neg = r->n != 0 && a->neg;
    } else {
        if (!mag_sub(b, a, r))
            return 0;
        r->neg = r->n != 0 && bneg;
    }
    return 1;
}

/* x += d, for d in {-1, 1} (in place). */
static int bn_step(bn *x, int d)
{
    uint32_t one = 1;
    bn u = { &one, 1, d < 0 }, r = BN0;
    if (!bn_addsub(x, &u, 0, &r))
        return 0;
    bn_free(x);
    *x = r;
    return 1;
}

/* The division operations (`op` a VX_P_ division code) of a by b != 0, on
   the truncated quotient q and remainder r (C99's / and %), as arith.c
   adjusts them: floor, ceiling, Euclidean quotient, Euclidean modulo. */
static int bn_div(uint32_t op, const bn *a, const bn *b, bn *out)
{
    bn q = BN0, r = BN0;
    int ok = mag_divmod(a, b, &q, &r);
    if (!ok)
        goto done;
    q.neg = q.n != 0 && (a->neg ^ b->neg);
    r.neg = r.n != 0 && a->neg;
    if (op == VX_P_MODULO) {
        /* if r < 0 then (b > 0 ? r + b : r - b) else r */
        if (r.neg)
            ok = bn_addsub(&r, b, b->neg, out);
        else {
            *out = r;
            r.d = NULL;
        }
        goto done;
    }
    if (op == VX_P_FLOORDIV && r.n != 0 && r.neg != b->neg)
        ok = bn_step(&q, -1);
    else if (op == VX_P_CEILDIV && r.n != 0 && r.neg == b->neg)
        ok = bn_step(&q, 1);
    else if (op == VX_P_QUOTIENT && r.neg)
        ok = bn_step(&q, b->neg ? 1 : -1);
    *out = q;
    q.d = NULL;
done:
    bn_free(&q);
    bn_free(&r);
    return ok;
}

int vx_big_op(vx_heap *h, uint32_t op, const vx_val *a, const vx_val *b, vx_val *r)
{
    bn x = BN0, y = BN0, z = BN0;
    int ok, rc;
    if (!bn_of(h, a, &x) || ((op != VX_P_NEG && op != VX_P_ABS) && !bn_of(h, b, &y))) {
        bn_free(&x);
        return VX_EFULL;
    }
    switch (op) {
    case VX_P_ADD: ok = bn_addsub(&x, &y, 0, &z); break;
    case VX_P_SUB: ok = bn_addsub(&x, &y, 1, &z); break;
    case VX_P_MUL:
        ok = mag_mul(&x, &y, &z);
        z.neg = z.n != 0 && (x.neg ^ y.neg);
        break;
    case VX_P_NEG:
    case VX_P_ABS:
        z = x;
        x.d = NULL;
        z.neg = op == VX_P_NEG ? z.n != 0 && !z.neg : 0;
        ok = 1;
        break;
    default:
        if (y.n == 0) {
            bn_free(&x);
            bn_free(&y);
            return VX_FAIL;
        }
        ok = bn_div(op, &x, &y, &z);
        break;
    }
    rc = ok ? bn_to(h, &z, r) : VX_EFULL;
    bn_free(&x);
    bn_free(&y);
    bn_free(&z);
    return rc;
}

/* ------------------------------------------------------ comparisons etc. */

int vx_big_cmp(const vx_heap *h, const vx_val *a, const vx_val *b)
{
    uint64_t ta = 0, tb = 0;
    size_t na, nb, k;
    int sa, sb, mag = 0;
    const vx_val *wa, *wb;
    if (a->tag == VX_T_INT && b->tag == VX_T_INT) {
        int64_t x = vx_int_of(a->bits), y = vx_int_of(b->bits);
        return x < y ? -1 : x > y;
    }
    wa = big_words(h, a, &ta, &na, &sa);
    wb = big_words(h, b, &tb, &nb, &sb);
    if (sa != sb)
        return sa ? -1 : 1;
    if (na != nb)
        mag = na < nb ? -1 : 1;
    else
        for (k = na; k-- > 0 && mag == 0;) {
            uint64_t x = wa != NULL ? wa[k].bits : ta, y = wb != NULL ? wb[k].bits : tb;
            if (x != y)
                mag = x < y ? -1 : 1;
        }
    return sa ? -mag : mag;
}

/* Float.ofInt: the double nearest the int, ties to even (IEEE's default
   rounding), an infinity beyond the largest double. */
double vx_big_double(const vx_heap *h, const vx_val *a)
{
    uint64_t one = 0, top, sticky = 0, w;
    size_t n, k, bits;
    int neg, shift;
    double d;
    const vx_val *ws = big_words(h, a, &one, &n, &neg);
    if (ws == NULL)
        return (double)vx_int_of(a->bits);
    /* bits: the magnitude's length; top: its highest 64 bits */
    w = ws[n - 1].bits;
    shift = 64;
    while (shift > 0 && !(w >> (shift - 1) & 1))
        shift--;
    bits = 64 * (n - 1) + (size_t)shift;
    if (bits > 1100)
        return neg ? -HUGE_VAL : HUGE_VAL;
    if (n == 1) {
        top = w;
        bits = 64;
    } else {
        top = shift == 64 ? w : w << (64 - shift) | ws[n - 2].bits >> shift;
        sticky = shift == 64 ? ws[n - 2].bits : ws[n - 2].bits << (64 - shift);
        for (k = 0; k + 2 < n; k++)
            sticky |= ws[k].bits;
    }
    /* the bits below the top 64 only break ties: one sticky bit stands for them */
    d = (double)(top | (sticky != 0));
    d = ldexp(d, (int)bits - 64);
    return neg ? -d : d;
}

/* The low 64 bits of the int's two's complement (fofBits's i mod 2^64). */
uint64_t vx_big_low64(const vx_heap *h, const vx_val *a)
{
    uint64_t one = 0, w;
    size_t n;
    int neg;
    const vx_val *ws = big_words(h, a, &one, &n, &neg);
    w = ws == NULL ? one : ws[0].bits;
    return neg ? (uint64_t)0 - w : w;
}

/* ------------------------------------------------------------- rationals */

/* rationalRes n d of Prims.lean: n/d in lowest terms, the denominator
   positive (n, d consumed). */
static int bn_reduce(vx_heap *h, bn *n, bn *d, vx_val parts[2])
{
    bn x = BN0, y = BN0, q = BN0, rr = BN0;
    int rc = VX_EFULL, neg = n->neg ^ d->neg;
    /* g = gcd(|n|, |d|) by Euclid */
    if (!bn_room(&x, n->n) || !bn_room(&y, d->n))
        goto done;
    memcpy(x.d, n->d, n->n * sizeof(uint32_t));
    x.n = n->n;
    memcpy(y.d, d->d, d->n * sizeof(uint32_t));
    y.n = d->n;
    while (y.n != 0) {
        if (!mag_divmod(&x, &y, &q, &rr))
            goto done;
        bn_free(&x);
        x = y;
        y = rr;
        rr.d = NULL;
        bn_free(&q);
    }
    if (x.n == 0) {           /* 0/0: no rational (checkedRationalRes) */
        rc = VX_OVERFLOW;
        goto done;
    }
    if (!mag_divmod(n, &x, &q, &rr))
        goto done;
    bn_free(n);
    *n = q;
    q.d = NULL;
    if (!mag_divmod(d, &x, &q, &rr))
        goto done;
    bn_free(d);
    *d = q;
    q.d = NULL;
    n->neg = n->n != 0 && neg;
    d->neg = 0;
    rc = bn_to(h, n, &parts[0]);
    if (rc == VX_OK)
        rc = bn_to(h, d, &parts[1]);
done:
    bn_free(&x);
    bn_free(&y);
    bn_free(&q);
    bn_free(&rr);
    return rc;
}

int vx_big_rational(vx_heap *h, uint32_t op, const vx_val *in, vx_val parts[2])
{
    bn a = BN0, b = BN0, p = BN0, q = BN0, s = BN0, t = BN0, n = BN0, d = BN0;
    int rc = VX_EFULL, ok;
    if (!bn_of(h, &in[0], &a) || !bn_of(h, &in[1], &b) || !bn_of(h, &in[2], &p) ||
        !bn_of(h, &in[3], &q))
        goto done;
    /* if b ≤ 0 || d ≤ 0 then .err .overflow */
    if (b.n == 0 || b.neg || q.n == 0 || q.neg) {
        rc = VX_OVERFLOW;
        goto done;
    }
    if (op == VX_P_QUOTIENT && p.n == 0) {
        rc = VX_FAIL;
        goto done;
    }
    switch (op) {
    case VX_P_ADD:   /* a*d + c*b over b*d */
    case VX_P_SUB:
        ok = mag_mul(&a, &q, &s) && mag_mul(&p, &b, &t);
        s.neg = s.n != 0 && a.neg;
        t.neg = t.n != 0 && p.neg;
        ok = ok && bn_addsub(&s, &t, op == VX_P_SUB, &n) && mag_mul(&b, &q, &d);
        break;
    case VX_P_MUL:   /* a*c over b*d */
        ok = mag_mul(&a, &p, &n) && mag_mul(&b, &q, &d);
        n.neg = n.n != 0 && (a.neg ^ p.neg);
        break;
    default:         /* a*d over b*c */
        ok = mag_mul(&a, &q, &n) && mag_mul(&b, &p, &d);
        n.neg = n.n != 0 && a.neg;
        d.neg = p.neg;
        break;
    }
    if (ok)
        rc = bn_reduce(h, &n, &d, parts);
done:
    bn_free(&a);
    bn_free(&b);
    bn_free(&p);
    bn_free(&q);
    bn_free(&s);
    bn_free(&t);
    bn_free(&n);
    bn_free(&d);
    return rc;
}
