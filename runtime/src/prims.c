/*
 * prims.c -- Prim.apply of OpenVerse/Core/Prims.lean.
 *
 * Each case is the Lean equation quoted above it.  A case whose argument
 * list does not match falls through (`break`) to the last equation of
 * Prim.apply, `| _, _ => .err .type`.  Allocation failure is a resource
 * limit (VX_L_MEMORY), which Lean does not have.
 *
 * The arguments a[0..n) live on the interpreter's value stack, which no
 * primitive changes; heap cells, however, move when the heap grows, so
 * element pointers are taken only after the last allocation.
 *
 * Ints are the Verse VM's, up to 2^20 bits (#724).  Two INT operands take
 * arith.c's fast path; when it reports VX_OVERFLOW (the result does not fit
 * in 64 bits), or an operand is BIG, bigint.c computes the result.
 */
#include <math.h>
#include <string.h>
#include "vx_runtime.h"

/* The paths of ints beyond 64 bits stay out of vx_prim_apply's code, so that
   its 64-bit paths keep their size. */
#if defined(__GNUC__)
#define VX_SLOW __attribute__((noinline, cold))
#else
#define VX_SLOW
#endif

static void ok_copy(vx_res *r, const vx_val *v)
{
    vx_res_ok(r, v->tag, v->bits);
}

static void nomem(vx_res *r)
{
    vx_res_limit(r, VX_L_MEMORY);
}

static int is(const vx_val *v, uint64_t tag)
{
    return v->tag == tag;
}

static int64_t I(const vx_val *v)
{
    return vx_int_of(v->bits);
}

/* The int operation op on two ints of which one at least is BIG, or whose
   result arith.c found out of 64 bits: Res.ofInt of the exact result
   (VX_FAIL: the `if b = 0 then .fail`). */
static VX_SLOW void big(vx_ctx *c, uint32_t op, const vx_val *x, const vx_val *y, vx_res *r)
{
    vx_val z;
    int rc = vx_big_op(&c->heap, op, x, y, &z);
    if (rc == VX_OK)
        vx_res_ok(r, z.tag, z.bits);
    else if (rc == VX_FAIL)
        vx_res_fail(r);
    else if (rc == VX_OVERFLOW)
        vx_res_error(r, VX_E_OVERFLOW);   /* longer than IntBits.max bits */
    else
        nomem(r);
}

/* Res.ofInt of an arith.c result: the fast path; on VX_OVERFLOW (the result
   does not fit in 64 bits), bigint.c's. */
static void arith(vx_ctx *c, uint32_t op, const vx_val *a, vx_res *r, int rc, int64_t z)
{
    if (rc == VX_OK)
        vx_res_ok(r, VX_T_INT, vx_bits_of(z));
    else if (rc == VX_FAIL)
        vx_res_fail(r);
    else
        big(c, op, &a[0], &a[op == VX_P_NEG || op == VX_P_ABS ? 0 : 1], r);
}

/* The order of two ints: -1, 0, 1. */
static VX_SLOW int order(vx_ctx *c, const vx_val *x, const vx_val *y)
{
    return vx_big_cmp(&c->heap, x, y);
}

/* cmpRes b left = if b then .ok left else .fail */
static void cmp(vx_res *r, int b, const vx_val *left)
{
    if (b)
        ok_copy(r, left);
    else
        vx_res_fail(r);
}

/* asBytes vs = some _  (every element is a char) */
static int all_chars(const vx_heap *h, size_t o)
{
    size_t n = vx_obj_len(h, o), k;
    const vx_val *e = vx_obj_elems(h, o);
    for (k = 0; k < n; k++)
        if (e[k].tag != VX_T_CHAR)
            return 0;
    return 1;
}

/* A new object with tag `tag` and elements src[0..n) (src not in the heap). */
static int new_from(vx_ctx *c, uint64_t tag, const vx_val *src, size_t n, vx_res *r)
{
    size_t o;
    if (vx_heap_alloc(&c->heap, n, &o) != VX_OK) {
        nomem(r);
        return 0;
    }
    if (n > 0)
        memcpy(vx_obj_elems(&c->heap, o), src, n * sizeof(vx_val));
    vx_res_ok(r, tag, o);
    return 1;
}

/* Exact rational forms of ADD/SUB/MUL/QUOTIENT take four int parts.
   Positive int64 denominators bound every product and add/sub sum inside
   signed 128 bits; a reduced part outside 64 bits is BIG, and BIG
   operands take bigint.c's path (vx_big_rational). */
static void rational(vx_ctx *c, uint32_t op, int64_t a, int64_t b,
                     int64_t p, int64_t q, vx_res *r)
{
    typedef __int128 wide;
    typedef unsigned __int128 uwide;
    wide n, d;
    uwide un, ud, x, y, rem, g, bound;
    int negative;
    vx_val parts[2];
    if (b <= 0 || q <= 0) {
        vx_res_error(r, VX_E_OVERFLOW);
        return;
    }
    if (op == VX_P_QUOTIENT && p == 0) {
        vx_res_fail(r);
        return;
    }
    if (op == VX_P_ADD)
        n = (wide)a * q + (wide)p * b;
    else if (op == VX_P_SUB)
        n = (wide)a * q - (wide)p * b;
    else if (op == VX_P_MUL)
        n = (wide)a * p;
    else
        n = (wide)a * q;
    d = op == VX_P_QUOTIENT ? (wide)b * p : (wide)b * q;
    negative = (n < 0) != (d < 0);
    un = n < 0 ? (uwide)0 - (uwide)n : (uwide)n;
    ud = d < 0 ? (uwide)0 - (uwide)d : (uwide)d;
    x = un;
    y = ud;
    while (y != 0) {
        rem = x % y;
        x = y;
        y = rem;
    }
    g = x;
    un /= g;
    ud /= g;
    bound = negative ? (uwide)INT64_MAX + 1 : (uwide)INT64_MAX;
    if (un > bound || ud > (uwide)INT64_MAX) {
        uint64_t wn[2], wd[2];
        wn[0] = (uint64_t)un;
        wn[1] = (uint64_t)(un >> 64);
        wd[0] = (uint64_t)ud;
        wd[1] = (uint64_t)(ud >> 64);
        if (vx_big_words(&c->heap, negative, wn, 2, &parts[0]) != VX_OK ||
            vx_big_words(&c->heap, 0, wd, 2, &parts[1]) != VX_OK) {
            nomem(r);
            return;
        }
    } else {
        parts[0] = (vx_val){VX_T_INT, negative ? UINT64_C(0) - (uint64_t)un : (uint64_t)un};
        parts[1] = (vx_val){VX_T_INT, (uint64_t)ud};
    }
    new_from(c, VX_T_TUP, parts, 2, r);
}

/* The rational forms with a BIG part. */
static VX_SLOW void big_rational(vx_ctx *c, uint32_t op, const vx_val *a, vx_res *r)
{
    vx_val parts[2];
    int rc = vx_big_rational(&c->heap, op, a, parts);
    if (rc == VX_OK)
        new_from(c, VX_T_TUP, parts, 2, r);
    else if (rc == VX_FAIL)
        vx_res_fail(r);
    else if (rc == VX_OVERFLOW)
        vx_res_error(r, VX_E_OVERFLOW);
    else
        nomem(r);
}

/* A string value of the ASCII text s[0..n). */
static void str_of(vx_ctx *c, const char *s, size_t n, vx_res *r)
{
    size_t k, o;
    vx_val *e;
    if (vx_heap_alloc(&c->heap, n, &o) != VX_OK) {
        nomem(r);
        return;
    }
    e = vx_obj_elems(&c->heap, o);
    for (k = 0; k < n; k++) {
        e[k].tag = VX_T_CHAR;
        e[k].bits = (uint64_t)(unsigned char)s[k];
    }
    vx_res_ok(r, VX_T_ARR, o);
}

static double F(const vx_val *v)
{
    return vx_fval(v->bits);
}

static void ok_float(vx_res *r, double d)
{
    vx_res_ok(r, VX_T_FLOAT, vx_fcanon(d));
}

/* VFloat.toIntRes: NaN or an infinity fails; out of range is the overflow error */
static void to_int(vx_res *r, int mode, const vx_val *v)
{
    int64_t i;
    if (((v->bits >> 52) & 2047u) == 2047u)
        vx_res_fail(r);
    else if (vx_ftoint(mode, v->bits, &i) == VX_OK)
        vx_res_ok(r, VX_T_INT, vx_bits_of(i));
    else
        vx_res_error(r, VX_E_OVERFLOW);
}

/* intBytes i: decimal, '-' for negatives (Lean's toString on Int). */
static void int_to_str(vx_ctx *c, int64_t i, vx_res *r)
{
    char d[24];
    size_t n = 0, k, o;
    uint64_t m = i < 0 ? (uint64_t)0 - vx_bits_of(i) : vx_bits_of(i);
    vx_val *e;
    do {
        d[n++] = (char)('0' + (int)(m % 10));
        m /= 10;
    } while (m != 0);
    if (i < 0)
        d[n++] = '-';
    if (vx_heap_alloc(&c->heap, n, &o) != VX_OK) {
        nomem(r);
        return;
    }
    e = vx_obj_elems(&c->heap, o);
    for (k = 0; k < n; k++) {
        e[k].tag = VX_T_CHAR;
        e[k].bits = (uint64_t)(unsigned char)d[n - 1 - k];
    }
    vx_res_ok(r, VX_T_ARR, o);
}

/* .concat, [.arr xs, .arr ys] => .ok (.arr (xs ++ ys)) */
static void concat(vx_ctx *c, const vx_val *x, const vx_val *y, vx_res *r)
{
    size_t nx = vx_obj_len(&c->heap, x->bits), ny = vx_obj_len(&c->heap, y->bits), o;
    vx_val *e;
    if (nx == 0) {        /* values are immutable: sharing is invisible */
        ok_copy(r, y);
        return;
    }
    if (ny == 0) {
        ok_copy(r, x);
        return;
    }
    if (vx_heap_alloc(&c->heap, nx + ny, &o) != VX_OK) {
        nomem(r);
        return;
    }
    e = vx_obj_elems(&c->heap, o);
    memcpy(e, vx_obj_elems(&c->heap, x->bits), nx * sizeof(vx_val));
    memcpy(e + nx, vx_obj_elems(&c->heap, y->bits), ny * sizeof(vx_val));
    vx_res_ok(r, VX_T_ARR, o);
}

/* .flatten, [.arr xss] => match flattenArrs xss with
     | some vs => .ok (.arr vs) | none => .err .type */
static void flatten(vx_ctx *c, const vx_val *x, vx_res *r)
{
    size_t n = vx_obj_len(&c->heap, x->bits), k, total = 0, o, at = 0;
    const vx_val *xs = vx_obj_elems(&c->heap, x->bits);
    vx_val *e;
    int too_big = 0;
    for (k = 0; k < n; k++) {
        if (xs[k].tag != VX_T_ARR) {
            vx_res_error(r, VX_E_TYPE);
            return;
        }
        /* Repeated references can expand beyond the heap limit. Keep
           checking the remaining types before reporting a memory limit. */
        if (!too_big) {
            size_t m = vx_obj_len(&c->heap, xs[k].bits);
            if (m > c->heap.max - total)
                too_big = 1;
            else
                total += m;
        }
    }
    if (too_big || vx_heap_alloc(&c->heap, total, &o) != VX_OK) {
        nomem(r);
        return;
    }
    xs = vx_obj_elems(&c->heap, x->bits);
    e = vx_obj_elems(&c->heap, o);
    for (k = 0; k < n; k++) {
        size_t m = vx_obj_len(&c->heap, xs[k].bits);
        if (m > 0)
            memcpy(e + at, vx_obj_elems(&c->heap, xs[k].bits), m * sizeof(vx_val));
        at += m;
    }
    vx_res_ok(r, VX_T_ARR, o);
}

/* .range with a BIG bound: rangeVals a b, each element a + k (INT or BIG) */
static VX_SLOW void big_range(vx_ctx *c, const vx_val *a, const vx_val *b, vx_res *r)
{
    vx_val d, one = { VX_T_INT, 1 }, x;
    size_t o, k, cnt;
    if (vx_big_cmp(&c->heap, a, b) > 0) {
        vx_res_ok(r, VX_T_ARR, 0);
        return;
    }
    /* the count, b - a + 1, must fit the heap */
    if (vx_big_op(&c->heap, VX_P_SUB, b, a, &d) != VX_OK || d.tag != VX_T_INT ||
        d.bits >= (uint64_t)c->heap.max || vx_heap_alloc(&c->heap, (size_t)d.bits + 1, &o) != VX_OK) {
        nomem(r);
        return;
    }
    cnt = (size_t)d.bits + 1;
    x = *a;
    for (k = 0; k < cnt; k++) {
        vx_obj_elems(&c->heap, o)[k] = x;
        if (k + 1 < cnt && vx_big_op(&c->heap, VX_P_ADD, &x, &one, &x) != VX_OK) {
            nomem(r);
            return;
        }
    }
    vx_res_ok(r, VX_T_ARR, o);
}

/* .range, [.int a, .int b] => .ok (.arr (rangeVals a b)) -- a..b inclusive */
static void range(vx_ctx *c, int64_t a, int64_t b, vx_res *r)
{
    uint64_t last, k;
    size_t o;
    vx_val *e;
    if (a > b) {
        vx_res_ok(r, VX_T_ARR, 0);
        return;
    }
    last = vx_bits_of(b) - vx_bits_of(a);   /* count - 1, exact */
    if (last >= (uint64_t)c->heap.max || vx_heap_alloc(&c->heap, (size_t)last + 1, &o) != VX_OK) {
        nomem(r);
        return;
    }
    e = vx_obj_elems(&c->heap, o);
    for (k = 0; k <= last; k++) {
        e[k].tag = VX_T_INT;
        e[k].bits = vx_bits_of(a) + k;
    }
    vx_res_ok(r, VX_T_ARR, o);
}

/* .arrSet, [.arr xs, .int i, v] =>
     if 0 ≤ i ∧ i.toNat < xs.length then .ok (.arr (xs.set i.toNat v)) else .fail */
static void arr_set(vx_ctx *c, const vx_val *x, int64_t i, const vx_val *v, vx_res *r)
{
    size_t n = vx_obj_len(&c->heap, x->bits), o;
    vx_val *e;
    if (i < 0 || (uint64_t)i >= (uint64_t)n) {
        vx_res_fail(r);
        return;
    }
    if (vx_heap_alloc(&c->heap, n, &o) != VX_OK) {
        nomem(r);
        return;
    }
    e = vx_obj_elems(&c->heap, o);
    memcpy(e, vx_obj_elems(&c->heap, x->bits), n * sizeof(vx_val));
    e[i].tag = v->tag;
    e[i].bits = v->bits;
    vx_res_ok(r, VX_T_ARR, o);
}

/* The position of the first element of the array xs that is a pair whose key
   equals k (Value.keyIs: `.tup [k', _]` with `veq k' k`), or the array's
   length when there is none; VX_E_NOMEM as vx_equal's. */
static int map_scan(vx_ctx *c, const vx_val *xs, const vx_val *k, size_t *at)
{
    size_t n = vx_obj_len(&c->heap, xs->bits), i;
    const vx_val *ps = vx_obj_elems(&c->heap, xs->bits);
    int eq, rc;
    for (i = 0; i < n; i++) {
        const vx_val *p = &ps[i], *key;
        if (p->tag != VX_T_TUP || vx_obj_len(&c->heap, p->bits) != 2)
            continue;
        key = vx_obj_elems(&c->heap, p->bits);
        /* (two ints within 64 bits, or two chars: equal when their bits are;
           vx_equal decides the same, by a longer way) */
        if (key->tag == k->tag && (k->tag == VX_T_INT || k->tag == VX_T_CHAR)) {
            if (key->bits == k->bits)
                break;
            continue;
        }
        if ((rc = vx_equal(&c->heap, key, k, &eq)) != VX_OK)
            return rc;
        if (eq)
            break;
    }
    *at = i;
    return VX_OK;
}

void vx_prim_apply(vx_ctx *c, uint32_t op, uint32_t k, const vx_val *a, size_t n, vx_res *r)
{
    int64_t z = 0;
    int rc, eq;
    int ii = n == 2 && is(&a[0], VX_T_INT) && is(&a[1], VX_T_INT);
    int cc = n == 2 && is(&a[0], VX_T_CHAR) && is(&a[1], VX_T_CHAR);
    int i1 = n == 1 && is(&a[0], VX_T_INT);
    int ff = n == 2 && is(&a[0], VX_T_FLOAT) && is(&a[1], VX_T_FLOAT);
    int f1 = n == 1 && is(&a[0], VX_T_FLOAT);
    char fb[VX_FMT_MAX];
    /* ints, one at least BIG (tested only where ii or i1 did not hold, so the
       fast path pays nothing) */
#define bb (n == 2 && vx_isint(&a[0]) && vx_isint(&a[1]))
#define b1 (n == 1 && vx_isint(&a[0]))

    if (n == 4 && (op == VX_P_ADD || op == VX_P_SUB || op == VX_P_MUL || op == VX_P_QUOTIENT)) {
        if (is(&a[0], VX_T_INT) && is(&a[1], VX_T_INT) &&
            is(&a[2], VX_T_INT) && is(&a[3], VX_T_INT))
            rational(c, op, I(&a[0]), I(&a[1]), I(&a[2]), I(&a[3]), r);
        else if (vx_isint(&a[0]) && vx_isint(&a[1]) && vx_isint(&a[2]) && vx_isint(&a[3]))
            big_rational(c, op, a, r);
        else
            vx_res_error(r, VX_E_TYPE);
        return;
    }

    switch (op) {
    /* | .add, [.int a, .int b] => .ok (.int (a + b)) */
    case VX_P_ADD:
        if (ii) { rc = vx_add(I(&a[0]), I(&a[1]), &z); arith(c, op, a, r, rc, z); return; }
        if (bb) { big(c, op, &a[0], &a[1], r); return; }
        break;
    /* | .sub, [.int a, .int b] => .ok (.int (a - b)) */
    case VX_P_SUB:
        if (ii) { rc = vx_sub(I(&a[0]), I(&a[1]), &z); arith(c, op, a, r, rc, z); return; }
        if (bb) { big(c, op, &a[0], &a[1], r); return; }
        break;
    /* | .mul, [.int a, .int b] => .ok (.int (a * b)) */
    case VX_P_MUL:
        if (ii) { rc = vx_mul(I(&a[0]), I(&a[1]), &z); arith(c, op, a, r, rc, z); return; }
        if (bb) { big(c, op, &a[0], &a[1], r); return; }
        break;
    /* | .neg, [.int a] => .ok (.int (-a)) */
    case VX_P_NEG:
        if (i1) { rc = vx_neg(I(&a[0]), &z); arith(c, op, a, r, rc, z); return; }
        if (b1) { big(c, op, &a[0], &a[0], r); return; }
        break;
    /* | .abs, [.int a] => .ok (.int (if a < 0 then -a else a)) */
    case VX_P_ABS:
        if (i1) { rc = vx_abs(I(&a[0]), &z); arith(c, op, a, r, rc, z); return; }
        if (b1) { big(c, op, &a[0], &a[0], r); return; }
        break;
    /* | .floorDiv, [.int a, .int b] => if b = 0 then .fail else .ok (.int (floorDivInt a b)) */
    case VX_P_FLOORDIV:
        if (ii) { rc = vx_floordiv(I(&a[0]), I(&a[1]), &z); arith(c, op, a, r, rc, z); return; }
        if (bb) { big(c, op, &a[0], &a[1], r); return; }
        break;
    /* | .ceilDiv, [.int a, .int b] => if b = 0 then .fail else .ok (.int (ceilDivInt a b)) */
    case VX_P_CEILDIV:
        if (ii) { rc = vx_ceildiv(I(&a[0]), I(&a[1]), &z); arith(c, op, a, r, rc, z); return; }
        if (bb) { big(c, op, &a[0], &a[1], r); return; }
        break;
    /* | .quotient, [.int a, .int b] => if b = 0 then .fail else .ok (.int (Int.ediv a b)) */
    case VX_P_QUOTIENT:
        if (ii) { rc = vx_quotient(I(&a[0]), I(&a[1]), &z); arith(c, op, a, r, rc, z); return; }
        if (bb) { big(c, op, &a[0], &a[1], r); return; }
        break;
    /* | .modulo, [.int a, .int b] => if b = 0 then .fail else .ok (.int (Int.emod a b)) */
    case VX_P_MODULO:
        if (ii) { rc = vx_modulo(I(&a[0]), I(&a[1]), &z); arith(c, op, a, r, rc, z); return; }
        if (bb) { big(c, op, &a[0], &a[1], r); return; }
        break;
    /* | .lt, [.int a, .int b] => cmpRes (decide (a < b)) (.int a)
       | .lt, [.char a, .char b] => cmpRes (decide (a < b)) (.char a)   (and le, gt, ge) */
    case VX_P_LT:
        if (ii) { cmp(r, I(&a[0]) < I(&a[1]), &a[0]); return; }
        if (cc) { cmp(r, a[0].bits < a[1].bits, &a[0]); return; }
        if (bb) { cmp(r, order(c, &a[0], &a[1]) < 0, &a[0]); return; }
        break;
    case VX_P_LE:
        if (ii) { cmp(r, I(&a[0]) <= I(&a[1]), &a[0]); return; }
        if (cc) { cmp(r, a[0].bits <= a[1].bits, &a[0]); return; }
        if (bb) { cmp(r, order(c, &a[0], &a[1]) <= 0, &a[0]); return; }
        break;
    case VX_P_GT:
        if (ii) { cmp(r, I(&a[0]) > I(&a[1]), &a[0]); return; }
        if (cc) { cmp(r, a[0].bits > a[1].bits, &a[0]); return; }
        if (bb) { cmp(r, order(c, &a[0], &a[1]) > 0, &a[0]); return; }
        break;
    case VX_P_GE:
        if (ii) { cmp(r, I(&a[0]) >= I(&a[1]), &a[0]); return; }
        if (cc) { cmp(r, a[0].bits >= a[1].bits, &a[0]); return; }
        if (bb) { cmp(r, order(c, &a[0], &a[1]) >= 0, &a[0]); return; }
        break;
    /* | .eq, [a, b] => cmpRes (Value.veq a b) a
       | .ne, [a, b] => cmpRes (!Value.veq a b) a  (vx_equal) */
    case VX_P_EQ:
    case VX_P_NE:
        if (n == 2) {
            if (vx_equal(&c->heap, &a[0], &a[1], &eq) != VX_OK) { nomem(r); return; }
            cmp(r, op == VX_P_EQ ? eq : !eq, &a[0]);
            return;
        }
        break;
    /* | .query, [.logic b] => if b then .ok (.logic true) else .fail
       | .query, [.none] => .fail
       | .query, [.some v] => .ok v */
    case VX_P_QUERY:
        if (n == 1 && is(&a[0], VX_T_LOGIC)) {
            if (a[0].bits) vx_res_ok(r, VX_T_LOGIC, 1); else vx_res_fail(r);
            return;
        }
        if (n == 1 && is(&a[0], VX_T_NONE)) { vx_res_fail(r); return; }
        if (n == 1 && is(&a[0], VX_T_SOME)) { ok_copy(r, vx_obj_elems(&c->heap, a[0].bits)); return; }
        break;
    /* | .mkArr, vs => .ok (.arr vs) */
    case VX_P_MKARR:
        new_from(c, VX_T_ARR, a, n, r);
        return;
    /* | .mkTup, vs => .ok (.tup vs) */
    case VX_P_MKTUP:
        new_from(c, VX_T_TUP, a, n, r);
        return;
    /* | .mkSome, [v] => .ok (.some v) */
    case VX_P_MKSOME:
        if (n == 1) { new_from(c, VX_T_SOME, a, 1, r); return; }
        break;
    /* | .concat, [.arr xs, .arr ys] => .ok (.arr (xs ++ ys)) */
    case VX_P_CONCAT:
        if (n == 2 && is(&a[0], VX_T_ARR) && is(&a[1], VX_T_ARR)) { concat(c, &a[0], &a[1], r); return; }
        break;
    /* | .flatten, [.arr xss] => ... */
    case VX_P_FLATTEN:
        if (n == 1 && is(&a[0], VX_T_ARR)) { flatten(c, &a[0], r); return; }
        break;
    /* | .range, [.int a, .int b] => .ok (.arr (rangeVals a b)) */
    case VX_P_RANGE:
        if (ii) { range(c, I(&a[0]), I(&a[1]), r); return; }
        if (bb) { big_range(c, &a[0], &a[1], r); return; }
        break;
    /* | .index, [.arr xs, .int i] =>
         if 0 ≤ i then match xs[i.toNat]? with | some v => .ok v | none => .fail else .fail
       (a BIG index is past every array, or negative: it fails) */
    case VX_P_INDEX:
        if (n == 2 && is(&a[0], VX_T_ARR) && is(&a[1], VX_T_INT)) {
            int64_t i = I(&a[1]);
            if (i >= 0 && (uint64_t)i < (uint64_t)vx_obj_len(&c->heap, a[0].bits))
                ok_copy(r, &vx_obj_elems(&c->heap, a[0].bits)[i]);
            else
                vx_res_fail(r);
            return;
        }
        if (n == 2 && is(&a[0], VX_T_ARR) && is(&a[1], VX_T_BIG)) { vx_res_fail(r); return; }
        break;
    /* | .len, [.arr xs] => .ok (.int xs.length) */
    case VX_P_LEN:
        if (n == 1 && is(&a[0], VX_T_ARR)) {
            vx_res_ok(r, VX_T_INT, (uint64_t)vx_obj_len(&c->heap, a[0].bits));
            return;
        }
        break;
    /* | .arrSet, [.arr xs, .int i, v] => ... */
    case VX_P_ARRSET:
        if (n == 3 && is(&a[0], VX_T_ARR) && is(&a[1], VX_T_INT)) {
            arr_set(c, &a[0], I(&a[1]), &a[2], r);
            return;
        }
        if (n == 3 && is(&a[0], VX_T_ARR) && is(&a[1], VX_T_BIG)) { vx_res_fail(r); return; }
        break;
    /* | .tupGet k, [.tup vs] => match vs[k]? with | some v => .ok v | none => .err .type */
    /* | .mapGet, [.arr ps, k] => match ps.find? (Value.keyIs k) with
         | some (.tup [_, v]) => .ok v | _ => .fail
       | .mapFind, [.arr ps, k] => match ps.findIdx? (Value.keyIs k) with
         | some i => .ok (.int i) | none => .fail */
    case VX_P_MAPGET:
    case VX_P_MAPFIND:
        if (n == 2 && is(&a[0], VX_T_ARR)) {
            size_t at;
            if (map_scan(c, &a[0], &a[1], &at) != VX_OK) { nomem(r); return; }
            if (at >= vx_obj_len(&c->heap, a[0].bits))
                vx_res_fail(r);
            else if (op == VX_P_MAPFIND)
                vx_res_ok(r, VX_T_INT, (uint64_t)at);
            else
                ok_copy(r, &vx_obj_elems(&c->heap, vx_obj_elems(&c->heap, a[0].bits)[at].bits)[1]);
            return;
        }
        break;
    case VX_P_TUPGET:
        if (n == 1 && is(&a[0], VX_T_TUP)) {
            if ((size_t)k < vx_obj_len(&c->heap, a[0].bits))
                ok_copy(r, &vx_obj_elems(&c->heap, a[0].bits)[k]);
            else
                vx_res_error(r, VX_E_TYPE);
            return;
        }
        break;
    /* | .toStr, [v] => toStrValue v, where
       toStrValue (.int i) = if Int64.inRange i then .ok (.arr ((intBytes i).map .char))
                             else .err .overflow   (the Verse VM's ToString(:int), #724)
       toStrValue (.char c) = .ok (.arr [.char c])
       toStrValue (.arr vs) = match asBytes vs with | some _ => .ok (.arr vs) | none => .err .type
       toStrValue _ = .err .type */
    case VX_P_TOSTR:
        if (n == 1) {
            if (is(&a[0], VX_T_INT))
                int_to_str(c, I(&a[0]), r);
            else if (is(&a[0], VX_T_BIG))
                vx_res_error(r, VX_E_OVERFLOW);
            else if (is(&a[0], VX_T_CHAR))
                new_from(c, VX_T_ARR, &a[0], 1, r);
            /* toStrValue (.float b) = .ok (Value.ofString (VFloat.fixed6 b)) */
            else if (is(&a[0], VX_T_FLOAT))
                str_of(c, fb, vx_fmt(a[0].bits, fb), r);
            else if (is(&a[0], VX_T_ARR) && all_chars(&c->heap, a[0].bits))
                ok_copy(r, &a[0]);
            else
                vx_res_error(r, VX_E_TYPE);
            return;
        }
        break;
    /* | .fail, [] => .fail */
    case VX_P_FAIL:
        if (n == 0) { vx_res_fail(r); return; }
        break;
    /* | .userErr, [] => .err .user */
    case VX_P_USERERR:
        if (n == 0) { vx_res_error(r, VX_E_USER); return; }
        break;
    /* floats (#127): | .fadd, [.float a, .float b] => .ok (.float (canon (a + b))), … */
    case VX_P_FADD:
        if (ff) { ok_float(r, F(&a[0]) + F(&a[1])); return; }
        break;
    case VX_P_FSUB:
        if (ff) { ok_float(r, F(&a[0]) - F(&a[1])); return; }
        break;
    case VX_P_FMUL:
        if (ff) { ok_float(r, F(&a[0]) * F(&a[1])); return; }
        break;
    case VX_P_FDIV:
        if (ff) { ok_float(r, F(&a[0]) / F(&a[1])); return; }
        break;
    case VX_P_FNEG:
        if (f1) { ok_float(r, -F(&a[0])); return; }
        break;
    case VX_P_FABS:
        if (f1) { double x = F(&a[0]); ok_float(r, x < 0 ? -x : x); return; }
        break;
    /* | .fmin, [.float a, .float b] => .ok (.float (VFloat.fmin a b)) (NaN if either is) */
    case VX_P_FMIN:
    case VX_P_FMAX:
        if (ff) {
            double x = F(&a[0]), y = F(&a[1]);
            if (x != x || y != y) vx_res_ok(r, VX_T_FLOAT, vx_fcanon(x != x ? x : y));
            else if (op == VX_P_FMIN) ok_copy(r, y < x ? &a[1] : &a[0]);
            else ok_copy(r, x < y ? &a[1] : &a[0]);
            return;
        }
        break;
    /* | .flt, [.float a, .float b] => cmpRes (decide (a < b)) (.float a), and fle, fgt, fge */
    case VX_P_FLT:
        if (ff) { cmp(r, F(&a[0]) < F(&a[1]), &a[0]); return; }
        break;
    /* (NaN <= NaN and NaN >= NaN succeed: canonical bits, a == b) */
    case VX_P_FLE:
        if (ff) { cmp(r, a[0].bits == a[1].bits || F(&a[0]) <= F(&a[1]), &a[0]); return; }
        break;
    case VX_P_FGT:
        if (ff) { cmp(r, F(&a[1]) < F(&a[0]), &a[0]); return; }
        break;
    case VX_P_FGE:
        if (ff) { cmp(r, a[0].bits == a[1].bits || F(&a[1]) <= F(&a[0]), &a[0]); return; }
        break;
    /* | .fofInt, [.int i] => .ok (.float (canon (Float.ofInt i))) */
    case VX_P_FOFINT:
        if (i1) { ok_float(r, (double)I(&a[0])); return; }
        if (b1) { ok_float(r, vx_big_double(&c->heap, &a[0])); return; }
        break;
    /* | .ffloor, [.float a] => VFloat.toIntRes .floor a, and fceil, fround, ftrunc */
    case VX_P_FFLOOR:
        if (f1) { to_int(r, VX_FFLOOR, &a[0]); return; }
        break;
    case VX_P_FCEIL:
        if (f1) { to_int(r, VX_FCEIL, &a[0]); return; }
        break;
    case VX_P_FROUND:
        if (f1) { to_int(r, VX_FROUND, &a[0]); return; }
        break;
    case VX_P_FTRUNC:
        if (f1) { to_int(r, VX_FTRUNC, &a[0]); return; }
        break;
    /* the mathematical functions (#132): | .fsqrt, [.float a] => .ok (.float (canon a.sqrt)), … */
    case VX_P_FSQRT: if (f1) { ok_float(r, sqrt(F(&a[0]))); return; } break;
    case VX_P_FEXP:  if (f1) { ok_float(r, exp(F(&a[0]))); return; } break;
    case VX_P_FLN:   if (f1) { ok_float(r, log(F(&a[0]))); return; } break;
    case VX_P_FSIN:  if (f1) { ok_float(r, sin(F(&a[0]))); return; } break;
    case VX_P_FCOS:  if (f1) { ok_float(r, cos(F(&a[0]))); return; } break;
    case VX_P_FTAN:  if (f1) { ok_float(r, tan(F(&a[0]))); return; } break;
    /* ArcSin, ArcCos: the argument clamped to [-1, 1] (VFloat.clamp1; NaN stays) */
    case VX_P_FASIN:
    case VX_P_FACOS:
        if (f1) {
            double x = F(&a[0]);
            if (x < -1.0) x = -1.0; else if (1.0 < x) x = 1.0;
            ok_float(r, op == VX_P_FASIN ? asin(x) : acos(x));
            return;
        }
        break;
    case VX_P_FATAN:  if (f1) { ok_float(r, atan(F(&a[0]))); return; } break;
    case VX_P_FPOW:   if (ff) { ok_float(r, pow(F(&a[0]), F(&a[1]))); return; } break;
    case VX_P_FATAN2: if (ff) { ok_float(r, atan2(F(&a[0]), F(&a[1]))); return; } break;
    case VX_P_FSINH:  if (f1) { ok_float(r, sinh(F(&a[0]))); return; } break;
    case VX_P_FCOSH:  if (f1) { ok_float(r, cosh(F(&a[0]))); return; } break;
    case VX_P_FTANH:  if (f1) { ok_float(r, tanh(F(&a[0]))); return; } break;
    case VX_P_FASINH: if (f1) { ok_float(r, asinh(F(&a[0]))); return; } break;
    case VX_P_FACOSH: if (f1) { ok_float(r, acosh(F(&a[0]))); return; } break;
    case VX_P_FATANH: if (f1) { ok_float(r, atanh(F(&a[0]))); return; } break;
    /* | .fisFinite, [.float a] => if isFinite a then .ok (.float a) else .fail */
    case VX_P_FISFINITE:
        if (f1) {
            if (((a[0].bits >> 52) & 2047u) == 2047u) vx_res_fail(r); else ok_copy(r, &a[0]);
            return;
        }
        break;
    /* | .fofBits, [.int i] => .ok (.float (canon (ofBits i))) (a float literal) */
    case VX_P_FOFBITS:
        if (i1) { vx_res_ok(r, VX_T_FLOAT, vx_fcanon(vx_fval(a[0].bits))); return; }
        if (b1) { vx_res_ok(r, VX_T_FLOAT, vx_fcanon(vx_fval(vx_big_low64(&c->heap, &a[0])))); return; }
        break;
    default:
        break;
    }
#undef bb
#undef b1
    /* | _, _ => .err .type */
    vx_res_error(r, VX_E_TYPE);
}
