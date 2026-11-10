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
 */
#include <math.h>
#include <string.h>
#include "vx_runtime.h"

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

/* Res.ofInt of an arith.c result (VX_FAIL: the `if b = 0 then .fail`). */
static void arith(vx_res *r, int rc, int64_t z)
{
    if (rc == VX_OK)
        vx_res_ok(r, VX_T_INT, vx_bits_of(z));
    else if (rc == VX_FAIL)
        vx_res_fail(r);
    else
        vx_res_error(r, VX_E_OVERFLOW);
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

void vx_prim_apply(vx_ctx *c, uint32_t op, uint32_t k, const vx_val *a, size_t n, vx_res *r)
{
    int64_t z = 0;
    int rc, eq;
    int ii = n == 2 && is(&a[0], VX_T_INT) && is(&a[1], VX_T_INT);
    int cc = n == 2 && is(&a[0], VX_T_CHAR) && is(&a[1], VX_T_CHAR);
    int i1 = n == 1 && is(&a[0], VX_T_INT);
    int ff = n == 2 && is(&a[0], VX_T_FLOAT) && is(&a[1], VX_T_FLOAT);
    int f1 = n == 1 && is(&a[0], VX_T_FLOAT);
    char fb[48];

    switch (op) {
    /* | .add, [.int a, .int b] => Res.ofInt (a + b) */
    case VX_P_ADD:
        if (ii) { rc = vx_add(I(&a[0]), I(&a[1]), &z); arith(r, rc, z); return; }
        break;
    /* | .sub, [.int a, .int b] => Res.ofInt (a - b) */
    case VX_P_SUB:
        if (ii) { rc = vx_sub(I(&a[0]), I(&a[1]), &z); arith(r, rc, z); return; }
        break;
    /* | .mul, [.int a, .int b] => Res.ofInt (a * b) */
    case VX_P_MUL:
        if (ii) { rc = vx_mul(I(&a[0]), I(&a[1]), &z); arith(r, rc, z); return; }
        break;
    /* | .neg, [.int a] => Res.ofInt (-a) */
    case VX_P_NEG:
        if (i1) { rc = vx_neg(I(&a[0]), &z); arith(r, rc, z); return; }
        break;
    /* | .abs, [.int a] => Res.ofInt (if a < 0 then -a else a) */
    case VX_P_ABS:
        if (i1) { rc = vx_abs(I(&a[0]), &z); arith(r, rc, z); return; }
        break;
    /* | .floorDiv, [.int a, .int b] => if b = 0 then .fail else Res.ofInt (floorDivInt a b) */
    case VX_P_FLOORDIV:
        if (ii) { rc = vx_floordiv(I(&a[0]), I(&a[1]), &z); arith(r, rc, z); return; }
        break;
    /* | .ceilDiv, [.int a, .int b] => if b = 0 then .fail else Res.ofInt (ceilDivInt a b) */
    case VX_P_CEILDIV:
        if (ii) { rc = vx_ceildiv(I(&a[0]), I(&a[1]), &z); arith(r, rc, z); return; }
        break;
    /* | .quotient, [.int a, .int b] => if b = 0 then .fail else Res.ofInt (Int.ediv a b) */
    case VX_P_QUOTIENT:
        if (ii) { rc = vx_quotient(I(&a[0]), I(&a[1]), &z); arith(r, rc, z); return; }
        break;
    /* | .modulo, [.int a, .int b] => if b = 0 then .fail else Res.ofInt (Int.emod a b) */
    case VX_P_MODULO:
        if (ii) { rc = vx_modulo(I(&a[0]), I(&a[1]), &z); arith(r, rc, z); return; }
        break;
    /* | .lt, [.int a, .int b] => cmpRes (decide (a < b)) (.int a)
       | .lt, [.char a, .char b] => cmpRes (decide (a < b)) (.char a)   (and le, gt, ge) */
    case VX_P_LT:
        if (ii) { cmp(r, I(&a[0]) < I(&a[1]), &a[0]); return; }
        if (cc) { cmp(r, a[0].bits < a[1].bits, &a[0]); return; }
        break;
    case VX_P_LE:
        if (ii) { cmp(r, I(&a[0]) <= I(&a[1]), &a[0]); return; }
        if (cc) { cmp(r, a[0].bits <= a[1].bits, &a[0]); return; }
        break;
    case VX_P_GT:
        if (ii) { cmp(r, I(&a[0]) > I(&a[1]), &a[0]); return; }
        if (cc) { cmp(r, a[0].bits > a[1].bits, &a[0]); return; }
        break;
    case VX_P_GE:
        if (ii) { cmp(r, I(&a[0]) >= I(&a[1]), &a[0]); return; }
        if (cc) { cmp(r, a[0].bits >= a[1].bits, &a[0]); return; }
        break;
    /* | .eq, [a, b] => cmpRes (decide (a = b)) a
       | .ne, [a, b] => cmpRes (decide (a ≠ b)) a */
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
        break;
    /* | .index, [.arr xs, .int i] =>
         if 0 ≤ i then match xs[i.toNat]? with | some v => .ok v | none => .fail else .fail */
    case VX_P_INDEX:
        if (n == 2 && is(&a[0], VX_T_ARR) && is(&a[1], VX_T_INT)) {
            int64_t i = I(&a[1]);
            if (i >= 0 && (uint64_t)i < (uint64_t)vx_obj_len(&c->heap, a[0].bits))
                ok_copy(r, &vx_obj_elems(&c->heap, a[0].bits)[i]);
            else
                vx_res_fail(r);
            return;
        }
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
        break;
    /* | .tupGet k, [.tup vs] => match vs[k]? with | some v => .ok v | none => .err .type */
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
       toStrValue (.int i) = .ok (.arr ((intBytes i).map .char))
       toStrValue (.char c) = .ok (.arr [.char c])
       toStrValue (.arr vs) = match asBytes vs with | some _ => .ok (.arr vs) | none => .err .type
       toStrValue _ = .err .type */
    case VX_P_TOSTR:
        if (n == 1) {
            if (is(&a[0], VX_T_INT))
                int_to_str(c, I(&a[0]), r);
            else if (is(&a[0], VX_T_CHAR))
                new_from(c, VX_T_ARR, &a[0], 1, r);
            /* toStrValue (.float b) = .ok (Value.ofString (VFloat.render b)) */
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
        break;
    default:
        break;
    }
    /* | _, _ => .err .type */
    vx_res_error(r, VX_E_TYPE);
}
