/*
 * arith.c -- the int operations of Prim.apply (OpenVerse/Core/Prims.lean).
 *
 * Each function computes the exact mathematical result of the Lean
 * definition and returns VX_OVERFLOW when it lies outside
 * [INT64_MIN, INT64_MAX] (Res.ofInt), VX_FAIL when Lean fails (a zero
 * divisor), VX_OK otherwise.  No intermediate C expression overflows, so
 * every function is defined for all inputs.
 *
 * QuickProof subset: no builtins, no __int128, no casts between pointers
 * and integers, no switch, no recursion.
 *
 * Division: C's '/' and '%' truncate toward zero and are defined for every
 * pair except (INT64_MIN, -1).  So b == -1 is handled first in every
 * division (for b = -1: floor = ceil = ediv = -a, and emod = 0), and for
 * the remaining divisors |b| >= 2 or b == 1, where the truncated quotient q
 * satisfies |q| <= 2^62 or the remainder is 0, so q +- 1 cannot overflow.
 */
#include "openverse.h"

/* Prim.add: Res.ofInt (a + b) */
int vx_add(int64_t a, int64_t b, int64_t *out)
{
    if (b > 0 ? a > INT64_MAX - b : a < INT64_MIN - b)
        return VX_OVERFLOW;
    *out = a + b;
    return VX_OK;
}

/* Prim.sub: Res.ofInt (a - b) */
int vx_sub(int64_t a, int64_t b, int64_t *out)
{
    if (b > 0 ? a < INT64_MIN + b : a > INT64_MAX + b)
        return VX_OVERFLOW;
    *out = a - b;
    return VX_OK;
}

/* Prim.mul: Res.ofInt (a * b).  The bounds are C's truncated quotients of
 * the extreme values, which equal the real bounds rounded toward zero. */
int vx_mul(int64_t a, int64_t b, int64_t *out)
{
    int ovf = 0;
    if (a > 0) {
        if (b > 0)
            ovf = a > INT64_MAX / b;
        else
            ovf = b < INT64_MIN / a;
    } else if (a < 0) {
        if (b > 0)
            ovf = a < INT64_MIN / b;
        else if (b < 0)
            ovf = b < INT64_MAX / a;
    }
    if (ovf)
        return VX_OVERFLOW;
    *out = a * b;
    return VX_OK;
}

/* Prim.neg: Res.ofInt (-a) */
int vx_neg(int64_t a, int64_t *out)
{
    if (a == INT64_MIN)
        return VX_OVERFLOW;
    *out = -a;
    return VX_OK;
}

/* Prim.abs: Res.ofInt (if a < 0 then -a else a) */
int vx_abs(int64_t a, int64_t *out)
{
    if (a < 0)
        return vx_neg(a, out);
    *out = a;
    return VX_OK;
}

/* Prim.floorDiv: if b = 0 then fail else Res.ofInt (Int.fdiv a b) */
int vx_floordiv(int64_t a, int64_t b, int64_t *out)
{
    int64_t q;
    int64_t r;
    if (b == 0)
        return VX_FAIL;
    if (b == -1)
        return vx_neg(a, out);
    q = a / b;
    r = a % b;
    if (r != 0 && ((r < 0) != (b < 0)))
        q = q - 1;
    *out = q;
    return VX_OK;
}

/* Prim.ceilDiv: if b = 0 then fail else Res.ofInt (-Int.fdiv (-a) b) */
int vx_ceildiv(int64_t a, int64_t b, int64_t *out)
{
    int64_t q;
    int64_t r;
    if (b == 0)
        return VX_FAIL;
    if (b == -1)
        return vx_neg(a, out);
    q = a / b;
    r = a % b;
    if (r != 0 && ((r < 0) == (b < 0)))
        q = q + 1;
    *out = q;
    return VX_OK;
}

/* Prim.quotient: if b = 0 then fail else Res.ofInt (Int.ediv a b).
 * Euclidean: a = b * q + r with 0 <= r < |b|. */
int vx_quotient(int64_t a, int64_t b, int64_t *out)
{
    int64_t q;
    int64_t r;
    if (b == 0)
        return VX_FAIL;
    if (b == -1)
        return vx_neg(a, out);
    q = a / b;
    r = a % b;
    if (r < 0) {
        if (b > 0)
            q = q - 1;
        else
            q = q + 1;
    }
    *out = q;
    return VX_OK;
}

/* Prim.modulo: if b = 0 then fail else Res.ofInt (Int.emod a b).
 * The result is in [0, |b|), always representable.  For b < 0 and r < 0,
 * r - b lies in (0, -b) and so in range even when b = INT64_MIN. */
int vx_modulo(int64_t a, int64_t b, int64_t *out)
{
    int64_t r;
    if (b == 0)
        return VX_FAIL;
    if (b == -1) {
        *out = 0;
        return VX_OK;
    }
    r = a % b;
    if (r < 0) {
        if (b > 0)
            r = r + b;
        else
            r = r - b;
    }
    *out = r;
    return VX_OK;
}
