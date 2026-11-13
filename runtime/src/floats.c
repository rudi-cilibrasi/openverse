/*
 * floats.c -- floats (#127), as OpenVerse/Core/Float.lean defines them.
 *
 * A float value holds the bits of a canonical IEEE double: one NaN, and +0
 * for -0 (vx_fcanon).  The conversions to int (vx_ftoint) and the decimal
 * rendering (vx_fmt) work from the bits; the rendering is ToString's fixed
 * point with six digits after the point, printf's "%.6f".  Lean computes the
 * same thing exactly with integers.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "vx_runtime.h"

#define VX_NAN_BITS 0x7FF8000000000000ull

double vx_fval(uint64_t b)
{
    double d;
    memcpy(&d, &b, sizeof d);
    return d;
}

uint64_t vx_fcanon(double d)
{
    uint64_t b;
    if (d != d)
        return VX_NAN_BITS;
    if (d == 0.0)
        return 0;
    memcpy(&b, &d, sizeof b);
    return b;
}

static int finite_bits(uint64_t b)
{
    return ((b >> 52) & 2047u) != 2047u;
}

/* VFloat.toInt?: Floor, Ceil, Round (ties to even), Int (towards zero).
   Returns VX_OK with *out, or VX_FAIL (NaN, an infinity, out of range). */
int vx_ftoint(int mode, uint64_t b, int64_t *out)
{
    int neg = (int)(b >> 63);
    uint64_t ef = (b >> 52) & 2047u, mf = b & ((1ull << 52) - 1), m, q, rem = 0, half = 0;
    int e, exact, up;
    if (!finite_bits(b))
        return VX_FAIL;
    if (ef == 0) { m = mf; e = -1074; } else { m = mf | (1ull << 52); e = (int)ef - 1075; }
    if (e >= 0) {
        if (e >= 64 || (m != 0 && m > (UINT64_MAX >> e)))
            return VX_FAIL;
        q = m << e;
        exact = 1;
    } else {
        int s = -e;
        if (s >= 64) {
            q = 0;
            rem = m;
            exact = m == 0;
            half = 0;   /* (unused: rem < 2^53 < 2^(s-1)) */
        } else {
            q = m >> s;
            rem = m & ((1ull << s) - 1);
            exact = rem == 0;
            half = 1ull << (s - 1);
        }
    }
    if (mode == VX_FTRUNC)
        up = 0;
    else if (mode == VX_FFLOOR)
        up = neg && !exact;
    else if (mode == VX_FCEIL)
        up = !neg && !exact;
    else   /* VX_FROUND */
        up = !exact && e < 0 && -e < 64 && (rem > half || (rem == half && (q & 1u)));
    if (up) {
        if (q == UINT64_MAX)
            return VX_FAIL;
        q++;
    }
    if (neg) {
        if (q > (1ull << 63))
            return VX_FAIL;
        *out = q == (1ull << 63) ? INT64_MIN : -(int64_t)q;
    } else {
        if (q > (uint64_t)INT64_MAX)
            return VX_FAIL;
        *out = (int64_t)q;
    }
    return VX_OK;
}

/* VFloat.fixed6, ToString of a float (the Book's API: "Fixed point with
   exactly six digits after the decimal point, always"): NaN, Inf, -Inf, or
   C's "%.6f" of the double, which is its exact value rounded to a multiple of
   10^-6 in the current rounding mode (round to nearest, ties to even: Verse
   never changes it), every digit before the point, and a '-' whenever the
   double is negative.  Lean computes the same digits with integers.  out
   holds at least VX_FMT_MAX bytes (the longest result, -DBL_MAX, is 317);
   returns the length. */
size_t vx_fmt(uint64_t b, char *out)
{
    int len;
    if (b == VX_NAN_BITS) { strcpy(out, "NaN"); return 3; }
    if (!finite_bits(b)) {
        strcpy(out, (b >> 63) ? "-Inf" : "Inf");
        return strlen(out);
    }
    len = snprintf(out, VX_FMT_MAX, "%.6f", vx_fval(b));
    return len < 0 ? 0 : (size_t)len;
}
