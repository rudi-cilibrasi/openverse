/*
 * floats.c -- floats (#127), as OpenVerse/Core/Float.lean defines them.
 *
 * A float value holds the bits of a canonical IEEE double: one NaN, and +0
 * for -0 (vx_fcanon).  The conversions to int (vx_ftoint) and the decimal
 * rendering (vx_fmt) work from the bits; the rendering is the shortest
 * decimal that reads back as the double (the closest of the shortest), in
 * Python's repr layout.  Lean computes the same thing exactly with integers;
 * here the digits come from printf's correctly rounded "%.*e" and are
 * checked with strtod's correctly rounded reading.
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

/* The digits (no trailing zeros) and the decimal point position of a
   positive finite double: d = 0.digits * 10^decpt. */
static void shortest(double d, char *digits, int *decpt)
{
    char buf[40];
    int p;
    for (p = 1; p <= 17; p++) {
        uint64_t D = 0;
        int x = 0, nd = 0, q;
        const char *s;
        snprintf(buf, sizeof buf, "%.*e", p - 1, d);
        /* the digits D and the exponent x of "d.ddde±x" */
        for (s = buf; *s != 'e'; s++)
            if (*s >= '0' && *s <= '9') { D = D * 10 + (uint64_t)(*s - '0'); nd++; }
        x = atoi(s + 1);
        q = x - nd + 1;
        if (strtod(buf, NULL) != d) {
            /* the neighbour on the other side of d */
            uint64_t D2 = strtod(buf, NULL) < d ? D + 1 : D - 1;
            char nb[40];
            if (D2 == 0)
                continue;
            snprintf(nb, sizeof nb, "%llue%d", (unsigned long long)D2, q);
            if (strtod(nb, NULL) != d)
                continue;
            D = D2;
        }
        /* strip the trailing zeros */
        while (D != 0 && D % 10 == 0) { D /= 10; q++; }
        snprintf(digits, 24, "%llu", (unsigned long long)D);
        *decpt = (int)strlen(digits) + q;
        return;
    }
    /* (17 digits always suffice) */
    snprintf(buf, sizeof buf, "%.16e", d);
    {
        uint64_t D = 0;
        int nd = 0, x, q;
        const char *s;
        for (s = buf; *s != 'e'; s++)
            if (*s >= '0' && *s <= '9') { D = D * 10 + (uint64_t)(*s - '0'); nd++; }
        x = atoi(s + 1);
        q = x - nd + 1;
        while (D != 0 && D % 10 == 0) { D /= 10; q++; }
        snprintf(digits, 24, "%llu", (unsigned long long)D);
        *decpt = (int)strlen(digits) + q;
    }
}

/* VFloat.render, into out (at least 40 bytes); returns the length. */
size_t vx_fmt(uint64_t b, char *out)
{
    char ds[24];
    int decpt, n, k;
    size_t len = 0;
    double d;
    if (b == VX_NAN_BITS) { strcpy(out, "NaN"); return 3; }
    if (!finite_bits(b)) {
        strcpy(out, (b >> 63) ? "-Inf" : "Inf");
        return strlen(out);
    }
    if (b == 0) { strcpy(out, "0.0"); return 3; }
    d = vx_fval(b);
    if (d < 0) { out[len++] = '-'; d = -d; }
    shortest(d, ds, &decpt);
    n = (int)strlen(ds);
    if (decpt <= -4 || decpt > 16) {
        int x = decpt - 1;
        out[len++] = ds[0];
        if (n > 1) {
            out[len++] = '.';
            for (k = 1; k < n; k++) out[len++] = ds[k];
        }
        len += (size_t)sprintf(out + len, "e%c%02d", x < 0 ? '-' : '+', x < 0 ? -x : x);
    } else if (decpt <= 0) {
        out[len++] = '0';
        out[len++] = '.';
        for (k = 0; k < -decpt; k++) out[len++] = '0';
        for (k = 0; k < n; k++) out[len++] = ds[k];
    } else if (decpt >= n) {
        for (k = 0; k < n; k++) out[len++] = ds[k];
        for (k = 0; k < decpt - n; k++) out[len++] = '0';
        out[len++] = '.';
        out[len++] = '0';
    } else {
        for (k = 0; k < decpt; k++) out[len++] = ds[k];
        out[len++] = '.';
        for (k = decpt; k < n; k++) out[len++] = ds[k];
    }
    out[len] = 0;
    return len;
}
