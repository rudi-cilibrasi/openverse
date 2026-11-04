/*
 * test_arith.c -- arith.c against hand-written edge cases, and against an
 * independent reference in 128-bit arithmetic on every pair of a set of
 * edge values plus random pairs.
 */
#include "testlib.h"

typedef __int128 i128;

#define MIN INT64_MIN
#define MAX INT64_MAX

typedef int (*binop)(int64_t, int64_t, int64_t *);

/* Expect op(a, b) to give rc and, on VX_OK, the value v. */
static void expect2(const char *name, binop op, int64_t a, int64_t b, int rc, int64_t v)
{
    int64_t out = 12345;
    int got = op(a, b, &out);
    t_checks++;
    if (got != rc || (rc == VX_OK && out != v) || (rc != VX_OK && out != 12345)) {
        t_failures++;
        fprintf(stderr, "%s(%lld, %lld): rc %d value %lld, expected rc %d value %lld\n", name,
                (long long)a, (long long)b, got, (long long)out, rc, (long long)v);
    }
}

#define E2(op, a, b, rc, v) expect2(#op, op, a, b, rc, v)

static void hand_cases(void)
{
    int64_t z;
    /* add / sub at the edges */
    E2(vx_add, MAX, 0, VX_OK, MAX);
    E2(vx_add, MAX, 1, VX_OVERFLOW, 0);
    E2(vx_add, MIN, -1, VX_OVERFLOW, 0);
    E2(vx_add, MIN, MAX, VX_OK, -1);
    E2(vx_add, MAX, MIN, VX_OK, -1);
    E2(vx_add, MIN, 0, VX_OK, MIN);
    E2(vx_add, MAX, MAX, VX_OVERFLOW, 0);
    E2(vx_add, MIN, MIN, VX_OVERFLOW, 0);
    E2(vx_sub, MIN, 1, VX_OVERFLOW, 0);
    E2(vx_sub, MAX, -1, VX_OVERFLOW, 0);
    E2(vx_sub, 0, MIN, VX_OVERFLOW, 0);
    E2(vx_sub, -1, MIN, VX_OK, MAX);
    E2(vx_sub, MIN, MIN, VX_OK, 0);
    E2(vx_sub, 0, MAX, VX_OK, MIN + 1);
    /* mul */
    E2(vx_mul, MIN, -1, VX_OVERFLOW, 0);
    E2(vx_mul, -1, MIN, VX_OVERFLOW, 0);
    E2(vx_mul, MIN, 1, VX_OK, MIN);
    E2(vx_mul, MAX, -1, VX_OK, -MAX);
    E2(vx_mul, MIN, 0, VX_OK, 0);
    E2(vx_mul, 0, MIN, VX_OK, 0);
    E2(vx_mul, 3037000499LL, 3037000499LL, VX_OK, 9223372030926249001LL);
    E2(vx_mul, 3037000500LL, 3037000500LL, VX_OVERFLOW, 0);
    E2(vx_mul, -3037000500LL, 3037000500LL, VX_OVERFLOW, 0);
    E2(vx_mul, 4294967296LL, -2147483648LL, VX_OK, MIN);   /* 2^32 * -2^31 = -2^63 */
    E2(vx_mul, -4294967296LL, 2147483648LL, VX_OK, MIN);
    E2(vx_mul, 4294967296LL, 2147483648LL, VX_OVERFLOW, 0);
    E2(vx_mul, 2, MIN / 2, VX_OK, MIN);
    E2(vx_mul, -2, MIN / 2, VX_OVERFLOW, 0);
    E2(vx_mul, 1350851717672992089LL, 3, VX_OK, 4052555153018976267LL);  /* tests/core/overflow */
    E2(vx_mul, 4052555153018976267LL, 3, VX_OVERFLOW, 0);
    /* neg / abs */
    CHECK_EQ(vx_neg(MIN, &z), VX_OVERFLOW);
    CHECK(vx_neg(MAX, &z) == VX_OK && z == -MAX);
    CHECK(vx_neg(0, &z) == VX_OK && z == 0);
    CHECK_EQ(vx_abs(MIN, &z), VX_OVERFLOW);
    CHECK(vx_abs(MIN + 1, &z) == VX_OK && z == MAX);
    CHECK(vx_abs(-5, &z) == VX_OK && z == 5);
    CHECK(vx_abs(5, &z) == VX_OK && z == 5);
    /* division by zero fails, whatever the dividend */
    E2(vx_floordiv, 7, 0, VX_FAIL, 0);
    E2(vx_ceildiv, MIN, 0, VX_FAIL, 0);
    E2(vx_quotient, 0, 0, VX_FAIL, 0);
    E2(vx_modulo, MAX, 0, VX_FAIL, 0);
    /* floor / ceil, all four sign combinations */
    E2(vx_floordiv, 7, 2, VX_OK, 3);
    E2(vx_floordiv, -7, 2, VX_OK, -4);
    E2(vx_floordiv, 7, -2, VX_OK, -4);
    E2(vx_floordiv, -7, -2, VX_OK, 3);
    E2(vx_ceildiv, 7, 2, VX_OK, 4);
    E2(vx_ceildiv, -7, 2, VX_OK, -3);
    E2(vx_ceildiv, 7, -2, VX_OK, -3);
    E2(vx_ceildiv, -7, -2, VX_OK, 4);
    E2(vx_floordiv, 6, 3, VX_OK, 2);
    E2(vx_ceildiv, -6, 3, VX_OK, -2);
    /* Euclidean: 0 <= r < |b|, a = b q + r */
    E2(vx_quotient, 7, 2, VX_OK, 3);
    E2(vx_modulo, 7, 2, VX_OK, 1);
    E2(vx_quotient, -7, 2, VX_OK, -4);   /* Quotient[-7, 2] = -4 (Book of Verse) */
    E2(vx_modulo, -7, 2, VX_OK, 1);
    E2(vx_quotient, 7, -2, VX_OK, -3);
    E2(vx_modulo, 7, -2, VX_OK, 1);
    E2(vx_quotient, -7, -2, VX_OK, 4);
    E2(vx_modulo, -7, -2, VX_OK, 1);
    E2(vx_quotient, -6, -2, VX_OK, 3);
    E2(vx_modulo, -6, -2, VX_OK, 0);
    /* INT64_MIN / -1 and friends */
    E2(vx_floordiv, MIN, -1, VX_OVERFLOW, 0);
    E2(vx_ceildiv, MIN, -1, VX_OVERFLOW, 0);
    E2(vx_quotient, MIN, -1, VX_OVERFLOW, 0);
    E2(vx_modulo, MIN, -1, VX_OK, 0);     /* emod is 0: no overflow */
    E2(vx_floordiv, MIN, 1, VX_OK, MIN);
    E2(vx_ceildiv, MIN, 1, VX_OK, MIN);
    E2(vx_floordiv, MAX, -1, VX_OK, -MAX);
    E2(vx_floordiv, MIN, 2, VX_OK, MIN / 2);
    E2(vx_floordiv, MIN, -2, VX_OK, -(MIN / 2));
    E2(vx_floordiv, MIN + 1, -2, VX_OK, 4611686018427387903LL);   /* (2^63-1)/2 floored */
    E2(vx_ceildiv, MIN + 1, -2, VX_OK, 4611686018427387904LL);
    E2(vx_floordiv, MIN, MIN, VX_OK, 1);
    E2(vx_floordiv, MAX, MIN, VX_OK, -1);
    E2(vx_ceildiv, MAX, MIN, VX_OK, 0);
    E2(vx_floordiv, -1, MIN, VX_OK, 0);
    E2(vx_ceildiv, -1, MIN, VX_OK, 1);
    E2(vx_quotient, MIN, MIN, VX_OK, 1);
    E2(vx_modulo, MIN, MIN, VX_OK, 0);
    E2(vx_quotient, -1, MIN, VX_OK, 1);    /* -1 = MIN * 1 + (2^63 - 1) */
    E2(vx_modulo, -1, MIN, VX_OK, MAX);
    E2(vx_quotient, MAX, MIN, VX_OK, 0);
    E2(vx_modulo, MAX, MIN, VX_OK, MAX);
    E2(vx_quotient, MIN, MAX, VX_OK, -2);  /* MIN = MAX * -2 + (2^63 - 2) */
    E2(vx_modulo, MIN, MAX, VX_OK, MAX - 1);
    E2(vx_modulo, MIN, 2, VX_OK, 0);
    E2(vx_modulo, MIN + 1, 2, VX_OK, 1);
    E2(vx_quotient, MIN + 1, 2, VX_OK, MIN / 2);
}

/* ------------------------------------------------- 128-bit reference */

static int ref_range(i128 x, int64_t *out)
{
    if (x < (i128)MIN || x > (i128)MAX)
        return VX_OVERFLOW;
    *out = (int64_t)x;
    return VX_OK;
}

static i128 r_floor(i128 a, i128 b)
{
    i128 q = a / b, r = a % b;
    return (r != 0 && ((r < 0) != (b < 0))) ? q - 1 : q;
}
static i128 r_ediv(i128 a, i128 b)
{
    i128 q = a / b, r = a % b;
    if (r < 0)
        q = b > 0 ? q - 1 : q + 1;
    return q;
}

static int ref(int op, int64_t a, int64_t b, int64_t *out)
{
    i128 A = a, B = b;
    switch (op) {
    case 0: return ref_range(A + B, out);
    case 1: return ref_range(A - B, out);
    case 2: return ref_range(A * B, out);
    case 3: return b == 0 ? VX_FAIL : ref_range(r_floor(A, B), out);
    case 4: return b == 0 ? VX_FAIL : ref_range(-r_floor(-A, B), out);   /* ceilDivInt */
    case 5: return b == 0 ? VX_FAIL : ref_range(r_ediv(A, B), out);
    default: return b == 0 ? VX_FAIL : ref_range(A - B * r_ediv(A, B), out);
    }
}

static const binop ops[] = { vx_add, vx_sub, vx_mul, vx_floordiv, vx_ceildiv, vx_quotient, vx_modulo };
static const char *const opnames[] = { "add", "sub", "mul", "floordiv", "ceildiv", "quotient", "modulo" };

static void compare(int op, int64_t a, int64_t b)
{
    int64_t want = 0, got = 0;
    int rw = ref(op, a, b, &want), rg = ops[op](a, b, &got);
    t_checks++;
    if (rw != rg || (rw == VX_OK && want != got)) {
        t_failures++;
        fprintf(stderr, "%s(%lld, %lld): got rc %d value %lld, reference rc %d value %lld\n",
                opnames[op], (long long)a, (long long)b, rg, (long long)got, rw, (long long)want);
    }
    if (rw == VX_OK && (op == 6)) {   /* Euclidean remainder: 0 <= r < |b| */
        i128 absb = b < 0 ? -(i128)b : (i128)b;
        CHECK(got >= 0 && (i128)got < absb);
    }
}

static uint64_t rng = 0x9e3779b97f4a7c15ull;
static uint64_t next(void)
{
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    return rng;
}

static void reference_cases(void)
{
    static const int64_t edge[] = {
        MIN, MIN + 1, MIN + 2, MIN / 2, MIN / 2 + 1, -4294967296LL, -3037000500LL, -3037000499LL,
        -10, -7, -3, -2, -1, 0, 1, 2, 3, 7, 10, 3037000499LL, 3037000500LL, 4294967296LL,
        MAX / 2, MAX / 2 + 1, MAX - 2, MAX - 1, MAX,
    };
    size_t ne = sizeof edge / sizeof edge[0], i, j;
    int op, k;
    int64_t z, w;
    for (op = 0; op < 7; op++)
        for (i = 0; i < ne; i++)
            for (j = 0; j < ne; j++)
                compare(op, edge[i], edge[j]);
    for (k = 0; k < 200000; k++) {
        uint64_t x = next(), y = next();
        int64_t a = (int64_t)x, b = (int64_t)y;
        /* small, medium and full-width operands */
        if (k % 3 == 1) { a >>= 32; b >>= 32; }
        if (k % 3 == 2) { a >>= 56; b >>= 60; }
        compare(k % 7, a, b);
    }
    /* neg and abs against the reference */
    for (i = 0; i < ne; i++) {
        int rn = vx_neg(edge[i], &z), ra = vx_abs(edge[i], &w);
        CHECK(rn == (edge[i] == MIN ? VX_OVERFLOW : VX_OK));
        CHECK(rn != VX_OK || z == -edge[i]);
        CHECK(ra == (edge[i] == MIN ? VX_OVERFLOW : VX_OK));
        CHECK(ra != VX_OK || w == (edge[i] < 0 ? -edge[i] : edge[i]));
    }
}

int main(void)
{
    hand_cases();
    reference_cases();
    return t_report("test_arith");
}
