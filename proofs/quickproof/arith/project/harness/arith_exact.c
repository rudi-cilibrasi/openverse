/* Law arith_exact.
 *
 * For every pair of 64-bit ints a and b, each of the nine int operations of the C runtime
 * (runtime/src/arith.c) returns exactly the Verse result defined by Prim.apply in
 * OpenVerse/Core/Prims.lean:
 *
 *   - vx_add, vx_sub, vx_mul, vx_neg, vx_abs return VX_OK and the exact result when it fits
 *     in 64 bits, and otherwise VX_OVERFLOW without writing *out;
 *   - vx_floordiv, vx_ceildiv, vx_quotient and vx_modulo return VX_FAIL without writing *out
 *     when b == 0 (a Verse failure, not an error), and otherwise VX_OK and the floor, ceiling,
 *     Euclidean quotient and Euclidean remainder of a / b, or VX_OVERFLOW without writing
 *     *out when that does not fit.
 *
 * The conditions and results are written below with C99's truncating / and %. Each helper
 * has a namesake in OpenVerse/Core/Seams.lean (add_fits = cAddFits, sub_fits = cSubFits,
 * mul_fits = cMulFits, c_floordiv = cFloorDiv, c_ceildiv = cCeilDiv, c_quotient = cQuotient,
 * c_modulo = cModulo, a != INT64_MIN = cNegFits), and Seams.lean proves in Lean that each is
 * the Lean definition (add_seam, ..., modulo_seam; apply_add, ..., apply_modulo).
 *
 * C's / and % are undefined for (INT64_MIN, -1) only. There the exact results are 2^63 for
 * floor, ceiling and quotient (overflow) and 0 for the remainder; Seams.lean checks these
 * four values (apply_min_neg_one).
 */
#include <stdint.h>
#include "quickproof.h"
#include "openverse.h"

#define UNTOUCHED 12345

static int add_fits(int64_t a, int64_t b) {
    if (b >= 0) return a <= INT64_MAX - b;
    return a >= INT64_MIN - b;
}

static int sub_fits(int64_t a, int64_t b) {
    if (b >= 0) return a >= INT64_MIN + b;
    return a <= INT64_MAX + b;
}

static int mul_fits(int64_t a, int64_t b) {
    if (b == 0) return 1;
    if (b == -1) return a != INT64_MIN;
    if (b > 0) return INT64_MIN / b <= a && a <= INT64_MAX / b;
    return INT64_MAX / b <= a && a <= INT64_MIN / b;
}

/* The four divisions for b != 0 and (a, b) != (INT64_MIN, -1). */
static int64_t c_floordiv(int64_t a, int64_t b) {
    int64_t q = a / b;
    int64_t r = a % b;
    if (r != 0 && ((r < 0) != (b < 0))) return q - 1;
    return q;
}

static int64_t c_ceildiv(int64_t a, int64_t b) {
    int64_t q = a / b;
    int64_t r = a % b;
    if (r != 0 && ((r < 0) == (b < 0))) return q + 1;
    return q;
}

static int64_t c_quotient(int64_t a, int64_t b) {
    int64_t q = a / b;
    int64_t r = a % b;
    if (r < 0) {
        if (b > 0) return q - 1;
        return q + 1;
    }
    return q;
}

static int64_t c_modulo(int64_t a, int64_t b) {
    int64_t r = a % b;
    if (r < 0) {
        if (b > 0) return r + b;
        return r - b;
    }
    return r;
}

int main(void) {
    int64_t a;
    int64_t b;
    int64_t r;
    int st;
    pick(a);
    pick(b);

    r = UNTOUCHED; st = vx_add(a, b, &r);
    if (add_fits(a, b)) { qp_assert(st == VX_OK); qp_assert(r == a + b); }
    else { qp_assert(st == VX_OVERFLOW); qp_assert(r == UNTOUCHED); }

    r = UNTOUCHED; st = vx_sub(a, b, &r);
    if (sub_fits(a, b)) { qp_assert(st == VX_OK); qp_assert(r == a - b); }
    else { qp_assert(st == VX_OVERFLOW); qp_assert(r == UNTOUCHED); }

    r = UNTOUCHED; st = vx_mul(a, b, &r);
    if (mul_fits(a, b)) { qp_assert(st == VX_OK); qp_assert(r == a * b); }
    else { qp_assert(st == VX_OVERFLOW); qp_assert(r == UNTOUCHED); }

    r = UNTOUCHED; st = vx_neg(a, &r);
    if (a != INT64_MIN) { qp_assert(st == VX_OK); qp_assert(r == -a); }
    else { qp_assert(st == VX_OVERFLOW); qp_assert(r == UNTOUCHED); }

    r = UNTOUCHED; st = vx_abs(a, &r);
    if (a != INT64_MIN) { qp_assert(st == VX_OK); qp_assert(r == (a < 0 ? -a : a)); }
    else { qp_assert(st == VX_OVERFLOW); qp_assert(r == UNTOUCHED); }

    r = UNTOUCHED; st = vx_floordiv(a, b, &r);
    if (b == 0) { qp_assert(st == VX_FAIL); qp_assert(r == UNTOUCHED); }
    else if (a == INT64_MIN && b == -1) { qp_assert(st == VX_OVERFLOW); qp_assert(r == UNTOUCHED); }
    else { qp_assert(st == VX_OK); qp_assert(r == c_floordiv(a, b)); }

    r = UNTOUCHED; st = vx_ceildiv(a, b, &r);
    if (b == 0) { qp_assert(st == VX_FAIL); qp_assert(r == UNTOUCHED); }
    else if (a == INT64_MIN && b == -1) { qp_assert(st == VX_OVERFLOW); qp_assert(r == UNTOUCHED); }
    else { qp_assert(st == VX_OK); qp_assert(r == c_ceildiv(a, b)); }

    r = UNTOUCHED; st = vx_quotient(a, b, &r);
    if (b == 0) { qp_assert(st == VX_FAIL); qp_assert(r == UNTOUCHED); }
    else if (a == INT64_MIN && b == -1) { qp_assert(st == VX_OVERFLOW); qp_assert(r == UNTOUCHED); }
    else { qp_assert(st == VX_OK); qp_assert(r == c_quotient(a, b)); }

    r = UNTOUCHED; st = vx_modulo(a, b, &r);
    if (b == 0) { qp_assert(st == VX_FAIL); qp_assert(r == UNTOUCHED); }
    else if (a == INT64_MIN && b == -1) { qp_assert(st == VX_OK); qp_assert(r == 0); }
    else { qp_assert(st == VX_OK); qp_assert(r == c_modulo(a, b)); }

    return 0;
}
