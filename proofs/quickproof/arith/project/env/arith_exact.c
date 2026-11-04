/* Value distributions for the native and interpreter runs of arith_exact (not part of any theorem).
 * Uniform 64-bit values almost never hit the cases the arithmetic distinguishes, so pick() draws
 * int64 values near 0, near INT64_MIN and INT64_MAX, near +-sqrt(2^63) (products at the overflow
 * boundary), powers of two, or uniformly. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

static int64_t env_sign(int64_t v) { return (quickproof_rnd() & 1) ? v : -v; }

static int64_t env_int64(void) {
    switch (quickproof_rnd() % 10) {
    case 8: return -1;
    case 9: return INT64_MIN;
    case 0: return (int64_t)(quickproof_rnd() % 7) - 3;
    case 1: return INT64_MAX - (int64_t)(quickproof_rnd() % 3);
    case 2: return INT64_MIN + (int64_t)(quickproof_rnd() % 3);
    case 3: return (int64_t)(quickproof_rnd() % 64) - 32;
    case 4: return env_sign(3037000498 + (int64_t)(quickproof_rnd() % 4));
    case 5: return env_sign((int64_t)1 << (quickproof_rnd() % 62));
    case 6: return env_sign((int64_t)(quickproof_rnd() >> 2));
    default: return (int64_t)quickproof_rnd();
    }
}

void nondet_bytes(uint8_t *buf, size_t n) {
    size_t i;
    if (n == 8) {
        uint64_t u = (uint64_t)env_int64();
        for (i = 0; i < 8; i++) buf[i] = (uint8_t)(u >> (8 * i));
        return;
    }
    for (i = 0; i < n; i++) buf[i] = (uint8_t)quickproof_rnd();
}
