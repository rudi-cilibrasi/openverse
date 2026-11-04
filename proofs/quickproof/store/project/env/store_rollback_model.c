/* Value distributions for the native and interpreter runs of store_rollback_model (not part of any
 * theorem): small sizes (so that the assumes pass and the journal and output fill up), an operation
 * mix that often nests contexts, slot indices around the valid range, and arbitrary values. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

size_t nondet_size(void) { return (size_t)(1 + quickproof_rnd() % 5); }   /* sizes and indices 1..5 */
/* operations: mark 25%, set 30%, append 10%, rollback 15%, commit 15%, no-op 5% */
uint8_t nondet_u8(void) {
    uint64_t r = quickproof_rnd() % 20;
    if (r < 5) return 0;
    if (r < 11) return 1;
    if (r < 13) return 2;
    if (r < 16) return 3;
    if (r < 19) return 4;
    return (uint8_t)(5 + quickproof_rnd() % 251);
}
uint32_t nondet_u32(void) { return (uint32_t)quickproof_rnd(); }
void nondet_bytes(uint8_t *buf, size_t n) {
    size_t i;
    for (i = 0; i < n; i++) buf[i] = (uint8_t)quickproof_rnd();
}
