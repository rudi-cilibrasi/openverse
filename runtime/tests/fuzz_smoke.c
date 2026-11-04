/*
 * fuzz_smoke.c N SEED FILE.vbc... -- mutation fuzz smoke test.
 *
 * Makes N mutants of the given OVBC files (bit flips, byte and word
 * overwrites with boundary values, insertions, deletions, truncations,
 * chunk copies), half of them from earlier accepted mutants, loads each
 * from an exact-size buffer and runs every accepted one with small limits.  Built with ASan + UBSan (and
 * -fno-sanitize-recover), so any memory error, leak or undefined behaviour
 * aborts the run.  Also checks that the outcome is one of the kinds the
 * exit protocol knows.
 */
#include "testlib.h"

static uint64_t rs;
static uint64_t rnd(void)
{
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static size_t below(size_t n) { return n ? (size_t)(rnd() % n) : 0; }

static const uint32_t words[] = { 0, 1, 2, 3, 4, 5, 7, 8, 11, 12, 16, 24, 25, 28, 29,
                                  255, 256, 65535, 65536, 0x7fffffffu, 0x80000000u, 0xffffffffu };
static const int64_t longs[] = { 0, 1, -1, 2, -2, INT64_MAX, INT64_MIN, INT64_MAX - 1, INT64_MIN + 1,
                                 1000000000000000000LL, 3037000500LL, 4294967296LL };

/* Mutate b[0..*n) in place (capacity cap). */
static void mutate(uint8_t *b, size_t *n, size_t cap)
{
    size_t i, j, k, len;
    switch (rnd() % 10) {
    case 0: /* flip a bit */
        if (*n) b[below(*n)] ^= (uint8_t)(1u << (rnd() % 8));
        break;
    case 1: /* random byte */
        if (*n) b[below(*n)] = (uint8_t)rnd();
        break;
    case 2: /* small byte: tags, codes, kinds */
        if (*n) b[below(*n)] = (uint8_t)(rnd() % 32);
        break;
    case 3: /* boundary u32 */
        if (*n >= 4) {
            uint32_t w = words[below(sizeof words / sizeof words[0])];
            i = below(*n - 3);
            for (k = 0; k < 4; k++) b[i + k] = (uint8_t)(w >> (8 * k));
        }
        break;
    case 4: /* boundary i64 */
        if (*n >= 8) {
            uint64_t w = (uint64_t)longs[below(sizeof longs / sizeof longs[0])];
            i = below(*n - 7);
            for (k = 0; k < 8; k++) b[i + k] = (uint8_t)(w >> (8 * k));
        }
        break;
    case 5: /* insert a byte */
        if (*n < cap) {
            i = below(*n + 1);
            memmove(b + i + 1, b + i, *n - i);
            b[i] = (uint8_t)rnd();
            (*n)++;
        }
        break;
    case 6: /* delete a byte */
        if (*n) {
            i = below(*n);
            memmove(b + i, b + i + 1, *n - i - 1);
            (*n)--;
        }
        break;
    case 7: /* truncate */
        *n = below(*n + 1);
        break;
    case 8: /* copy a chunk over another place */
        if (*n >= 2) {
            i = below(*n);
            j = below(*n);
            len = 1 + below(16);
            if (i + len > *n) len = *n - i;
            if (j + len > *n) len = *n - j;
            memmove(b + j, b + i, len);
        }
        break;
    default: /* small u32 at a 4-aligned offset after the header (indices) */
        if (*n >= 20) {
            uint32_t w = (uint32_t)(rnd() % 8);
            i = 16 + 4 * below((*n - 16) / 4);
            if (i + 4 <= *n)
                for (k = 0; k < 4; k++) b[i + k] = (uint8_t)(w >> (8 * k));
        }
        break;
    }
}

#define MAXCORPUS 256
static uint8_t *corpus[MAXCORPUS];
static size_t corpus_len[MAXCORPUS], ncorpus;

int main(int argc, char **argv)
{
    int nfiles, f, it, n;
    uint8_t *file[16];
    size_t flen[16];
    long accepted = 0, kinds[6] = { 0 }, loadrc[VX_LOAD_LAST + 1] = { 0 };
    if (argc < 4) {
        fprintf(stderr, "usage: fuzz_smoke N SEED FILE.vbc...\n");
        return 2;
    }
    n = atoi(argv[1]);
    rs = 0x2545F4914F6CDD1Dull ^ ((uint64_t)strtoull(argv[2], NULL, 10) * 0x9E3779B97F4A7C15ull);
    if (rs == 0)
        rs = 1;
    nfiles = argc - 3 > 16 ? 16 : argc - 3;
    for (f = 0; f < nfiles; f++) {
        file[f] = t_read_file(argv[3 + f], &flen[f]);
        if (file[f] == NULL) {
            fprintf(stderr, "cannot read %s\n", argv[3 + f]);
            return 2;
        }
    }
    for (it = 0; it < n; it++) {
        size_t cap, len, m, nm, srclen;
        uint8_t *b, *exact;
        const uint8_t *src;
        vx_program p;
        int rc;
        /* half the time, mutate further a mutant that was accepted */
        if (ncorpus > 0 && rnd() % 2 == 0) {
            size_t c = below(ncorpus);
            src = corpus[c];
            srclen = corpus_len[c];
        } else {
            f = (int)below((size_t)nfiles);
            src = file[f];
            srclen = flen[f];
        }
        cap = srclen + 64;
        b = malloc(cap);
        memcpy(b, src, srclen);
        len = srclen;
        nm = rnd() % 4 == 0 ? 2 + below(3) : 1;
        for (m = 0; m < nm; m++)
            mutate(b, &len, cap);
        exact = malloc(len ? len : 1);
        memcpy(exact, b, len);
        free(b);
        rc = vx_load(exact, len, &p);
        if (rc == VX_LOAD_OK && len > 0) {   /* keep it for further mutation */
            size_t slot = ncorpus < MAXCORPUS ? ncorpus++ : below(MAXCORPUS);
            if (slot < ncorpus && corpus[slot] != NULL)
                free(corpus[slot]);
            corpus[slot] = exact;
            corpus_len[slot] = len;
        } else {
            free(exact);
        }
        if (rc < 0 || rc > VX_LOAD_LAST) {
            fprintf(stderr, "mutant %d: bad load code %d\n", it, rc);
            return 1;
        }
        loadrc[rc]++;
        if (rc == VX_LOAD_OK) {
            vx_opts o;
            vx_outcome r;
            vx_default_opts(&o);
            o.fuel = 2000;
            o.max_steps = 200000;
            o.max_depth = 1000;
            o.max_heap = (size_t)1 << 20;
            o.max_slots = (size_t)1 << 16;
            o.max_journal = (size_t)1 << 16;
            o.max_out = (size_t)1 << 20;
            o.max_vstack = (size_t)1 << 16;
            vx_run(&p, &o, &r);
            if (r.kind < 0 || r.kind > VX_R_LIMIT || r.kind == VX_R_BRK || r.kind == VX_R_RET) {
                fprintf(stderr, "mutant %d: outcome kind %d escaped retOf\n", it, r.kind);
                return 1;
            }
            kinds[r.kind]++;
            vx_outcome_free(&r);
            accepted++;
        }
        vx_free_program(&p);
    }
    for (f = 0; f < nfiles; f++)
        free(file[f]);
    for (f = 0; f < (int)ncorpus; f++)
        free(corpus[f]);
    printf("fuzz_smoke: %d mutants, %ld accepted and run: ok %ld, fail %ld, error %ld, limit %ld\n",
           n, accepted, kinds[VX_R_OK], kinds[VX_R_FAIL], kinds[VX_R_ERR], kinds[VX_R_LIMIT]);
    printf("fuzz_smoke: rejections:");
    for (f = 1; f <= VX_LOAD_LAST; f++)
        if (loadrc[f])
            printf(" %s=%ld", vx_load_reason(f), loadrc[f]);
    printf("\n");
    return 0;
}
