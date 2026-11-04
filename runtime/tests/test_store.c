/*
 * test_store.c -- store.c: directed cases (nested marks, rollback of slots
 * and output, commit, the journal-full and bounds cases, forget, moving to
 * larger buffers) and a random model check against snapshots.
 */
#include "testlib.h"

#define NS 8

static vx_val slots[NS];
static vx_undo jour[64];
static uint8_t out[64];

static uint64_t val(const vx_store *s, size_t i)
{
    vx_val v;
    CHECK_EQ(vx_store_get(s, i, &v), VX_OK);
    return v.tag * 1000 + v.bits;
}

static void fill(vx_store *s)
{
    size_t i;
    for (i = 0; i < NS; i++)
        CHECK_EQ(vx_store_put(s, i, 0, i), VX_OK);
}

static void directed(void)
{
    vx_store s;
    vx_mark m1, m2, m3;
    vx_val v;
    size_t i;

    vx_store_init(&s, slots, NS, jour, 4, out, 8);
    fill(&s);
    CHECK_EQ(s.depth, 0);

    /* depth 0: writes are not logged */
    CHECK_EQ(vx_store_set(&s, 0, 1, 7), VX_OK);
    CHECK_EQ(vx_store_journal_len(&s), 0);
    CHECK_EQ(val(&s, 0), 1007);

    /* nested marks */
    CHECK_EQ(vx_store_out_append(&s, (const uint8_t *)"ab", 2), VX_OK);
    vx_store_mark(&s, &m1);                               /* depth 1 */
    CHECK_EQ(s.depth, 1);
    CHECK_EQ(vx_store_set(&s, 1, 2, 11), VX_OK);
    CHECK_EQ(vx_store_journal_len(&s), 1);
    CHECK_EQ(vx_store_out_append(&s, (const uint8_t *)"cd", 2), VX_OK);
    vx_store_mark(&s, &m2);                               /* depth 2 */
    CHECK_EQ(vx_store_set(&s, 2, 3, 22), VX_OK);
    CHECK_EQ(vx_store_set(&s, 1, 3, 33), VX_OK);          /* same slot again */
    CHECK_EQ(vx_store_out_append(&s, (const uint8_t *)"ef", 2), VX_OK);
    CHECK_EQ(vx_store_out_len(&s), 6);
    vx_store_rollback(&s, &m2);                           /* back to depth 1 */
    CHECK_EQ(s.depth, 1);
    CHECK_EQ(val(&s, 1), 2011);                           /* the write after m1 stays */
    CHECK_EQ(val(&s, 2), 2);                              /* restored */
    CHECK_EQ(vx_store_out_len(&s), 4);
    CHECK(memcmp(s.out, "abcd", 4) == 0);
    CHECK_EQ(vx_store_journal_len(&s), 1);

    /* an inner commit keeps its entries for the outer context */
    vx_store_mark(&s, &m2);
    CHECK_EQ(vx_store_set(&s, 3, 4, 44), VX_OK);
    vx_store_commit(&s, &m2);
    CHECK_EQ(s.depth, 1);
    CHECK_EQ(vx_store_journal_len(&s), 2);
    CHECK_EQ(val(&s, 3), 4044);
    /* ... so the outer rollback undoes it too */
    vx_store_rollback(&s, &m1);
    CHECK_EQ(s.depth, 0);
    CHECK_EQ(val(&s, 1), 1);
    CHECK_EQ(val(&s, 3), 3);
    CHECK_EQ(val(&s, 0), 1007);                           /* written before m1 */
    CHECK_EQ(vx_store_out_len(&s), 2);
    CHECK_EQ(vx_store_journal_len(&s), 0);

    /* the outermost commit clears the journal and keeps the effects */
    vx_store_mark(&s, &m1);
    CHECK_EQ(vx_store_set(&s, 4, 5, 55), VX_OK);
    CHECK_EQ(vx_store_out_append(&s, (const uint8_t *)"x", 1), VX_OK);
    vx_store_commit(&s, &m1);
    CHECK_EQ(s.depth, 0);
    CHECK_EQ(vx_store_journal_len(&s), 0);
    CHECK_EQ(val(&s, 4), 5055);
    CHECK_EQ(vx_store_out_len(&s), 3);

    /* journal full: VX_EFULL and nothing changes */
    vx_store_mark(&s, &m1);
    for (i = 0; i < 4; i++)
        CHECK_EQ(vx_store_set(&s, i, 6, 60 + i), VX_OK);
    CHECK_EQ(vx_store_set(&s, 5, 6, 65), VX_EFULL);
    CHECK_EQ(val(&s, 5), 5);
    CHECK_EQ(vx_store_journal_len(&s), 4);
    /* put never logs, even inside a context */
    CHECK_EQ(vx_store_put(&s, 6, 6, 66), VX_OK);
    CHECK_EQ(vx_store_journal_len(&s), 4);
    /* moving to a bigger journal keeps the entries; then the write succeeds */
    CHECK_EQ(vx_store_move_journal(&s, jour + 8, 2), VX_EFULL);   /* too small */
    CHECK_EQ(vx_store_move_journal(&s, jour + 8, 16), VX_OK);
    CHECK_EQ(vx_store_set(&s, 5, 6, 65), VX_OK);
    vx_store_rollback(&s, &m1);
    for (i = 0; i < 4; i++)
        CHECK(val(&s, i) == (i == 0 ? 1007 : i));
    CHECK_EQ(val(&s, 5), 5);
    CHECK_EQ(val(&s, 6), 6066);                           /* put is not undone */

    /* bounds */
    CHECK_EQ(vx_store_get(&s, NS, &v), VX_ESLOT);
    CHECK_EQ(vx_store_set(&s, NS, 0, 0), VX_ESLOT);
    CHECK_EQ(vx_store_put(&s, (size_t)-1, 0, 0), VX_ESLOT);

    /* output: all or nothing */
    CHECK_EQ(vx_store_out_len(&s), 3);
    CHECK_EQ(vx_store_out_append(&s, (const uint8_t *)"123456", 6), VX_EFULL);
    CHECK_EQ(vx_store_out_len(&s), 3);
    CHECK_EQ(vx_store_out_append(&s, (const uint8_t *)"12345", 5), VX_OK);
    CHECK_EQ(vx_store_out_len(&s), 8);
    CHECK_EQ(vx_store_out_append(&s, (const uint8_t *)"", 0), VX_OK);
    CHECK_EQ(vx_store_move_out(&s, out + 32, 4), VX_EFULL);
    CHECK_EQ(vx_store_move_out(&s, out + 32, 32), VX_OK);
    CHECK(memcmp(s.out, "abx12345", 8) == 0);
    CHECK_EQ(vx_store_out_append(&s, (const uint8_t *)"Z", 1), VX_OK);

    /* forget drops entries above a length, never below */
    vx_store_mark(&s, &m1);
    CHECK_EQ(vx_store_set(&s, 0, 7, 70), VX_OK);
    vx_store_mark(&s, &m2);
    CHECK_EQ(vx_store_set(&s, 1, 7, 71), VX_OK);
    CHECK_EQ(vx_store_set(&s, 2, 7, 72), VX_OK);
    vx_store_forget(&s, 1);
    CHECK_EQ(vx_store_journal_len(&s), 1);
    vx_store_forget(&s, 5);
    CHECK_EQ(vx_store_journal_len(&s), 1);
    vx_store_mark(&s, &m3);
    vx_store_rollback(&s, &m3);
    vx_store_rollback(&s, &m2);   /* nothing logged above m2 any more */
    CHECK_EQ(val(&s, 1), 7071);
    vx_store_rollback(&s, &m1);
    CHECK_EQ(val(&s, 0), 1007);
    CHECK_EQ(s.depth, 0);

    /* moving the slots keeps them */
    {
        vx_val big[2 * NS];
        CHECK_EQ(vx_store_move_slots(&s, big, NS - 1), VX_EFULL);
        CHECK_EQ(vx_store_move_slots(&s, big, 2 * NS), VX_OK);
        for (i = 0; i < NS; i++)
            CHECK_EQ(s.slots[i].bits, slots[i].bits);
        vx_store_init(&s, slots, NS, jour, 4, out, 8);   /* big goes out of scope */
    }
}

/* Random operations against a model that snapshots the state at each mark. */
#define MAXD 6
typedef struct {
    uint64_t slot[NS];
    size_t   olen;
} snap;

static uint64_t rs = 88172645463325252ull;
static uint64_t rnd(void)
{
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static void model(void)
{
    vx_store s;
    vx_mark marks[MAXD];
    snap snaps[MAXD];
    uint64_t cur[NS];
    static vx_undo bigj[1 << 12];
    static uint8_t bigo[1 << 14];
    size_t d = 0, i, olen = 0;
    int step;
    vx_store_init(&s, slots, NS, bigj, 1 << 12, bigo, 1 << 14);
    for (i = 0; i < NS; i++) {
        vx_store_put(&s, i, 9, i);
        cur[i] = i;
    }
    for (step = 0; step < 200000; step++) {
        unsigned op = (unsigned)(rnd() % 10);
        if (op < 4) {                                     /* set */
            size_t sl = (size_t)(rnd() % NS);
            uint64_t x = rnd() % 1000;
            int rc = vx_store_set(&s, sl, 9, x);
            if (rc == VX_EFULL) {   /* only when logging into a full journal; no change */
                CHECK(d > 0 && vx_store_journal_len(&s) == s.jcap);
                CHECK_EQ(s.slots[sl].bits, cur[sl]);
                continue;
            }
            CHECK_EQ(rc, VX_OK);
            cur[sl] = x;
        } else if (op < 6) {                              /* print */
            uint8_t b = (uint8_t)rnd();
            if (olen + 1 >= sizeof bigo) {
                continue;
            }
            CHECK_EQ(vx_store_out_append(&s, &b, 1), VX_OK);
            olen++;
        } else if (op < 8) {                              /* enter a context */
            if (d == MAXD)
                continue;
            vx_store_mark(&s, &marks[d]);
            memcpy(snaps[d].slot, cur, sizeof cur);
            snaps[d].olen = olen;
            d++;
        } else if (op == 8) {                             /* it fails */
            if (d == 0)
                continue;
            d--;
            vx_store_rollback(&s, &marks[d]);
            memcpy(cur, snaps[d].slot, sizeof cur);
            olen = snaps[d].olen;
        } else {                                          /* it succeeds */
            if (d == 0)
                continue;
            d--;
            vx_store_commit(&s, &marks[d]);
        }
        CHECK_EQ(s.depth, d);
        CHECK_EQ(vx_store_out_len(&s), olen);
        if (d == 0)
            CHECK_EQ(vx_store_journal_len(&s), 0);
        for (i = 0; i < NS; i++)
            if (s.slots[i].bits != cur[i] || s.slots[i].tag != 9) {
                CHECK(s.slots[i].bits == cur[i]);
                return;
            }
    }
}

int main(void)
{
    directed();
    model();
    return t_report("test_store");
}
