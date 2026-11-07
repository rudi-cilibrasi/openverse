/*
 * test_load.c COREDIR -- load.c:
 *   - the sample programs are accepted, with the expected tables;
 *   - every proper prefix and every extension by a byte is rejected;
 *   - each acceptance condition of FORMAT.md, violated alone, is rejected
 *     with its reason, and the limits are enforced;
 *   - over single-byte mutations of the samples, every accepted program
 *     satisfies conditions 1-7 as re-checked by an independent checker.
 */
#include "testlib.h"

static const char *const samples[] = { "fib", "rollback", "for", "overflow", "decides" };
#define NSAMPLES 5

/* Conditions 1-7 on a loaded program, checked independently of load.c. */
static int wellscoped(const vx_program *p)
{
    uint32_t f, j, k;
    if (p->nfns < 1 || p->entry >= p->nfns || p->fns == NULL)
        return 0;
    for (f = 0; f < p->nfns; f++) {
        const vx_fn *fn = &p->fns[f];
        if (fn->arity > fn->nslots || fn->nnodes < 1 || fn->root >= fn->nnodes)
            return 0;
        if (fn->nslots > VX_MAX_SLOTS || fn->nnodes > VX_MAX_NODES)
            return 0;
        if ((uint64_t)fn->name_off + fn->name_len > p->nbytes)
            return 0;
        for (j = 0; j < fn->nnodes; j++) {
            const vx_node *nd = &fn->nodes[j];
            switch (nd->tag) {
            case VX_N_LIT:
                if (nd->op > VX_LIT_LAST)
                    return 0;
                if (nd->op == VX_LIT_LOGIC && (nd->lit < 0 || nd->lit > 1))
                    return 0;
                if (nd->op == VX_LIT_CHAR && (nd->lit < 0 || nd->lit > 255))
                    return 0;
                if (nd->op == VX_LIT_STR && (uint64_t)nd->a + nd->b > p->nbytes)
                    return 0;
                break;
            case VX_N_LOCAL:
                if (nd->a >= fn->nslots)
                    return 0;
                break;
            case VX_N_ASSIGN:
                if (nd->a >= fn->nslots || nd->b >= j)
                    return 0;
                break;
            case VX_N_SEQ:
                if (nd->a >= j || nd->b >= j)
                    return 0;
                break;
            case VX_N_PRIM:
            case VX_N_CALL:
                if ((uint64_t)nd->c + nd->b > p->nargs || nd->b > VX_MAX_ARGS)
                    return 0;
                for (k = 0; k < nd->b; k++)
                    if (p->args[nd->c + k] >= j)
                        return 0;
                if (nd->tag == VX_N_PRIM &&
                    (nd->op > VX_P_LAST || (nd->a != 0 && nd->op != VX_P_TUPGET)))
                    return 0;
                if (nd->tag == VX_N_CALL &&
                    (nd->a >= p->nfns || p->fns[nd->a].arity != nd->b))
                    return 0;
                break;
            case VX_N_ITE:
                if (nd->a >= j || nd->b >= j || nd->c >= j)
                    return 0;
                break;
            case VX_N_FOR:
                if (nd->a >= fn->nslots || nd->b >= j || nd->c >= j || nd->d >= j)
                    return 0;
                break;
            case VX_N_LOOP:
            case VX_N_RET:
            case VX_N_PRINT:
                if (nd->a >= j)
                    return 0;
                break;
            case VX_N_BRK:
                break;
            case VX_N_HEAP:
                if ((uint64_t)nd->c + nd->b > p->nargs || nd->b > VX_MAX_ARGS)
                    return 0;
                for (k = 0; k < nd->b; k++)
                    if (p->args[nd->c + k] >= j)
                        return 0;
                if (nd->op > VX_H_LAST || (nd->op == VX_H_TAG && nd->a != 0))
                    return 0;
                if (nd->op == VX_H_ISTAG && (uint64_t)nd->a + 4 * (uint64_t)nd->d > p->nbytes)
                    return 0;
                if (nd->op != VX_H_ISTAG && nd->d != 0)
                    return 0;
                break;
            default:
                return 0;
            }
        }
    }
    return 1;
}

static int is_empty(const vx_program *p)
{
    return p->nfns == 0 && p->entry == 0 && p->fns == NULL && p->args == NULL &&
           p->nargs == 0 && p->bytes == NULL && p->nbytes == 0;
}

/* Load and return the code; check the post-conditions either way. */
static int load(const uint8_t *b, size_t n)
{
    vx_program p;
    int rc = vx_load(b, n, &p);
    if (rc == VX_LOAD_OK)
        CHECK(wellscoped(&p));
    else
        CHECK(is_empty(&p));
    vx_free_program(&p);
    CHECK(is_empty(&p));
    return rc;
}

static uint8_t *sample[NSAMPLES];
static size_t sample_len[NSAMPLES];

static void samples_accepted(const char *dir)
{
    char path[1024];
    int s;
    vx_program p;
    for (s = 0; s < NSAMPLES; s++) {
        snprintf(path, sizeof path, "%s/%s.vbc", dir, samples[s]);
        sample[s] = t_read_file(path, &sample_len[s]);
        if (sample[s] == NULL) {
            fprintf(stderr, "cannot read %s\n", path);
            exit(1);
        }
        CHECK_EQ(load(sample[s], sample_len[s]), VX_LOAD_OK);
    }
    /* fib: Fib(N) = if (N <= 1) then N else Fib(N-1) + Fib(N-2); Main = Print("{Fib(20)}") */
    CHECK_EQ(vx_load(sample[0], sample_len[0], &p), VX_LOAD_OK);
    CHECK_EQ(p.nfns, 2);
    CHECK_EQ(p.entry, 1);
    CHECK(p.fns[0].arity == 1 && p.fns[0].nslots == 1 && p.fns[0].decides == 0);
    CHECK(p.fns[0].name_len == 3 && memcmp(p.bytes + p.fns[0].name_off, "Fib", 3) == 0);
    CHECK(p.fns[1].arity == 0 && p.fns[1].nslots == 0);
    CHECK(p.fns[1].name_len == 4 && memcmp(p.bytes + p.fns[1].name_off, "Main", 4) == 0);
    CHECK_EQ(p.fns[0].nodes[p.fns[0].root].tag, VX_N_ITE);
    CHECK_EQ(p.fns[1].nodes[p.fns[1].root].tag, VX_N_PRINT);
    CHECK_EQ(p.nbytes, 7);   /* the two names, no string literals */
    vx_free_program(&p);
    /* decides: Half is <decides> */
    CHECK_EQ(vx_load(sample[4], sample_len[4], &p), VX_LOAD_OK);
    CHECK(p.fns[0].decides == 1 && p.fns[1].decides == 0);
    vx_free_program(&p);
}

static void prefixes_and_trailing(void)
{
    int s;
    size_t n;
    for (s = 0; s < NSAMPLES; s++) {
        uint8_t *b = malloc(sample_len[s] + 1);
        for (n = 0; n < sample_len[s]; n++) {
            /* an exact-size copy, so ASan sees any read past the end */
            uint8_t *pre = malloc(n ? n : 1);
            memcpy(pre, sample[s], n);
            CHECK(load(pre, n) != VX_LOAD_OK);
            free(pre);
        }
        memcpy(b, sample[s], sample_len[s]);
        b[sample_len[s]] = 0;
        CHECK_EQ(load(b, sample_len[s] + 1), VX_LOAD_TRAILING);
        b[sample_len[s]] = 0xff;
        CHECK_EQ(load(b, sample_len[s] + 1), VX_LOAD_TRAILING);
        free(b);
    }
    CHECK_EQ(load(NULL, 0), VX_LOAD_TRUNCATED);
}

/* ----------------------------------------------- hand-built violations */

/* A program of one function Main (arity 0, nslots 2) with the given nodes. */
static int load_one(tfn *f, uint32_t arity, uint32_t nslots, uint32_t root)
{
    tbuf p = { 0 };
    int rc;
    t_prog_header(&p, 1, 0);
    t_fn(&p, f, arity, nslots, "Main", root);
    rc = load(p.b, p.n);
    free(p.b);
    return rc;
}

static void put32(uint8_t *b, uint32_t x)
{
    b[0] = (uint8_t)x;
    b[1] = (uint8_t)(x >> 8);
    b[2] = (uint8_t)(x >> 16);
    b[3] = (uint8_t)(x >> 24);
}

static void violations(void)
{
    tfn f = { 0 }, g = { 0 };
    tbuf p = { 0 };
    uint32_t a, b;

    /* the smallest program: Main() = break */
    n_brk(&f);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_OK);

    /* 1. header */
    n_brk(&f);
    t_prog_header(&p, 1, 0);
    t_fn(&p, &f, 0, 0, "M", 0);
    CHECK_EQ(load(p.b, p.n), VX_LOAD_OK);
    p.b[3] = 'D';
    CHECK_EQ(load(p.b, p.n), VX_LOAD_MAGIC);
    p.b[3] = 'C';
    put32(p.b + 4, 2);
    CHECK_EQ(load(p.b, p.n), VX_LOAD_VERSION);
    put32(p.b + 4, 1);
    put32(p.b + 8, 0);
    CHECK_EQ(load(p.b, p.n), VX_LOAD_NOFNS);
    put32(p.b + 8, VX_MAX_FNS + 1);
    CHECK_EQ(load(p.b, p.n), VX_LOAD_LIMIT);
    put32(p.b + 8, 2);
    CHECK_EQ(load(p.b, p.n), VX_LOAD_TRUNCATED);   /* the second function is missing */
    put32(p.b + 8, 1);
    put32(p.b + 12, 1);
    CHECK_EQ(load(p.b, p.n), VX_LOAD_MAIN);
    put32(p.b + 12, 0);
    CHECK_EQ(load(p.b, p.n), VX_LOAD_OK);
    free(p.b);
    memset(&p, 0, sizeof p);

    /* 2. functions */
    n_brk(&f);
    CHECK_EQ(load_one(&f, 3, 2, 0), VX_LOAD_ARITY);
    n_brk(&f);
    CHECK_EQ(load_one(&f, 2, 2, 0), VX_LOAD_OK);
    n_brk(&f);
    CHECK_EQ(load_one(&f, 0, 0, 1), VX_LOAD_ROOT);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_NONODES);   /* f is empty again */
    n_brk(&f);
    CHECK_EQ(load_one(&f, 0, VX_MAX_SLOTS, 0), VX_LOAD_OK);
    n_brk(&f);
    CHECK_EQ(load_one(&f, 0, VX_MAX_SLOTS + 1, 0), VX_LOAD_LIMIT);

    /* 3. children point backwards */
    a = n_int(&f, 1);
    n_seq(&f, a, 1);                               /* node 1 names itself */
    CHECK_EQ(load_one(&f, 0, 0, 1), VX_LOAD_CHILD);
    a = n_int(&f, 1);
    n_seq(&f, 2, a);                               /* a later node */
    CHECK_EQ(load_one(&f, 0, 0, 1), VX_LOAD_CHILD);
    a = n_int(&f, 1);
    b = n_logic(&f, 1);
    n_ite(&f, b, a, 2);
    CHECK_EQ(load_one(&f, 0, 0, 2), VX_LOAD_CHILD);
    a = n_int(&f, 1);
    n_prim(&f, VX_P_ADD, 0, 2, a, 1u);
    CHECK_EQ(load_one(&f, 0, 0, 1), VX_LOAD_CHILD);
    n_loop(&f, 0);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_CHILD);
    a = n_int(&f, 1);
    b = n_prim(&f, VX_P_ADD, 0, 2, a, a);          /* a DAG is fine */
    n_print(&f, b);
    CHECK_EQ(load_one(&f, 0, 0, 2), VX_LOAD_OK);

    /* 4. slots */
    n_local(&f, 2);
    CHECK_EQ(load_one(&f, 0, 2, 0), VX_LOAD_SLOT);
    n_local(&f, 1);
    CHECK_EQ(load_one(&f, 0, 2, 0), VX_LOAD_OK);
    a = n_int(&f, 1);
    n_assign(&f, 2, a);
    CHECK_EQ(load_one(&f, 0, 2, 1), VX_LOAD_SLOT);
    a = n_prim(&f, VX_P_MKARR, 0, 0);
    b = n_logic(&f, 1);
    n_for(&f, 5, a, b, b);
    CHECK_EQ(load_one(&f, 0, 2, 2), VX_LOAD_SLOT);
    a = n_prim(&f, VX_P_MKARR, 0, 0);
    b = n_logic(&f, 1);
    n_for(&f, 1, a, b, b);
    CHECK_EQ(load_one(&f, 0, 2, 2), VX_LOAD_OK);

    /* 5. calls: the callee exists and has the call's arity, even when it
       comes later in the file */
    n_call(&f, 1, 0);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_CALL);
    {
        int k;
        for (k = 0; k < 3; k++) {
            uint32_t x, y;
            x = n_int(&f, 1);
            y = n_int(&f, 2);
            if (k == 0)
                n_call(&f, 1, 2, x, y);            /* G has arity 2: fine */
            else if (k == 1)
                n_call(&f, 1, 1, x);               /* one argument short */
            else
                n_call(&f, 1, 3, x, y, y);         /* one too many */
            n_brk(&g);
            t_prog_header(&p, 2, 0);
            t_fn(&p, &f, 0, 0, "Main", 2 - (k == 1));
            t_fn(&p, &g, 2, 2, "G", 0);
            CHECK_EQ(load(p.b, p.n), k == 0 ? VX_LOAD_OK : VX_LOAD_CALLARITY);
            free(p.b);
            memset(&p, 0, sizeof p);
        }
    }

    /* 6. codes */
    tn_begin(&f, 13);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_TAG);
    tn_begin(&f, 255);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_TAG);
    n_prim(&f, VX_P_LAST + 1, 0, 0);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_PRIM);
    n_prim(&f, VX_P_USERERR, 0, 0);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_OK);
    n_prim(&f, VX_P_FAIL, 1, 0);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_K);
    a = n_prim(&f, VX_P_MKTUP, 0, 0);
    n_prim(&f, VX_P_TUPGET, 7, 1, a);
    CHECK_EQ(load_one(&f, 0, 0, 1), VX_LOAD_OK);
    tn_begin(&f, VX_N_LIT);
    tb_u8(&f.nodes, VX_LIT_LAST + 1);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_LIT);
    tn_begin(&f, VX_N_LIT);
    tb_u8(&f.nodes, VX_LIT_LOGIC);
    tb_u8(&f.nodes, 2);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_LOGIC);
    n_char(&f, 255);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_OK);
    /* heap operations and reference literals (#31) */
    n_ref(&f, 0xffffffffu);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_OK);
    n_heap(&f, VX_H_LAST + 1, 0, 0);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_HEAP);
    n_heap(&f, VX_H_NEW, 0xffffffffu, 0);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_OK);
    a = n_int(&f, 1);
    n_heap(&f, VX_H_GET, 9, 1, a);
    CHECK_EQ(load_one(&f, 0, 0, 1), VX_LOAD_OK);
    a = n_int(&f, 1);
    n_heap(&f, VX_H_TAG, 0, 1, a);
    CHECK_EQ(load_one(&f, 0, 0, 1), VX_LOAD_OK);
    a = n_int(&f, 1);
    n_heap(&f, VX_H_TAG, 1, 1, a);
    CHECK_EQ(load_one(&f, 0, 0, 1), VX_LOAD_K);
    n_heap(&f, VX_H_SET, 0, 1, 0);                   /* the child is the node itself */
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_CHILD);
    {
        static const uint32_t tags[] = { 3, 0x01020304u };
        vx_program pr;
        a = n_int(&f, 1);
        n_istag(&f, 2, tags, a);
        t_prog_header(&p, 1, 0);
        t_fn(&p, &f, 0, 0, "Main", 1);
        CHECK_EQ(vx_load(p.b, p.n, &pr), VX_LOAD_OK);
        if (pr.nfns == 1) {
            const vx_node *nd = &pr.fns[0].nodes[1];
            CHECK(nd->tag == VX_N_HEAP && nd->op == VX_H_ISTAG && nd->d == 2 && nd->b == 1);
            CHECK((uint64_t)nd->a + 8 <= pr.nbytes);
            if ((uint64_t)nd->a + 8 <= pr.nbytes) {
                CHECK(pr.bytes[nd->a] == 3 && pr.bytes[nd->a + 4] == 4 && pr.bytes[nd->a + 7] == 1);
            }
            CHECK(pr.args[nd->c] == 0);
        }
        vx_free_program(&pr);
        free(p.b);
        memset(&p, 0, sizeof p);
    }
    /* isTag: the tag list may be empty; it is bounded and must be complete */
    a = n_int(&f, 1);
    n_istag(&f, 0, NULL, a);
    CHECK_EQ(load_one(&f, 0, 0, 1), VX_LOAD_OK);
    tn_begin(&f, VX_N_HEAP);
    tb_u8(&f.nodes, VX_H_ISTAG);
    tb_u32(&f.nodes, VX_MAX_TAGS + 1);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_LIMIT);
    tn_begin(&f, VX_N_HEAP);
    tb_u8(&f.nodes, VX_H_ISTAG);
    tb_u32(&f.nodes, 1000);
    tb_u32(&f.nodes, 5);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_TRUNCATED);
    n_int(&f, INT64_MIN);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_OK);
    n_str(&f, "");
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_OK);
    n_none(&f);
    n_void(&f);
    CHECK_EQ(load_one(&f, 0, 0, 1), VX_LOAD_OK);

    /* 7. limits */
    tn_begin(&f, VX_N_PRIM);
    tb_u8(&f.nodes, VX_P_MKARR);
    tb_u32(&f.nodes, 0);
    tb_u32(&f.nodes, VX_MAX_ARGS + 1);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_LIMIT);
    tn_begin(&f, VX_N_LIT);
    tb_u8(&f.nodes, VX_LIT_STR);
    tb_u32(&f.nodes, VX_MAX_STR + 1);
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_LIMIT);
    tn_begin(&f, VX_N_LIT);
    tb_u8(&f.nodes, VX_LIT_STR);
    tb_u32(&f.nodes, 1000);                        /* longer than what is left */
    CHECK_EQ(load_one(&f, 0, 0, 0), VX_LOAD_TRUNCATED);
    {
        /* nnodes over the limit, and a huge nnodes in a tiny file */
        static const uint8_t hdr[] = { 'O', 'V', 'B', 'C', 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
                                       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
        uint8_t buf[sizeof hdr + 4 + 30];
        memset(buf, 9, sizeof buf);   /* BRK nodes */
        memcpy(buf, hdr, sizeof hdr);
        put32(buf + sizeof hdr, VX_MAX_NODES + 1);
        CHECK_EQ(load(buf, sizeof buf), VX_LOAD_LIMIT);
        put32(buf + sizeof hdr, VX_MAX_NODES);
        CHECK_EQ(load(buf, sizeof buf), VX_LOAD_TRUNCATED);
        put32(buf + sizeof hdr, 26);   /* 26 BRKs, root = 0x09090909: not a node */
        CHECK_EQ(load(buf, sizeof buf), VX_LOAD_ROOT);
        put32(buf + sizeof buf - 4, 25);
        CHECK_EQ(load(buf, sizeof buf), VX_LOAD_OK);
    }
    {
        uint8_t *big = calloc((size_t)VX_MAX_INPUT + 1, 1);
        CHECK(big != NULL);
        if (big != NULL) {
            memcpy(big, "OVBC", 4);
            CHECK_EQ(load(big, (size_t)VX_MAX_INPUT + 1), VX_LOAD_LIMIT);
            free(big);
        }
    }
}

/* ------------------------------------------------------ mutation sweep */

static void mutation_sweep(void)
{
    static const int deltas[] = { 1, -1, 0x80, 0x40, 0x10 };
    int s, accepted = 0, total = 0;
    size_t i, d;
    for (s = 0; s < NSAMPLES; s++) {
        uint8_t *b = malloc(sample_len[s]);
        for (i = 0; i < sample_len[s]; i++) {
            for (d = 0; d < sizeof deltas / sizeof deltas[0] + 3; d++) {
                memcpy(b, sample[s], sample_len[s]);
                if (d < sizeof deltas / sizeof deltas[0])
                    b[i] = (uint8_t)(b[i] + deltas[d]);
                else
                    b[i] = d == 5 ? 0 : d == 6 ? 0xff : (uint8_t)(b[i] ^ 0x01);
                total++;
                if (load(b, sample_len[s]) == VX_LOAD_OK)
                    accepted++;
            }
        }
        free(b);
    }
    printf("mutation sweep: %d single-byte mutants, %d accepted (all well-scoped)\n", total, accepted);
    CHECK(accepted > 0 && accepted < total);
}

int main(int argc, char **argv)
{
    int s;
    if (argc < 2) {
        fprintf(stderr, "usage: test_load COREDIR\n");
        return 2;
    }
    samples_accepted(argv[1]);
    prefixes_and_trailing();
    violations();
    mutation_sweep();
    for (s = 0; s < NSAMPLES; s++)
        free(sample[s]);
    return t_report("test_load");
}
