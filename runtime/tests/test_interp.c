/*
 * test_interp.c -- the interpreter on hand-assembled programs, for the
 * parts of Interp.lean / Prims.lean the sample programs do not reach.
 */
#include "testlib.h"

static vx_outcome last;

/* Load p (consumed), run it with `fuel`, keep the outcome in `last`. */
static int run(tbuf *p, uint64_t fuel, size_t max_depth)
{
    vx_program prog;
    vx_opts o;
    int rc = vx_load(p->b, p->n, &prog);
    free(p->b);
    memset(p, 0, sizeof *p);
    vx_outcome_free(&last);
    memset(&last, 0, sizeof last);
    if (rc != VX_LOAD_OK) {
        fprintf(stderr, "load failed: %s\n", vx_load_reason(rc));
        return 0;
    }
    vx_default_opts(&o);
    o.fuel = fuel;
    o.max_depth = max_depth;
    vx_run(&prog, &o, &last);
    vx_free_program(&prog);
    return 1;
}

static void expect(int line, tbuf *p, uint64_t fuel, int kind, int code, const char *out)
{
    int ok = run(p, fuel, 2000) && last.kind == kind && (kind == VX_R_OK || last.code == code) &&
             (out == NULL || (last.outlen == strlen(out) && memcmp(last.out, out, last.outlen) == 0));
    t_checks++;
    if (!ok) {
        t_failures++;
        fprintf(stderr, "test_interp.c:%d: got kind %d code %d out \"%.*s\"; expected kind %d code %d out \"%s\"\n",
                line, last.kind, last.code, (int)last.outlen, last.out ? (const char *)last.out : "",
                kind, code, out ? out : "(any)");
    }
}
#define EXPECT(p, kind, code, out) expect(__LINE__, p, VX_DEFAULT_FUEL, kind, code, out)
#define OK_OUT(p, out) EXPECT(p, VX_R_OK, 0, out)

/* A program whose only function is Main(nslots) = root. */
static void main_only(tbuf *p, tfn *f, uint32_t nslots, uint32_t root)
{
    t_prog_header(p, 1, 0);
    t_fn(p, f, 0, nslots, "Main", root);
}

#define FAILP(f) n_prim(f, VX_P_FAIL, 0, 0)
#define TRUE(f) n_logic(f, 1)

static void rollback_cases(void)
{
    tbuf p = { 0 };
    tfn f = { 0 }, m = { 0 };
    uint32_t a, b, c, d;

    /* A failed callee's output is rolled back by the caller's condition:
       F() = Print("x"); false?    Main() = if (F[]) then Print("a") else Print("b") */
    n_seq(&f, n_print(&f, n_str(&f, "x")), FAILP(&f));
    a = n_call(&m, 0, 0);
    b = n_print(&m, n_str(&m, "a"));
    c = n_print(&m, n_str(&m, "b"));
    n_ite(&m, a, b, c);
    t_prog_header(&p, 2, 1);
    t_fn(&p, &f, 0, 0, "F", f.count - 1);
    t_fn(&p, &m, 0, 0, "Main", m.count - 1);
    OK_OUT(&p, "b\n");

    /* ... but a failure outside every context is Main's failure, output kept */
    n_seq(&f, n_print(&f, n_str(&f, "x")), FAILP(&f));
    n_call(&m, 0, 0);
    t_prog_header(&p, 2, 1);
    t_fn(&p, &f, 0, 0, "F", f.count - 1);
    t_fn(&p, &m, 0, 0, "Main", 0);
    EXPECT(&p, VX_R_FAIL, 0, "x\n");

    /* break out of a condition is not rolled back (Eval.ite_stop):
       X := 0; loop { if (set X = 1; break) {} else {} }; Print(X) */
    a = n_assign(&m, 0, n_int(&m, 0));
    b = n_seq(&m, n_assign(&m, 0, n_int(&m, 1)), n_brk(&m));
    c = n_loop(&m, n_ite(&m, b, n_void(&m), n_void(&m)));
    n_seq(&m, a, n_seq(&m, c, n_print_int(&m, n_local(&m, 0))));
    main_only(&p, &m, 1, m.count - 1);
    OK_OUT(&p, "1\n");

    /* return out of a condition: F() = if (return 5) then 1 else 2 */
    n_ite(&f, n_ret(&f, n_int(&f, 5)), n_int(&f, 1), n_int(&f, 2));
    n_print_int(&m, n_call(&m, 0, 0));
    t_prog_header(&p, 2, 1);
    t_fn(&p, &f, 0, 0, "F", f.count - 1);
    t_fn(&p, &m, 0, 0, "Main", m.count - 1);
    OK_OUT(&p, "5\n");

    /* nested contexts: the outer failure undoes the inner else branch too
       X := 0; Y := 0
       if ((if (set X = 1; false?) {} else { set Y = 2 }); set X = 3; false?) { Print("no") }
       Print(X); Print(Y) */
    {
        int k;
        for (k = 0; k < 2; k++) {
            uint32_t inner, outer, tail;
            a = n_seq(&m, n_assign(&m, 0, n_int(&m, 0)), n_assign(&m, 1, n_int(&m, 0)));
            inner = n_ite(&m, n_seq(&m, n_assign(&m, 0, n_int(&m, 1)), FAILP(&m)), n_void(&m),
                          n_assign(&m, 1, n_int(&m, 2)));
            tail = n_assign(&m, 0, n_int(&m, 3));
            if (k == 0)
                tail = n_seq(&m, tail, FAILP(&m));
            outer = n_ite(&m, n_seq(&m, inner, tail), n_print(&m, n_str(&m, "yes")), n_void(&m));
            d = n_seq(&m, n_print_int(&m, n_local(&m, 0)), n_print_int(&m, n_local(&m, 1)));
            n_seq(&m, a, n_seq(&m, outer, d));
            main_only(&p, &m, 2, m.count - 1);
            if (k == 0)
                OK_OUT(&p, "0\n0\n");
            else
                OK_OUT(&p, "yes\n3\n2\n");
        }
    }

    /* the for filter: a failed filter's writes and output are undone, back to
       the state after binding the element (EvalFor.skip)
       Y := 0
       R := for (I : array{1, 2, 3}, (Print("f"); set Y = I; I > 1)) { I }
       Print(Y); Print(R.Length); Print(I) */
    a = n_assign(&m, 1, n_int(&m, 0));
    b = n_prim(&m, VX_P_MKARR, 0, 3, n_int(&m, 1), n_int(&m, 2), n_int(&m, 3));
    c = n_seq(&m, n_print(&m, n_str(&m, "f")),
              n_seq(&m, n_assign(&m, 1, n_local(&m, 0)),
                    n_prim(&m, VX_P_GT, 0, 2, n_local(&m, 0), n_int(&m, 1))));
    d = n_assign(&m, 2, n_for(&m, 0, b, c, n_local(&m, 0)));
    n_seq(&m, a, n_seq(&m, d, n_seq(&m, n_print_int(&m, n_local(&m, 1)),
          n_seq(&m, n_print_int(&m, n_prim(&m, VX_P_LEN, 0, 1, n_local(&m, 2))),
                n_print_int(&m, n_local(&m, 0))))));
    main_only(&p, &m, 3, m.count - 1);
    OK_OUT(&p, "f\nf\n3\n2\n3\n");

    /* a callee that writes its own frame inside the caller's context, then
       the context fails: G(N) = set N = 9; Print("g"); false?
       X := 1; if (set X = 2; G[X]) {} else { Print(X) } */
    n_seq(&f, n_assign(&f, 0, n_int(&f, 9)), n_seq(&f, n_print(&f, n_str(&f, "g")), FAILP(&f)));
    a = n_assign(&m, 0, n_int(&m, 1));
    b = n_seq(&m, n_assign(&m, 0, n_int(&m, 2)), n_call(&m, 0, 1, n_local(&m, 0)));
    n_seq(&m, a, n_ite(&m, b, n_void(&m), n_print_int(&m, n_local(&m, 0))));
    t_prog_header(&p, 2, 1);
    t_fn(&p, &f, 1, 1, "G", f.count - 1);
    t_fn(&p, &m, 0, 1, "Main", m.count - 1);
    OK_OUT(&p, "1\n");

    /* many writes inside one context (journal growth), then failure:
       X := 7; if (loop { set X = X + 1; if (X >= 10007) { break } }; false?) {} else {}; Print(X) */
    a = n_assign(&m, 0, n_int(&m, 7));
    b = n_seq(&m, n_assign(&m, 0, n_prim(&m, VX_P_ADD, 0, 2, n_local(&m, 0), n_int(&m, 1))),
              n_ite(&m, n_prim(&m, VX_P_GE, 0, 2, n_local(&m, 0), n_int(&m, 10007)), n_brk(&m),
                    n_void(&m)));
    c = n_ite(&m, n_seq(&m, n_loop(&m, b), FAILP(&m)), n_void(&m), n_void(&m));
    n_seq(&m, a, n_seq(&m, c, n_print_int(&m, n_local(&m, 0))));
    main_only(&p, &m, 1, m.count - 1);
    OK_OUT(&p, "7\n");
}

static void prim_cases(void)
{
    tbuf p = { 0 };
    tfn m = { 0 };
    uint32_t a, b;

    /* int edge cases through the primitives */
    n_seq(&m, n_print_int(&m, n_int(&m, INT64_MIN)),
          n_seq(&m, n_print_int(&m, n_prim(&m, VX_P_MODULO, 0, 2, n_int(&m, INT64_MIN), n_int(&m, -1))),
                n_seq(&m, n_print_int(&m, n_prim(&m, VX_P_QUOTIENT, 0, 2, n_int(&m, -7), n_int(&m, 2))),
                      n_print_int(&m, n_prim(&m, VX_P_CEILDIV, 0, 2, n_int(&m, -7), n_int(&m, 2))))));
    main_only(&p, &m, 0, m.count - 1);
    OK_OUT(&p, "-9223372036854775808\n0\n-4\n-3\n");
    n_seq(&m, n_print(&m, n_str(&m, "before")), n_prim(&m, VX_P_ABS, 0, 1, n_int(&m, INT64_MIN)));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_OVERFLOW, "before\n");
    n_prim(&m, VX_P_QUOTIENT, 0, 2, n_int(&m, INT64_MIN), n_int(&m, -1));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_OVERFLOW, "");
    /* division by zero fails; it is caught by a condition */
    a = n_prim(&m, VX_P_FLOORDIV, 0, 2, n_int(&m, 7), n_int(&m, 0));
    n_ite(&m, a, n_print(&m, n_str(&m, "q")), n_print(&m, n_str(&m, "div0")));
    main_only(&p, &m, 0, m.count - 1);
    OK_OUT(&p, "div0\n");

    /* structural equality */
    {
        uint32_t x = n_prim(&m, VX_P_MKARR, 0, 2, n_int(&m, 1), n_prim(&m, VX_P_MKARR, 0, 1, n_int(&m, 2)));
        uint32_t y = n_prim(&m, VX_P_MKARR, 0, 2, n_int(&m, 1), n_prim(&m, VX_P_MKARR, 0, 1, n_int(&m, 2)));
        uint32_t e1 = n_ite(&m, n_prim(&m, VX_P_EQ, 0, 2, x, y), n_print(&m, n_str(&m, "eq1")), n_print(&m, n_str(&m, "ne1")));
        uint32_t e2 = n_ite(&m, n_prim(&m, VX_P_EQ, 0, 2, n_prim(&m, VX_P_MKARR, 0, 0), n_prim(&m, VX_P_MKTUP, 0, 0)),
                            n_print(&m, n_str(&m, "eq2")), n_print(&m, n_str(&m, "ne2")));
        uint32_t e3 = n_ite(&m, n_prim(&m, VX_P_NE, 0, 2, n_prim(&m, VX_P_MKSOME, 0, 1, n_int(&m, 1)),
                                       n_prim(&m, VX_P_MKSOME, 0, 1, n_int(&m, 2))),
                            n_print(&m, n_str(&m, "ne3")), n_print(&m, n_str(&m, "eq3")));
        uint32_t e4 = n_ite(&m, n_prim(&m, VX_P_EQ, 0, 2, n_str(&m, "ab"),
                                       n_prim(&m, VX_P_MKARR, 0, 2, n_char(&m, 'a'), n_char(&m, 'b'))),
                            n_print(&m, n_str(&m, "eq4")), n_print(&m, n_str(&m, "ne4")));
        uint32_t e5 = n_ite(&m, n_prim(&m, VX_P_EQ, 0, 2, n_logic(&m, 0), n_none(&m)),
                            n_print(&m, n_str(&m, "eq5")), n_print(&m, n_str(&m, "ne5")));
        /* eq succeeds with its LEFT operand; lt on chars */
        uint32_t e6 = n_print(&m, n_prim(&m, VX_P_EQ, 0, 2, n_str(&m, "L"), n_str(&m, "L")));
        uint32_t e7 = n_print(&m, n_prim(&m, VX_P_TOSTR, 0, 1, n_prim(&m, VX_P_LT, 0, 2, n_char(&m, 'a'), n_char(&m, 'b'))));
        n_seq(&m, e1, n_seq(&m, e2, n_seq(&m, e3, n_seq(&m, e4, n_seq(&m, e5, n_seq(&m, e6, e7))))));
        main_only(&p, &m, 0, m.count - 1);
        OK_OUT(&p, "eq1\nne2\nne3\neq4\nne5\nL\na\n");
    }

    /* the error type of each wrong shape */
    n_prim(&m, VX_P_TUPGET, 2, 1, n_prim(&m, VX_P_MKTUP, 0, 2, n_int(&m, 1), n_int(&m, 2)));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_TYPE, "");
    n_prim(&m, VX_P_TOSTR, 0, 1, n_logic(&m, 1));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_TYPE, "");
    n_print(&m, n_int(&m, 3));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_TYPE, "");
    n_print(&m, n_prim(&m, VX_P_MKARR, 0, 2, n_char(&m, 'a'), n_int(&m, 1)));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_TYPE, "");
    n_prim(&m, VX_P_ADD, 0, 3, n_int(&m, 1), n_int(&m, 2), n_int(&m, 3));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_TYPE, "");
    n_prim(&m, VX_P_LT, 0, 2, n_int(&m, 1), n_char(&m, 'a'));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_TYPE, "");
    n_prim(&m, VX_P_FLATTEN, 0, 1, n_prim(&m, VX_P_MKARR, 0, 2, n_str(&m, "a"), n_int(&m, 1)));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_TYPE, "");
    n_prim(&m, VX_P_USERERR, 0, 0);
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_USER, "");
    n_prim(&m, VX_P_FAIL, 0, 1, n_int(&m, 1));        /* false? with an argument: type */
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_TYPE, "");
    n_for(&m, 0, n_int(&m, 3), TRUE(&m), n_void(&m));  /* for over a non-array */
    main_only(&p, &m, 1, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_TYPE, "");

    /* arrays: index, arrSet, concat, flatten, query */
    a = n_assign(&m, 0, n_prim(&m, VX_P_CONCAT, 0, 2, n_str(&m, "ab"), n_str(&m, "cd")));
    b = n_seq(&m, n_print(&m, n_local(&m, 0)),
              n_seq(&m, n_print(&m, n_prim(&m, VX_P_ARRSET, 0, 3, n_local(&m, 0), n_int(&m, 1), n_char(&m, 'X'))),
                    n_seq(&m, n_print(&m, n_local(&m, 0)),
                          n_seq(&m, n_ite(&m, n_prim(&m, VX_P_INDEX, 0, 2, n_local(&m, 0), n_int(&m, 4)),
                                          n_print(&m, n_str(&m, "in")), n_print(&m, n_str(&m, "out"))),
                                n_seq(&m, n_ite(&m, n_prim(&m, VX_P_ARRSET, 0, 3, n_local(&m, 0), n_int(&m, -1), n_char(&m, 'X')),
                                                n_print(&m, n_str(&m, "set")), n_print(&m, n_str(&m, "noset"))),
                                      n_seq(&m, n_print(&m, n_prim(&m, VX_P_FLATTEN, 0, 1,
                                                    n_prim(&m, VX_P_MKARR, 0, 3, n_str(&m, "x"), n_str(&m, ""), n_str(&m, "yz")))),
                                            n_print(&m, n_prim(&m, VX_P_TOSTR, 0, 1,
                                                    n_prim(&m, VX_P_QUERY, 0, 1, n_prim(&m, VX_P_MKSOME, 0, 1, n_char(&m, 'q')))))))))));
    n_seq(&m, a, b);
    main_only(&p, &m, 1, m.count - 1);
    OK_OUT(&p, "abcd\naXcd\nabcd\nout\nnoset\nxyz\nq\n");
}

static void control_cases(void)
{
    tbuf p = { 0 };
    tfn f = { 0 }, m = { 0 };
    uint32_t a, b;

    /* break escaping a function: retOf .brk = .err .control */
    n_brk(&f);
    n_call(&m, 0, 0);
    t_prog_header(&p, 2, 1);
    t_fn(&p, &f, 0, 0, "F", 0);
    t_fn(&p, &m, 0, 0, "Main", 0);
    EXPECT(&p, VX_R_ERR, VX_E_CONTROL, "");
    n_seq(&m, n_print(&m, n_str(&m, "o")), n_brk(&m));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_CONTROL, "o\n");

    /* Main with a parameter: Prog.callable main 0 = none */
    n_brk(&m);
    t_prog_header(&p, 1, 0);
    t_fn(&p, &m, 1, 1, "Main", 0);
    EXPECT(&p, VX_R_ERR, VX_E_CALL, "");

    /* return from a for inside a function:
       FirstAbove(A, T) = for (X : A) { if (X > T) { return X } }; -1 */
    a = n_ite(&f, n_prim(&f, VX_P_GT, 0, 2, n_local(&f, 2), n_local(&f, 1)), n_ret(&f, n_local(&f, 2)), n_void(&f));
    n_seq(&f, n_for(&f, 2, n_local(&f, 0), TRUE(&f), a), n_int(&f, -1));
    b = n_prim(&m, VX_P_MKARR, 0, 4, n_int(&m, 1), n_int(&m, 5), n_int(&m, 2), n_int(&m, 7));
    n_seq(&m, n_print_int(&m, n_call(&m, 0, 2, b, n_int(&m, 3))),
          n_print_int(&m, n_call(&m, 0, 2, b, n_int(&m, 9))));
    t_prog_header(&p, 2, 1);
    t_fn(&p, &f, 2, 3, "FirstAbove", f.count - 1);
    t_fn(&p, &m, 0, 0, "Main", m.count - 1);
    OK_OUT(&p, "5\n-1\n");

    /* unbounded recursion stops at the depth limit */
    n_call(&f, 0, 0);
    n_call(&m, 0, 0);
    t_prog_header(&p, 2, 1);
    t_fn(&p, &f, 0, 0, "F", 0);
    t_fn(&p, &m, 0, 0, "Main", 0);
    EXPECT(&p, VX_R_LIMIT, VX_L_DEPTH, NULL);

    /* deep but bounded recursion with wide frames grows the slot stack:
       D(N) = if (N <= 0) then 0 else D(N - 1) + 1 , with 10 slots */
    a = n_prim(&f, VX_P_LE, 0, 2, n_local(&f, 0), n_int(&f, 0));
    b = n_prim(&f, VX_P_ADD, 0, 2,
               n_call(&f, 0, 1, n_prim(&f, VX_P_SUB, 0, 2, n_local(&f, 0), n_int(&f, 1))), n_int(&f, 1));
    n_ite(&f, a, n_int(&f, 0), b);
    n_print_int(&m, n_call(&m, 0, 1, n_int(&m, 600)));
    t_prog_header(&p, 2, 1);
    t_fn(&p, &f, 1, 10, "D", f.count - 1);
    t_fn(&p, &m, 0, 0, "Main", m.count - 1);
    OK_OUT(&p, "600\n");

    /* lots of output */
    a = n_for(&m, 0, n_prim(&m, VX_P_RANGE, 0, 2, n_int(&m, 1), n_int(&m, 5000)), TRUE(&m),
              n_print_int(&m, n_local(&m, 0)));
    main_only(&p, &m, 1, a);
    CHECK(run(&p, VX_DEFAULT_FUEL, 2000));
    CHECK(last.kind == VX_R_OK && last.outlen == 2 * 9 + 90 * 3 + 900 * 4 + 4001 * 5);
}

/* Lean's fuel: the nesting bound, transcribed exactly. */
static void fuel_cases(void)
{
    tbuf p = { 0 };
    tfn m = { 0 };
    uint64_t fuel;
    uint32_t a, b;

    /* Main() = Print("a"); Print("b") needs fuel 4: eval of the call (1),
       then the body with 3: seq (1), print (1), the literal (1) */
    for (fuel = 0; fuel <= 6; fuel++) {
        n_seq(&m, n_print(&m, n_str(&m, "a")), n_print(&m, n_str(&m, "b")));
        main_only(&p, &m, 0, m.count - 1);
        if (fuel < 4)
            expect(__LINE__, &p, fuel, VX_R_LIMIT, VX_L_FUEL, NULL);
        else
            expect(__LINE__, &p, fuel, VX_R_OK, 0, "a\nb\n");
    }
    /* X := 0; loop { set X = X + 1; if (X >= 3) { break } }; Print(X):
       the threshold is 12, by unfolding eval by hand */
    for (fuel = 9; fuel <= 14; fuel++) {
        a = n_assign(&m, 0, n_int(&m, 0));
        b = n_seq(&m, n_assign(&m, 0, n_prim(&m, VX_P_ADD, 0, 2, n_local(&m, 0), n_int(&m, 1))),
                  n_ite(&m, n_prim(&m, VX_P_GE, 0, 2, n_local(&m, 0), n_int(&m, 3)), n_brk(&m), n_void(&m)));
        n_seq(&m, a, n_seq(&m, n_loop(&m, b), n_print_int(&m, n_local(&m, 0))));
        main_only(&p, &m, 1, m.count - 1);
        if (fuel < 12)
            expect(__LINE__, &p, fuel, VX_R_LIMIT, VX_L_FUEL, NULL);
        else
            expect(__LINE__, &p, fuel, VX_R_OK, 0, "3\n");
    }
    /* a for over `range` is iterated without building the array; at every
       fuel it must end exactly as when the array is built (o.eager_range) */
    {
        int64_t n;
        int eager;
        for (n = -1; n <= 4; n++) {
            for (fuel = 1; fuel <= 24; fuel++) {
                vx_outcome res[2];
                for (eager = 0; eager < 2; eager++) {
                    vx_program prog;
                    vx_opts o;
                    a = n_prim(&m, VX_P_RANGE, 0, 2, n_int(&m, 1), n_int(&m, n));
                    b = n_for(&m, 0, a, n_prim(&m, VX_P_GT, 0, 2, n_local(&m, 0), n_int(&m, 1)),
                              n_prim(&m, VX_P_MUL, 0, 2, n_local(&m, 0), n_local(&m, 0)));
                    n_print(&m, n_prim(&m, VX_P_TOSTR, 0, 1, n_prim(&m, VX_P_LEN, 0, 1, b)));
                    main_only(&p, &m, 1, m.count - 1);
                    CHECK_EQ(vx_load(p.b, p.n, &prog), VX_LOAD_OK);
                    free(p.b);
                    memset(&p, 0, sizeof p);
                    vx_default_opts(&o);
                    o.fuel = fuel;
                    o.eager_range = eager;
                    vx_run(&prog, &o, &res[eager]);
                    vx_free_program(&prog);
                }
                CHECK(res[0].kind == res[1].kind && res[0].code == res[1].code &&
                      res[0].outlen == res[1].outlen &&
                      (res[0].outlen == 0 || memcmp(res[0].out, res[1].out, res[0].outlen) == 0));
                vx_outcome_free(&res[0]);
                vx_outcome_free(&res[1]);
            }
        }
    }
    /* eval_mono: once a program finishes with some fuel it finishes the
       same way with any more fuel */
    {
        int done = 0;
        for (fuel = 1; fuel <= 60; fuel++) {
            a = n_prim(&m, VX_P_MKARR, 0, 3, n_int(&m, 1), n_int(&m, 2), n_int(&m, 3));
            b = n_for(&m, 0, a, n_prim(&m, VX_P_GT, 0, 2, n_local(&m, 0), n_int(&m, 1)),
                      n_print_int(&m, n_local(&m, 0)));
            main_only(&p, &m, 1, b);
            run(&p, fuel, 2000);
            if (last.kind == VX_R_OK) {
                CHECK(last.outlen == 4 && memcmp(last.out, "2\n3\n", 4) == 0);
                done = 1;
            } else {
                CHECK(!done && last.kind == VX_R_LIMIT && last.code == VX_L_FUEL);
            }
        }
        CHECK(done);
    }
}

/* The heap: reclamation at call return, compaction with sharing, deep values. */
static void heap_cases(void)
{
    tbuf p = { 0 };
    tfn f = { 0 }, g = { 0 }, m = { 0 };
    uint32_t a, b, c;

    /* Garbage made by a callee that returns an int is all freed:
       L(N) = (ToString(N) + "!").Length ; loop 20000 times calling L */
    n_prim(&f, VX_P_LEN, 0, 1, n_prim(&f, VX_P_CONCAT, 0, 2,
                                      n_prim(&f, VX_P_TOSTR, 0, 1, n_local(&f, 0)), n_str(&f, "!")));
    a = n_assign(&m, 0, n_int(&m, 0));
    b = n_seq(&m, n_assign(&m, 0, n_prim(&m, VX_P_ADD, 0, 2, n_local(&m, 0), n_int(&m, 1))),
              n_seq(&m, n_assign(&m, 1, n_call(&m, 0, 1, n_local(&m, 0))),
                    n_ite(&m, n_prim(&m, VX_P_GE, 0, 2, n_local(&m, 0), n_int(&m, 20000)), n_brk(&m), n_void(&m))));
    n_seq(&m, a, n_seq(&m, n_loop(&m, b), n_print_int(&m, n_local(&m, 1))));
    t_prog_header(&p, 2, 1);
    t_fn(&p, &f, 1, 1, "L", f.count - 1);
    t_fn(&p, &m, 0, 2, "Main", m.count - 1);
    CHECK(run(&p, VX_DEFAULT_FUEL, 2000));
    CHECK(last.kind == VX_R_OK && last.outlen == 2 && memcmp(last.out, "6\n", 2) == 0);
    CHECK(last.heap_cells < 64);

    /* A fresh result survives, with its sharing, through two returns:
       G(N) = S := ToString(N); (S + S); array{S, S, option{S}}      -- S + S is garbage
       H(N) = X := G(N); (ToString(N) + "junk"); (X, G(N + 1))
       Main: loop 300 times { set R = H(I) }; then compare R with a value
       built directly, and print its pieces */
    a = n_assign(&g, 1, n_prim(&g, VX_P_TOSTR, 0, 1, n_local(&g, 0)));
    b = n_prim(&g, VX_P_CONCAT, 0, 2, n_local(&g, 1), n_local(&g, 1));
    c = n_prim(&g, VX_P_MKARR, 0, 3, n_local(&g, 1), n_local(&g, 1), n_prim(&g, VX_P_MKSOME, 0, 1, n_local(&g, 1)));
    n_seq(&g, a, n_seq(&g, b, c));
    a = n_assign(&f, 1, n_call(&f, 0, 1, n_local(&f, 0)));
    b = n_prim(&f, VX_P_CONCAT, 0, 2, n_prim(&f, VX_P_TOSTR, 0, 1, n_local(&f, 0)), n_str(&f, "junk"));
    c = n_prim(&f, VX_P_MKTUP, 0, 2, n_local(&f, 1),
               n_call(&f, 0, 1, n_prim(&f, VX_P_ADD, 0, 2, n_local(&f, 0), n_int(&f, 1))));
    n_seq(&f, a, n_seq(&f, b, c));
    {
        uint32_t loop, want, cmp, show;
        a = n_assign(&m, 0, n_int(&m, 0));
        b = n_seq(&m, n_assign(&m, 0, n_prim(&m, VX_P_ADD, 0, 2, n_local(&m, 0), n_int(&m, 1))),
                  n_seq(&m, n_assign(&m, 1, n_call(&m, 1, 1, n_local(&m, 0))),
                        n_ite(&m, n_prim(&m, VX_P_GE, 0, 2, n_local(&m, 0), n_int(&m, 300)), n_brk(&m), n_void(&m))));
        loop = n_loop(&m, b);
        want = n_prim(&m, VX_P_MKTUP, 0, 2,
                      n_prim(&m, VX_P_MKARR, 0, 3, n_str(&m, "300"), n_str(&m, "300"),
                             n_prim(&m, VX_P_MKSOME, 0, 1, n_str(&m, "300"))),
                      n_prim(&m, VX_P_MKARR, 0, 3, n_str(&m, "301"), n_str(&m, "301"),
                             n_prim(&m, VX_P_MKSOME, 0, 1, n_str(&m, "301"))));
        cmp = n_ite(&m, n_prim(&m, VX_P_EQ, 0, 2, n_local(&m, 1), want), n_print(&m, n_str(&m, "same")),
                    n_print(&m, n_str(&m, "differs")));
        show = n_print(&m, n_prim(&m, VX_P_QUERY, 0, 1,
                                  n_prim(&m, VX_P_INDEX, 0, 2,
                                         n_prim(&m, VX_P_TUPGET, 1, 1, n_local(&m, 1)), n_int(&m, 2))));
        n_seq(&m, a, n_seq(&m, loop, n_seq(&m, cmp, show)));
    }
    t_prog_header(&p, 3, 2);
    t_fn(&p, &g, 1, 2, "G", g.count - 1);
    t_fn(&p, &f, 1, 2, "H", f.count - 1);
    t_fn(&p, &m, 0, 2, "Main", m.count - 1);
    CHECK(run(&p, VX_DEFAULT_FUEL, 2000));
    CHECK(last.kind == VX_R_OK && last.outlen == 9 && memcmp(last.out, "same\n301\n", 9) == 0);
    /* each iteration leaves one result in Main's region (~20 cells), not
       the ~60 cells of garbage made to get it */
    CHECK(last.heap_cells < 300 * 30);

    /* Equality of values nested 100000 deep (no recursion in vx_equal):
       loop 100000 times { set A = option{A}; set B = option{B} }; A = B */
    a = n_seq(&m, n_assign(&m, 0, n_int(&m, 0)), n_seq(&m, n_assign(&m, 1, n_int(&m, 0)), n_assign(&m, 2, n_int(&m, 0))));
    b = n_seq(&m, n_assign(&m, 0, n_prim(&m, VX_P_MKSOME, 0, 1, n_local(&m, 0))),
              n_seq(&m, n_assign(&m, 1, n_prim(&m, VX_P_MKSOME, 0, 1, n_local(&m, 1))),
                    n_seq(&m, n_assign(&m, 2, n_prim(&m, VX_P_ADD, 0, 2, n_local(&m, 2), n_int(&m, 1))),
                          n_ite(&m, n_prim(&m, VX_P_GE, 0, 2, n_local(&m, 2), n_int(&m, 100000)), n_brk(&m), n_void(&m)))));
    c = n_ite(&m, n_prim(&m, VX_P_EQ, 0, 2, n_local(&m, 0), n_local(&m, 1)), n_print(&m, n_str(&m, "deep eq")),
              n_print(&m, n_str(&m, "deep ne")));
    n_seq(&m, a, n_seq(&m, n_loop(&m, b), c));
    main_only(&p, &m, 3, m.count - 1);
    OK_OUT(&p, "deep eq\n");

    /* ranges: lazy in a for, materialised elsewhere; empty when a > b;
       INT64_MAX - 1 .. INT64_MAX without overflow; a huge materialised
       range is a memory limit */
    a = n_for(&m, 0, n_prim(&m, VX_P_RANGE, 0, 2, n_int(&m, INT64_MAX - 1), n_int(&m, INT64_MAX)), TRUE(&m),
              n_print_int(&m, n_local(&m, 0)));
    b = n_for(&m, 0, n_prim(&m, VX_P_RANGE, 0, 2, n_int(&m, 5), n_int(&m, 1)), TRUE(&m),
              n_print_int(&m, n_local(&m, 0)));
    c = n_print_int(&m, n_prim(&m, VX_P_LEN, 0, 1, n_prim(&m, VX_P_RANGE, 0, 2, n_int(&m, -3), n_int(&m, 4))));
    n_seq(&m, a, n_seq(&m, b, c));
    main_only(&p, &m, 1, m.count - 1);
    OK_OUT(&p, "9223372036854775806\n9223372036854775807\n8\n");
    n_for(&m, 0, n_prim(&m, VX_P_RANGE, 0, 2, n_int(&m, 1), n_logic(&m, 1)), TRUE(&m), n_void(&m));
    main_only(&p, &m, 1, m.count - 1);
    EXPECT(&p, VX_R_ERR, VX_E_TYPE, "");
    n_prim(&m, VX_P_LEN, 0, 1, n_prim(&m, VX_P_RANGE, 0, 2, n_int(&m, INT64_MIN), n_int(&m, INT64_MAX)));
    main_only(&p, &m, 0, m.count - 1);
    EXPECT(&p, VX_R_LIMIT, VX_L_MEMORY, NULL);
}

int main(void)
{
    rollback_cases();
    prim_cases();
    control_cases();
    fuel_cases();
    heap_cases();
    vx_outcome_free(&last);
    return t_report("test_interp");
}
