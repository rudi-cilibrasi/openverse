/*
 * main.c -- cverse FILE.vbc [--fuel N]
 *
 * Loads an OVBC program, runs Main() and reports per the exit protocol of
 * docs/FORMAT.md, with the stderr strings of the Lean runner (Main.lean):
 *
 *   0  Main succeeded                 -
 *   1  Main failed                    failure
 *   2  runtime error                  error: overflow|type|slot|call|control|user
 *   3  resource limit                 limit: fuel exhausted|recursion depth|memory
 *   4  not loadable / bad usage       the reason
 *
 * stdout gets the bytes the program printed.  When a limit stops the run
 * nothing is printed: Lean's Prog.run is `none` then and Main.lean writes
 * no output.
 *
 * The interpreter recurses once per nested evaluation, so it runs on a
 * thread with a large reserved stack (pages are touched only as used).  The
 * deepest C frame chain per nested evaluation is eval_node -> eval_for_iter
 * (about 352 bytes at -O2, 880 under ASan, per gcc -fstack-usage), so
 * VX_MAIN_DEPTH nested evaluations fit VX_STACK_BYTES; the Lean reference
 * binary, for comparison, gives up at a few million nested calls.  The byte
 * budget given to vx_run is a second guard for builds with larger frames.
 * If the system refuses the stack, smaller ones are tried, with the depth
 * scaled down alike.
 */
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "vx_runtime.h"

#ifndef VX_MAIN_DEPTH
#define VX_MAIN_DEPTH   10000000u            /* nested evaluations */
#endif
#ifndef VX_STACK_BYTES
#define VX_STACK_BYTES  ((size_t)4 << 30)    /* reserved for the interpreter thread */
#endif
#define VX_STACK_MARGIN ((size_t)4 << 20)    /* kept free below the budget */
#define VX_MAIN_STACK_DEPTH 2000u            /* on the main thread, as a last resort */

static const char *usage = "usage: cverse FILE.vbc [--fuel N]\n";

static int read_file(const char *path, uint8_t **buf, size_t *len)
{
    FILE *f = fopen(path, "rb");
    uint8_t *b = NULL;
    size_t n = 0, cap = 0;
    if (f == NULL)
        return 0;
    for (;;) {
        size_t got;
        if (n == cap) {
            uint8_t *nb;
            if (cap > VX_MAX_INPUT)
                break;   /* longer than the loader accepts: it says so */
            cap = cap ? cap * 2 : 65536;
            nb = realloc(b, cap);
            if (nb == NULL) {
                free(b);
                fclose(f);
                errno = ENOMEM;
                return 0;
            }
            b = nb;
        }
        got = fread(b + n, 1, cap - n, f);
        n += got;
        if (got == 0) {
            if (ferror(f)) {
                int e = errno;
                free(b);
                fclose(f);
                errno = e ? e : EIO;
                return 0;
            }
            break;
        }
    }
    fclose(f);
    *buf = b;
    *len = n;
    return 1;
}

static int parse_u64(const char *s, uint64_t *out)
{
    uint64_t v = 0;
    if (*s == 0)
        return 0;
    for (; *s; s++) {
        unsigned d;
        if (*s < '0' || *s > '9')
            return 0;
        d = (unsigned)(*s - '0');
        if (v > (UINT64_MAX - d) / 10)
            return 0;
        v = v * 10 + d;
    }
    *out = v;
    return 1;
}

typedef struct {
    const vx_program *p;
    vx_opts o;
    vx_outcome out;
} job;

static void *run_job(void *arg)
{
    job *j = arg;
    vx_run(j->p, &j->o, &j->out);
    return NULL;
}

static int try_thread(job *j, size_t stack)
{
    pthread_attr_t attr;
    pthread_t th;
    int ok = 0;
    if (pthread_attr_init(&attr) != 0)
        return 0;
    if (pthread_attr_setstacksize(&attr, stack) == 0 &&
        pthread_create(&th, &attr, run_job, j) == 0)
        ok = 1;
    pthread_attr_destroy(&attr);
    if (ok)
        pthread_join(th, NULL);
    return ok;
}

static void run_on_big_stack(job *j)
{
    size_t stack = VX_STACK_BYTES, depth = VX_MAIN_DEPTH;
    int k;
    for (k = 0; k < 4; k++, stack /= 4, depth /= 4) {
        j->o.max_depth = depth;
        j->o.stack_budget = stack - VX_STACK_MARGIN;
        if (try_thread(j, stack))
            return;
    }
    j->o.max_depth = VX_MAIN_STACK_DEPTH;
    j->o.stack_budget = (size_t)6 << 20;
    run_job(j);
}

int main(int argc, char **argv)
{
    const char *path = NULL;
    uint8_t *buf = NULL;
    size_t len = 0;
    vx_program prog;
    job j;
    int i, rc, code;

    vx_default_opts(&j.o);
    for (i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--fuel") == 0) {
            if (i + 1 >= argc || !parse_u64(argv[i + 1], &j.o.fuel)) {
                fputs(usage, stderr);
                return 4;
            }
            i++;
        } else if (path == NULL && argv[i][0] != '-') {
            path = argv[i];
        } else {
            fputs(usage, stderr);
            return 4;
        }
    }
    if (path == NULL) {
        fputs(usage, stderr);
        return 4;
    }
    if (!read_file(path, &buf, &len)) {
        fprintf(stderr, "cannot read %s: %s\n", path, strerror(errno));
        return 4;
    }
    rc = vx_load(buf, len, &prog);
    free(buf);
    if (rc != VX_LOAD_OK) {
        fprintf(stderr, "cannot load %s: %s\n", path, vx_load_reason(rc));
        return 4;
    }

    j.p = &prog;
    run_on_big_stack(&j);

    if (j.out.kind == VX_R_LIMIT) {
        fprintf(stderr, "limit: %s\n", vx_limit_name(j.out.code));
        code = 3;
    } else {
        if (j.out.outlen > 0)
            fwrite(j.out.out, 1, j.out.outlen, stdout);
        fflush(stdout);
        if (j.out.kind == VX_R_OK || j.out.kind == VX_R_RET) {
            code = 0;
        } else if (j.out.kind == VX_R_FAIL) {
            fputs("failure\n", stderr);
            code = 1;
        } else if (j.out.kind == VX_R_BRK) {
            fputs("error: control\n", stderr);
            code = 2;
        } else {
            fprintf(stderr, "error: %s\n", vx_err_name(j.out.code));
            code = 2;
        }
    }
    vx_outcome_free(&j.out);
    vx_free_program(&prog);
    return code;
}
