/*
 * vx_runtime.h -- the unproved part of the C runtime: heap values (value.c),
 * the primitives (prims.c), the interpreter (interp.c) and the CLI (main.c).
 */
#ifndef VX_RUNTIME_H
#define VX_RUNTIME_H

#include "openverse.h"

/* ------------------------------------------------------------------------
 * Values (OpenVerse/Core/Value.lean).  A vx_val is (tag, bits):
 *
 *   tag        Value          bits
 *   VX_T_INT   .int i         i as two's complement
 *   VX_T_LOGIC .logic b       0 / 1
 *   VX_T_CHAR  .char c        0..255
 *   VX_T_ARR   .arr vs        heap index of an object with the elements
 *   VX_T_TUP   .tup vs        heap index of an object with the elements
 *   VX_T_NONE  .none          0
 *   VX_T_SOME  .some v        heap index of a one-element object
 *
 * Strings are arrays of chars, as in Lean.  `void` = .tup [] = (TUP, 0).
 * ------------------------------------------------------------------------ */
#define VX_T_INT    0
#define VX_T_LOGIC  1
#define VX_T_CHAR   2
#define VX_T_ARR    3
#define VX_T_TUP    4
#define VX_T_NONE   5
#define VX_T_SOME   6

static inline int vx_isref(const vx_val *v)
{
    return v->tag == VX_T_ARR || v->tag == VX_T_TUP || v->tag == VX_T_SOME;
}

/* int64 <-> bits without implementation-defined conversions. */
static inline int64_t vx_int_of(uint64_t u)
{
    return u <= (uint64_t)INT64_MAX ? (int64_t)u : -(int64_t)(~u) - 1;
}
static inline uint64_t vx_bits_of(int64_t i)
{
    return (uint64_t)i;
}

/* ------------------------------------------------------------------------
 * Heap (value.c).  An array of 16-byte cells.  An object at index o is a
 * header cell (tag = number of elements n, bits = 0) followed by n element
 * cells.  Cell 0 is the shared object with no elements: every empty array
 * and empty tuple points at it.  Values hold indices, not pointers, so the
 * cell array may move when it grows.  Objects are immutable and only refer
 * to objects that existed when they were made.
 * ------------------------------------------------------------------------ */
typedef struct vx_heap {
    vx_val *cells;
    size_t  len;   /* cells in use */
    size_t  cap;   /* cells allocated */
    size_t  max;   /* cells allowed */
} vx_heap;

int  vx_heap_init(vx_heap *h, size_t max_cells);   /* VX_OK | VX_EFULL */
void vx_heap_free(vx_heap *h);
/* A new object of n elements (header set, elements to be filled by the
 * caller before the next call returns).  n == 0 gives the shared index 0. */
int  vx_heap_alloc(vx_heap *h, size_t n, size_t *idx); /* VX_OK | VX_EFULL */

static inline size_t vx_obj_len(const vx_heap *h, size_t o)
{
    return (size_t)h->cells[o].tag;
}
static inline vx_val *vx_obj_elems(const vx_heap *h, size_t o)
{
    return &h->cells[o + 1];
}

/* Free the cells allocated since `mark` except what `*root` reaches,
 * sliding the survivors down (root is updated).  Used when a call returns:
 * nothing else can refer to the callee's cells (see interp.c). */
int  vx_heap_keep(vx_heap *h, size_t mark, vx_val *root);   /* VX_OK | VX_EFULL */
/* Structural equality, `decide (a = b)` (iterative). */
int  vx_equal(const vx_heap *h, const vx_val *a, const vx_val *b, int *eq);

/* ------------------------------------------------------------------------
 * Outcomes (Res of Value.lean, plus LIMIT for Lean's `none` and for the C
 * resource limits).
 * ------------------------------------------------------------------------ */
#define VX_R_OK     0
#define VX_R_FAIL   1
#define VX_R_BRK    2
#define VX_R_RET    3
#define VX_R_ERR    4
#define VX_R_LIMIT  5

#define VX_E_OVERFLOW  0
#define VX_E_TYPE      1
#define VX_E_SLOT      2
#define VX_E_CALL      3
#define VX_E_CONTROL   4
#define VX_E_USER      5

#define VX_L_FUEL      0   /* Lean's `none` (or the optional step budget) */
#define VX_L_DEPTH     1   /* C recursion depth */
#define VX_L_MEMORY    2   /* heap, slots, journal, output or temporaries */

typedef struct vx_res {
    int    kind;   /* VX_R_* */
    int    code;   /* VX_E_* for ERR, VX_L_* for LIMIT */
    vx_val v;      /* OK, RET */
} vx_res;

typedef struct vx_opts {
    uint64_t fuel;        /* Lean's fuel: eval/evalList/evalFor nesting  */
    uint64_t max_steps;   /* 0 = none; else a total-work budget (fuzzing) */
    size_t   max_depth;   /* nested eval calls (C recursion)             */
    size_t   stack_budget;/* bytes of C stack eval may use; 0 = unchecked */
    size_t   max_heap;    /* heap cells                                  */
    size_t   max_slots;   /* slots of all live frames                    */
    size_t   max_journal; /* journal entries                             */
    size_t   max_out;     /* output bytes                                */
    size_t   max_vstack;  /* argument lists and for accumulators         */
    int      eager_range; /* tests: build the array of a `for` over range */
} vx_opts;

#define VX_DEFAULT_FUEL 100000000u

typedef struct vx_outcome {
    int      kind;        /* VX_R_OK | FAIL | ERR | LIMIT (BRK, RET never: retOf) */
    int      code;
    uint8_t *out;         /* the bytes printed (malloc'd, may be NULL) */
    size_t   outlen;
    size_t   heap_cells;  /* heap cells in use at the end (for tests) */
} vx_outcome;

void vx_default_opts(vx_opts *o);
/* Prog.run: call Main() with fuel o->fuel. */
void vx_run(const vx_program *p, const vx_opts *o, vx_outcome *res);
void vx_outcome_free(vx_outcome *res);

const char *vx_err_name(int code);      /* "overflow", "type", ... */
const char *vx_limit_name(int code);    /* "fuel exhausted", ...   */
const char *vx_load_reason(int rc);     /* reason of a VX_LOAD_* code */

/* ------------------------------------------------------------------------
 * Interpreter context (interp.c), shared with prims.c.
 * ------------------------------------------------------------------------ */
typedef struct vx_ctx {
    const vx_program *p;
    const vx_opts    *o;
    vx_store  st;          /* slots of every live frame, journal, output */
    vx_heap   heap;
    size_t    top;         /* slots in use; the current frame ends here  */
    vx_val   *vs;          /* value stack: temporaries                   */
    size_t    vsp;
    size_t    vcap;
    uint8_t  *scratch;     /* bytes of a string being printed            */
    size_t    scap;
    size_t  **strlit;      /* [fn][node]: heap index of a STR literal    */
    size_t    depth;
    uint64_t  steps;
    uintptr_t stack_base;  /* frame address of vx_run */
} vx_ctx;

/* Prim.apply op vs, with vs = a[0..n).  a must not point into the heap. */
void vx_prim_apply(vx_ctx *c, uint32_t op, uint32_t k, const vx_val *a, size_t n, vx_res *r);

#endif /* VX_RUNTIME_H */
