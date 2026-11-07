/*
 * openverse.h -- the parts of the C runtime that QuickProof proves:
 *
 *   arith.c  int64 arithmetic of Verse Core     (OpenVerse/Core/Prims.lean)
 *   store.c  slot store + undo journal + output (St of OpenVerse/Core/Semantics.lean)
 *   load.c   the OVBC loader                    (docs/FORMAT.md)
 *
 * Everything here is plain C11 over fixed-width integers, so a QuickProof law
 * (a C harness) can call each function directly.  The interpreter, the
 * value heap, the object store and the CLI are declared in vx_runtime.h.
 */
#ifndef OPENVERSE_H
#define OPENVERSE_H

#include <stddef.h>
#include <stdint.h>

/* ------------------------------------------------------------------------
 * Return codes shared by arith.c and store.c
 * ------------------------------------------------------------------------ */
#define VX_OK        0  /* success                                           */
#define VX_FAIL      1  /* Verse failure (division by zero)                  */
#define VX_OVERFLOW  2  /* result outside [INT64_MIN, INT64_MAX]             */
#define VX_ESLOT     3  /* store: slot index outside the slot array          */
#define VX_EFULL     4  /* store: journal or output buffer has no room       */

/* ------------------------------------------------------------------------
 * arith.c -- Res.ofInt (op a b) of Prim.apply, for int arguments.
 * On VX_OK, *out is the exact mathematical result; otherwise *out is not
 * written.  VX_FAIL only for a zero divisor.
 * ------------------------------------------------------------------------ */
int vx_add(int64_t a, int64_t b, int64_t *out);
int vx_sub(int64_t a, int64_t b, int64_t *out);
int vx_mul(int64_t a, int64_t b, int64_t *out);
int vx_neg(int64_t a, int64_t *out);
int vx_abs(int64_t a, int64_t *out);
int vx_floordiv(int64_t a, int64_t b, int64_t *out);  /* floor(a / b)              */
int vx_ceildiv(int64_t a, int64_t b, int64_t *out);   /* ceil(a / b)               */
int vx_quotient(int64_t a, int64_t b, int64_t *out);  /* Int.ediv: Euclidean       */
int vx_modulo(int64_t a, int64_t b, int64_t *out);    /* Int.emod: 0 <= r < |b|    */

/* ------------------------------------------------------------------------
 * store.c -- the transactional state: slots, undo journal, output.
 *
 * A value is two opaque 64-bit words; the store never looks inside them.
 * Slots are addressed absolutely (the interpreter keeps every frame as a
 * window of the one slot array).  While depth > 0 (inside at least one
 * failure context), vx_store_set logs (slot, old value) in the journal.
 * A mark records (journal length, output length, depth); rollback undoes
 * the journal back to the mark and truncates the output; commit keeps the
 * effects, and clears the journal when it leaves the outermost context.
 * Invariants: jlen <= jcap, olen <= ocap, depth == 0 implies jlen == 0.
 * ------------------------------------------------------------------------ */
typedef struct vx_val {
    uint64_t tag;
    uint64_t bits;
} vx_val;

typedef struct vx_undo {
    size_t   slot;
    uint64_t tag;   /* the value the slot held before the write */
    uint64_t bits;
} vx_undo;

typedef struct vx_store {
    vx_val  *slots;  size_t nslots;
    vx_undo *jour;   size_t jcap;  size_t jlen;
    uint8_t *out;    size_t ocap;  size_t olen;
    size_t   depth;
} vx_store;

typedef struct vx_mark {
    size_t jlen;
    size_t olen;
    size_t depth;
} vx_mark;

void   vx_store_init(vx_store *s, vx_val *slots, size_t nslots,
                     vx_undo *jour, size_t jcap, uint8_t *out, size_t ocap);
int    vx_store_get(const vx_store *s, size_t slot, vx_val *v);            /* OK | ESLOT */
int    vx_store_set(vx_store *s, size_t slot, uint64_t tag, uint64_t bits); /* OK | ESLOT | EFULL */
int    vx_store_put(vx_store *s, size_t slot, uint64_t tag, uint64_t bits); /* OK | ESLOT; never logs */
void   vx_store_mark(vx_store *s, vx_mark *m);
void   vx_store_rollback(vx_store *s, const vx_mark *m);
void   vx_store_commit(vx_store *s, const vx_mark *m);
size_t vx_store_journal_len(const vx_store *s);
void   vx_store_forget(vx_store *s, size_t jlen);
int    vx_store_out_append(vx_store *s, const uint8_t *b, size_t n);       /* OK | EFULL */
size_t vx_store_out_len(const vx_store *s);
/* Move onto larger caller-provided buffers (the live contents are copied;
 * the caller frees the old buffer).  EFULL if the new one is too small. */
int    vx_store_move_slots(vx_store *s, vx_val *slots, size_t nslots);
int    vx_store_move_journal(vx_store *s, vx_undo *jour, size_t jcap);
int    vx_store_move_out(vx_store *s, uint8_t *out, size_t ocap);

/* ------------------------------------------------------------------------
 * load.c -- the OVBC loader (docs/FORMAT.md, "What the loader accepts").
 * ------------------------------------------------------------------------ */

/* Limits (condition 7). Each keeps every size computation far from overflow. */
#define VX_MAX_INPUT   (1u << 26)  /* bytes in one file                    */
#define VX_MAX_FNS     (1u << 16)  /* functions                            */
#define VX_MAX_NODES   (1u << 22)  /* nodes of one function                */
#define VX_MAX_SLOTS   (1u << 16)  /* nslots of one function               */
#define VX_MAX_ARGS    (1u << 16)  /* arguments of one PRIM or CALL node   */
#define VX_MAX_STR     (1u << 24)  /* bytes of one name or string literal  */
#define VX_MAX_TAGS    (1u << 22)  /* class tags of one isTag (4 bytes each) */

/* Node tags (FORMAT.md table). */
#define VX_N_LIT     0
#define VX_N_LOCAL   1
#define VX_N_ASSIGN  2
#define VX_N_SEQ     3
#define VX_N_PRIM    4
#define VX_N_CALL    5
#define VX_N_ITE     6
#define VX_N_FOR     7
#define VX_N_LOOP    8
#define VX_N_BRK     9
#define VX_N_RET    10
#define VX_N_PRINT  11
#define VX_N_HEAP   12
#define VX_N_LAST   12

/* Literal kinds. */
#define VX_LIT_INT    0
#define VX_LIT_LOGIC  1
#define VX_LIT_CHAR   2
#define VX_LIT_STR    3
#define VX_LIT_NONE   4
#define VX_LIT_VOID   5
#define VX_LIT_REF    6
#define VX_LIT_LAST   6

/* Heap operations (the op of a HEAP node). */
#define VX_H_NEW    0
#define VX_H_GET    1
#define VX_H_SET    2
#define VX_H_TAG    3
#define VX_H_ISTAG  4
#define VX_H_LAST   4

/* Primitive codes. */
#define VX_P_ADD       0
#define VX_P_SUB       1
#define VX_P_MUL       2
#define VX_P_NEG       3
#define VX_P_ABS       4
#define VX_P_FLOORDIV  5
#define VX_P_CEILDIV   6
#define VX_P_QUOTIENT  7
#define VX_P_MODULO    8
#define VX_P_LT        9
#define VX_P_LE       10
#define VX_P_GT       11
#define VX_P_GE       12
#define VX_P_EQ       13
#define VX_P_NE       14
#define VX_P_QUERY    15
#define VX_P_MKARR    16
#define VX_P_MKTUP    17
#define VX_P_MKSOME   18
#define VX_P_CONCAT   19
#define VX_P_INDEX    20
#define VX_P_LEN      21
#define VX_P_ARRSET   22
#define VX_P_FLATTEN  23
#define VX_P_RANGE    24
#define VX_P_TUPGET   25
#define VX_P_TOSTR    26
#define VX_P_FAIL     27
#define VX_P_USERERR  28
#define VX_P_LAST     28

/*
 * One node.  Child indices are into the node table of the same function.
 *
 *   tag     op         a          b          c          d       lit
 *   LIT     lit kind   STR: off   STR: len   -          -       INT/LOGIC/CHAR/REF value
 *   LOCAL   -          slot
 *   ASSIGN  -          slot       e
 *   SEQ     -          a          b
 *   PRIM    prim code  k          n          args off
 *   CALL    -          fn         n          args off
 *   ITE     -          c          t          e
 *   FOR     -          slot       it         filt       body
 *   LOOP    -          b
 *   BRK     -
 *   RET     -          e
 *   PRINT   -          e
 *   HEAP    heap op    k          n          args off   -
 *   HEAP    ISTAG      tags off   n          args off   m
 *
 * "args off" indexes vx_program.args (n child indices); "STR: off" and
 * "tags off" index vx_program.bytes (an ISTAG's m class tags are 4m bytes
 * there, each a little-endian u32).  Unused fields are 0.
 */
typedef struct vx_node {
    uint32_t tag;
    uint32_t op;
    uint32_t a, b, c, d;
    int64_t  lit;
} vx_node;

typedef struct vx_fn {
    uint32_t arity;
    uint32_t nslots;
    uint32_t decides;   /* the byte as read; only 0/1 are emitted by Lean */
    uint32_t name_off;  /* into vx_program.bytes */
    uint32_t name_len;
    uint32_t nnodes;
    uint32_t root;
    vx_node *nodes;     /* nnodes records, malloc'd exactly */
} vx_fn;

typedef struct vx_program {
    uint32_t  nfns;
    uint32_t  entry;    /* index of Main (the file's `main` field) */
    vx_fn    *fns;      /* nfns records */
    uint32_t *args;     /* child lists of PRIM/CALL nodes (NULL if none) */
    uint32_t  nargs;
    uint8_t  *bytes;    /* names and string literals (NULL if none) */
    uint32_t  nbytes;
} vx_program;

/* vx_load results. */
#define VX_LOAD_OK          0
#define VX_LOAD_TRUNCATED   1  /* the input ends inside a field            */
#define VX_LOAD_MAGIC       2  /* not "OVBC"                               */
#define VX_LOAD_VERSION     3  /* version != 1                             */
#define VX_LOAD_NOFNS       4  /* nfns == 0                                */
#define VX_LOAD_MAIN        5  /* main >= nfns                             */
#define VX_LOAD_ARITY       6  /* arity > nslots                           */
#define VX_LOAD_NONODES     7  /* nnodes == 0                              */
#define VX_LOAD_ROOT        8  /* root >= nnodes                           */
#define VX_LOAD_CHILD       9  /* a child index of node j is >= j          */
#define VX_LOAD_SLOT       10  /* a slot is >= nslots                      */
#define VX_LOAD_CALL       11  /* a CALL names a function >= nfns          */
#define VX_LOAD_CALLARITY  12  /* a CALL's n differs from the callee arity */
#define VX_LOAD_TAG        13  /* node tag > 12                            */
#define VX_LOAD_PRIM       14  /* prim code > 28                           */
#define VX_LOAD_K          15  /* k != 0 on a prim other than tupGet, or on
                                  the heap op tag                          */
#define VX_LOAD_LIT        16  /* literal kind > 6                         */
#define VX_LOAD_LOGIC      17  /* LOGIC byte > 1                           */
#define VX_LOAD_TRAILING   18  /* bytes left after the last function      */
#define VX_LOAD_LIMIT      19  /* a count exceeds a VX_MAX_* limit         */
#define VX_LOAD_NOMEM      20  /* malloc failed                            */
#define VX_LOAD_HEAP       21  /* heap op > 4                              */
#define VX_LOAD_LAST       21

/* Parse and check buf[0..len).  Reads only inside the buffer.  On
 * VX_LOAD_OK, *out owns a program satisfying FORMAT.md conditions 1-7;
 * on any other result *out is empty (all NULL / 0).  Either way
 * vx_free_program(out) is safe. */
int  vx_load(const uint8_t *buf, size_t len, vx_program *out);
void vx_free_program(vx_program *p);

#endif /* OPENVERSE_H */
