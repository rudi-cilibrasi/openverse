/*
 * interp.c -- the reference interpreter OpenVerse/Core/Interp.lean
 * (`eval`, `evalList`, `evalFor`, `Prog.run`), transcribed over the node
 * table of a loaded program.  Each case quotes the Lean equation it
 * implements.
 *
 * Fuel.  Lean's fuel bounds the nesting of eval/evalList/evalFor calls (not
 * their total number): `eval (n+1)` runs its sub-evaluations with `n`.  It
 * is transcribed exactly: every function takes `fuel`, reports VX_L_FUEL
 * (Lean's `none`) at 0, and passes fuel - 1 down.  Lean's tail calls
 * (`eval P n s₁ b` of seq/ite, `eval P n s₁ (.loop b)`, the recursive
 * evalList/evalFor) become loops that decrement the fuel the same way, so a
 * run finishes with the outcome and output of Lean whenever Lean's run
 * with the same fuel finishes.
 *
 * State.  St = (frame, output) is the vx_store: all frames are windows of
 * one slot array ([base, base + nslots) is the current frame, `top` ends
 * the newest), and the output is the store's buffer.  Failure contexts
 * (the ite condition, the for filter) take a store mark and roll back to it
 * on failure.  A call pushes the frame `frameOf fn vs` above `top` and pops
 * it on return; the output stays (`⟨s₁.fr, s₂.out⟩`).
 *
 * Results.  vx_res is Res plus VX_R_LIMIT, which stands for Lean's `none`
 * (fuel) and for the C resource limits (recursion depth, memory); a limit
 * aborts the run, so no state is repaired on that path.
 *
 * Heap.  When a call returns, the heap cells it allocated are freed except
 * those its result reaches (vx_heap_keep).  That is sound because nothing
 * else can refer to them: the caller's frame and temporaries were made
 * before the call, the callee's frame is gone, the journal entries the
 * callee logged are dropped (vx_store_forget: they are all for slots of
 * frames that no longer exist), and the object fields that may refer to
 * them are roots too: a field written with a heap reference is remembered
 * in the list of the active call whose region holds the value (or a deeper
 * one), and a call returning takes its list's fields as roots, then hands
 * the list to its caller (#50).  Old field values a failure context logged
 * need no root: what a rollback finally restores predates the context.
 *
 * Objects.  Class instances live in the object store (objects.c), Glob.heap
 * of the Lean state: they outlive calls, and a failure context marks and
 * rolls back the object store along with the vx_store (fc_enter, fc_fail,
 * fc_keep).
 */
#include <stdlib.h>
#include <string.h>
#include "vx_runtime.h"

#define INIT_SLOTS    256u
#define INIT_JOURNAL  256u
#define INIT_OUT      4096u
#define INIT_VSTACK   256u

/* -------------------------------------------------------------- results */

static void set_ok(vx_res *r, uint64_t tag, uint64_t bits)
{
    r->kind = VX_R_OK;
    r->code = 0;
    r->v.tag = tag;
    r->v.bits = bits;
}

static void set_void(vx_res *r)
{
    set_ok(r, VX_T_TUP, 0);   /* Value.void = .tup [] */
}

static void set_err(vx_res *r, int code)
{
    r->kind = VX_R_ERR;
    r->code = code;
}

static void set_limit(vx_res *r, int code)
{
    r->kind = VX_R_LIMIT;
    r->code = code;
}

/* ------------------------------------------------- growable resources */

static int grow_slots(vx_ctx *c, size_t need)
{
    size_t cap = c->st.nslots;
    vx_val *old = c->st.slots, *s;
    if (need <= cap)
        return 1;
    if (need > c->o->max_slots)
        return 0;
    while (cap < need)
        cap = cap ? cap * 2 : INIT_SLOTS;
    if (cap > c->o->max_slots)
        cap = c->o->max_slots;
    s = malloc(cap * sizeof(vx_val));
    if (s == NULL)
        return 0;
    vx_store_move_slots(&c->st, s, cap);   /* cap >= need > nslots */
    free(old);
    return 1;
}

static int grow_journal(vx_ctx *c)
{
    size_t cap = c->st.jcap * 2;
    vx_undo *old = c->st.jour, *j;
    if (c->st.jcap >= c->o->max_journal)
        return 0;
    if (cap > c->o->max_journal)
        cap = c->o->max_journal;
    j = malloc(cap * sizeof(vx_undo));
    if (j == NULL)
        return 0;
    vx_store_move_journal(&c->st, j, cap);
    free(old);
    return 1;
}

static int grow_out(vx_ctx *c, size_t extra)
{
    size_t need, cap = c->st.ocap;
    uint8_t *old = c->st.out, *b;
    if (extra > c->o->max_out - c->st.olen)
        return 0;
    need = c->st.olen + extra;
    while (cap < need)
        cap = cap > c->o->max_out / 2 ? c->o->max_out : cap * 2;
    b = malloc(cap);
    if (b == NULL)
        return 0;
    vx_store_move_out(&c->st, b, cap);
    free(old);
    return 1;
}

static int vpush(vx_ctx *c, const vx_val *v)
{
    if (c->vsp == c->vcap) {
        size_t cap = c->vcap * 2;
        vx_val *s;
        if (c->vcap >= c->o->max_vstack)
            return 0;
        if (cap > c->o->max_vstack)
            cap = c->o->max_vstack;
        s = realloc(c->vs, cap * sizeof(vx_val));
        if (s == NULL)
            return 0;
        c->vs = s;
        c->vcap = cap;
    }
    c->vs[c->vsp++] = *v;
    return 1;
}

/* ----------------------------------------------- failure contexts */

/* The state a failure context restarts from: slots and output (vx_store)
   and objects. */
typedef struct {
    vx_mark    st;
    vx_objmark ob;
} fc_mark;

static void fc_enter(vx_ctx *c, fc_mark *m)
{
    vx_store_mark(&c->st, &m->st);
    vx_objs_mark(&c->objs, &m->ob);
}

/* The context failed: back to the state at the mark. */
static void fc_fail(vx_ctx *c, const fc_mark *m)
{
    /* fields restored or objects dropped: a block kept for them may die */
    if (c->nframes > 0 && (c->objs.nlog > m->ob.nlog || c->objs.nobjs > m->ob.nobjs))
        c->dmax[c->nframes - 1] = 0;
    vx_store_rollback(&c->st, &m->st);
    vx_objs_rollback(&c->objs, &m->ob);
    if (c->st.depth == 0)
        vx_objs_forget(&c->objs);
}

/* The context succeeded (or stopped): keep its effects. */
static void fc_keep(vx_ctx *c, const fc_mark *m)
{
    vx_store_commit(&c->st, &m->st);
    if (c->st.depth == 0)
        vx_objs_forget(&c->objs);
}

/* writeSlot through the journal; 0 when the journal cannot grow. */
static int slot_write(vx_ctx *c, size_t slot, const vx_val *v)
{
    int rc = vx_store_set(&c->st, slot, v->tag, v->bits);
    while (rc == VX_EFULL) {
        if (!grow_journal(c))
            return 0;
        rc = vx_store_set(&c->st, slot, v->tag, v->bits);
    }
    return rc == VX_OK;
}

/* s₁.out ++ printBytes v, where
   printBytes (.arr vs) = (asBytes vs).map (· ++ [10]);  printBytes _ = none */
static void print_value(vx_ctx *c, const vx_val *v, vx_res *r)
{
    size_t n, k;
    const vx_val *e;
    if (v->tag != VX_T_ARR) {
        set_err(r, VX_E_TYPE);
        return;
    }
    n = vx_obj_len(&c->heap, v->bits);
    e = vx_obj_elems(&c->heap, v->bits);
    for (k = 0; k < n; k++) {
        if (e[k].tag != VX_T_CHAR) {
            set_err(r, VX_E_TYPE);
            return;
        }
    }
    if (n + 1 > c->scap) {
        size_t cap = n + 1 > 2 * c->scap ? n + 1 : 2 * c->scap;
        uint8_t *s = realloc(c->scratch, cap);
        if (s == NULL) {
            set_limit(r, VX_L_MEMORY);
            return;
        }
        c->scratch = s;
        c->scap = cap;
    }
    for (k = 0; k < n; k++)
        c->scratch[k] = (uint8_t)e[k].bits;
    c->scratch[n] = 10;
    if (vx_store_out_append(&c->st, c->scratch, n + 1) != VX_OK) {
        if (!grow_out(c, n + 1) || vx_store_out_append(&c->st, c->scratch, n + 1) != VX_OK) {
            set_limit(r, VX_L_MEMORY);
            return;
        }
    }
    set_void(r);
}

/* ------------------------------------------------------------- the eval */

static void eval(vx_ctx *c, const vx_fn *fn, size_t base, uint32_t e, uint64_t fuel, vx_res *r);

/*
 * evalList P fuel s es, with es = args[off .. off + n).  On OK the values
 * are pushed on the value stack (at the vsp of entry); any other result is
 * the `.stop r` (value stack unchanged).
 *
 *   | 0, _, _ => none
 *   | _+1, s, [] => some (.ok [], s)
 *   | n+1, s, e :: es => match eval P n s e with
 *     | some (.ok v, s₁) => match evalList P n s₁ es with ... (.ok (v :: vs)) / (.stop r)
 *     | some (.fail | .brk | .ret v | .err k, s₁) => some (.stop _, s₁)
 */
static void eval_list(vx_ctx *c, const vx_fn *fn, size_t base, uint32_t off, uint32_t n,
                      uint64_t fuel, vx_res *r)
{
    size_t sp0 = c->vsp;
    uint32_t k;
    for (k = 0;; k++) {
        if (fuel == 0) {                            /* | 0, _, _ => none */
            c->vsp = sp0;
            set_limit(r, VX_L_FUEL);
            return;
        }
        if (k == n) {                               /* | _+1, s, [] => some (.ok [], s) */
            r->kind = VX_R_OK;
            return;
        }
        eval(c, fn, base, c->p->args[off + k], fuel - 1, r);   /* eval P n s e */
        if (r->kind != VX_R_OK) {                   /* .stop r */
            c->vsp = sp0;
            return;
        }
        if (!vpush(c, &r->v)) {
            c->vsp = sp0;
            set_limit(r, VX_L_MEMORY);
            return;
        }
        fuel = fuel - 1;                            /* evalList P n s₁ es */
    }
}

/*
 * The call proper, after `evalList P n s es` gave vs = vs[sp0 .. sp0+nargs):
 *
 *   match P.callable f vs.length with
 *   | none => some (.err .call, s₁)
 *   | some fn => match eval P n ⟨frameOf fn vs, s₁.out⟩ fn.body with
 *     | none => none
 *     | some (r, s₂) => some (retOf r, ⟨s₁.fr, s₂.out⟩)
 */
/* Reclaim the cells allocated since `hmark` (the top call returning with
   *res), keeping what *res and the fields in the call's list reach. */
static int reclaim(vx_ctx *c, size_t hmark, vx_val *res, size_t *fieldkept)
{
    vx_objs *ob = &c->objs;
    const vx_remlist *l = vx_objs_top(ob);
    size_t j, nr = 0;
    vx_val **roots;
    int rc;
    *fieldkept = 0;
    if (l == NULL || l->n == 0)
        return vx_heap_keep(&c->heap, hmark, res);
    roots = malloc((1 + l->n) * sizeof(vx_val *));
    if (roots == NULL)
        return VX_EFULL;
    roots[nr++] = res;
    for (j = 0; j < l->n; j++) {
        vx_val *v = &ob->cells[l->cells[j]];
        if (vx_isref(v) && v->bits >= hmark)
            roots[nr++] = v;
    }
    rc = vx_heap_keep_roots(&c->heap, hmark, roots, nr, fieldkept);
    free(roots);
    return rc;
}

static void call_fn(vx_ctx *c, uint32_t f, size_t sp0, size_t nargs, uint64_t n, vx_res *r)
{
    const vx_fn *g;
    size_t nb, top0, hmark, jlen0, j;

    /* Prog.callable P f n: the function exists and its arity is n */
    if (f >= c->p->nfns || c->p->fns[f].arity != nargs) {
        c->vsp = sp0;
        set_err(r, VX_E_CALL);
        return;
    }
    g = &c->p->fns[f];
    /* frameOf fn vs = vs ++ List.replicate (fn.nslots - fn.arity) Value.void,
       placed above every live frame */
    nb = c->top;
    if (!grow_slots(c, nb + g->nslots)) {
        c->vsp = sp0;
        set_limit(r, VX_L_MEMORY);
        return;
    }
    for (j = 0; j < nargs; j++)
        vx_store_put(&c->st, nb + j, c->vs[sp0 + j].tag, c->vs[sp0 + j].bits);
    for (; j < g->nslots; j++)
        vx_store_put(&c->st, nb + j, VX_T_TUP, 0);
    c->vsp = sp0;
    top0 = c->top;
    c->top = nb + g->nslots;
    hmark = c->heap.len;
    jlen0 = vx_store_journal_len(&c->st);
    /* the call's heap mark and list of fields (#50) */
    if (c->nframes == c->fcap) {
        size_t cap = c->fcap ? 2 * c->fcap : 64;
        size_t *hm = realloc(c->hmarks, cap * sizeof(size_t));
        size_t *dm = hm == NULL ? NULL : realloc(c->dmax, cap * sizeof(size_t));
        size_t *dl = dm == NULL ? NULL : realloc(c->dlo, cap * sizeof(size_t));
        size_t *dh = dl == NULL ? NULL : realloc(c->dhi, cap * sizeof(size_t));
        if (hm != NULL) c->hmarks = hm;
        if (dm != NULL) c->dmax = dm;
        if (dl != NULL) c->dlo = dl;
        if (dh == NULL) {
            c->top = top0;
            set_limit(r, VX_L_MEMORY);
            return;
        }
        c->dhi = dh;
        c->fcap = cap;
    }
    if (vx_objs_call_fast(&c->objs) != VX_OK) {
        c->top = top0;
        set_limit(r, VX_L_MEMORY);
        return;
    }
    c->hmarks[c->nframes] = hmark;
    c->dmax[c->nframes] = 0;
    c->nframes++;

    eval(c, g, nb, g->root, n, r);                  /* eval P n ⟨frameOf fn vs, s₁.out⟩ fn.body */

    c->top = top0;                                  /* ⟨s₁.fr, s₂.out⟩ */
    if (r->kind == VX_R_LIMIT) {
        c->nframes--;
        vx_objs_return_fast(&c->objs);
        return;
    }
    vx_store_forget(&c->st, jlen0);
    /* retOf: .ok v => .ok v | .ret v => .ok v | .fail => .fail
              | .brk => .err .control | .err e => .err e */
    if (r->kind == VX_R_RET)
        r->kind = VX_R_OK;
    else if (r->kind == VX_R_BRK)
        set_err(r, VX_E_CONTROL);
    /* reclaim the callee's heap cells, except what the result, the fields
       written during the call and the field log made during it reach */
    if (r->kind == VX_R_OK) {
        /* compact, unless the region is less than twice the largest block a
           callee's compaction kept for fields that still hold it: skipping
           keeps more, never less, and what it keeps is mostly live (objects
           are never reclaimed, and a field's change or a rollback zeroes the
           block, below), while the work stays linear where each return
           compacting would be quadratic (a recursion building a linked
           structure re-compacting its survivors at every level). A block
           only a result kept does not count: a caller may drop it. */
        size_t k = c->nframes - 1;
        size_t region = c->heap.len - hmark;
        size_t fk = 0;
        if (c->dmax[k] == 0 && vx_objs_top_empty(&c->objs)) {
            /* no field roots and no block: the result only */
            if (vx_heap_keep(&c->heap, hmark, &r->v) != VX_OK)
                set_limit(r, VX_L_MEMORY);
        } else if (region >= 2 * c->dmax[k]) {
            if (c->st.depth == 0)
                vx_objs_drop_stale(&c->objs);
            if (reclaim(c, hmark, &r->v, &fk) != VX_OK)
                set_limit(r, VX_L_MEMORY);
            else if (k > 0 && fk > c->dmax[k - 1]) {
                /* the survivors lie in [hmark, len): a field change there may
                   kill the block */
                c->dmax[k - 1] = fk;
                c->dlo[k - 1] = hmark;
                c->dhi[k - 1] = c->heap.len;
            }
        } else if (k > 0 && c->dmax[k] > c->dmax[k - 1]) {
            /* the block stays where it is, in the caller's region now */
            c->dmax[k - 1] = c->dmax[k];
            c->dlo[k - 1] = c->dlo[k];
            c->dhi[k - 1] = c->dhi[k];
        }
    } else if (r->kind == VX_R_FAIL) {
        /* the failure reaches a context that rolls the fields back (or ends
           the program) before anything reads them */
        c->heap.len = hmark;
    }
    /* the list goes to the caller */
    c->nframes--;
    if (vx_objs_return_fast(&c->objs) != VX_OK)
        set_limit(r, VX_L_MEMORY);
}

/* The elements still to visit in evalFor: an array object, or (for a
 * `for` over `range a b`, which need not be materialised) a..b. */
typedef struct {
    int      is_range;
    size_t   arr;     /* array: heap index */
    size_t   len;
    int64_t  lo;      /* range: lo .. lo + last */
    uint64_t last;
    int      empty;
} for_src;

static int src_get(const vx_ctx *c, const for_src *s, uint64_t k, vx_val *v)
{
    if (s->is_range) {
        if (s->empty || k > s->last)
            return 0;
        v->tag = VX_T_INT;
        v->bits = vx_bits_of(s->lo) + k;   /* rangeVals a b = [a + k | k < b + 1 - a] */
        return 1;
    }
    if (k >= (uint64_t)s->len)
        return 0;
    *v = vx_obj_elems(&c->heap, s->arr)[k];   /* re-read: the cells may move */
    return 1;
}

/*
 * evalFor P fuel i filt body s vs acc, with vs = the elements of src and
 * acc = [] at entry.  acc is kept on the value stack in visiting order, so
 * acc.reverse is the stack segment.
 *
 *   | 0, _, _, _, _, _, _ => none
 *   | _+1, _, _, _, s, [], acc => some (.ok (.arr acc.reverse), s)
 *   | n+1, i, filt, body, s, v :: vs, acc => match writeSlot s i v with
 *     | none => some (.err .slot, s)
 *     | some s₀ => match eval P n s₀ filt with
 *       | none => none
 *       | some (.fail, _) => evalFor P n i filt body s₀ vs acc
 *       | some (.ok _, s₁) => match eval P n s₁ body with
 *         | none => none
 *         | some (.ok w, s₂) => evalFor P n i filt body s₂ vs (w :: acc)
 *         | some (.fail | .brk | .ret v | .err k, s₂) => pass on, with s₂
 *       | some (.brk | .ret v | .err k, s₁) => pass on, with s₁
 */
static void eval_for_iter(vx_ctx *c, const vx_fn *fn, size_t base, const vx_node *nd,
                          uint64_t fuel, const for_src *src, vx_res *r)
{
    size_t sp0 = c->vsp, o, cnt;
    uint64_t k;
    vx_val v;
    fc_mark m;
    for (k = 0;; k++) {
        if (fuel == 0) {                            /* | 0, ... => none */
            c->vsp = sp0;
            set_limit(r, VX_L_FUEL);
            return;
        }
        if (c->o->max_steps && ++c->steps > c->o->max_steps) {
            c->vsp = sp0;
            set_limit(r, VX_L_FUEL);
            return;
        }
        if (!src_get(c, src, k, &v)) {              /* | _+1, ..., s, [], acc */
            cnt = c->vsp - sp0;
            if (vx_heap_alloc(&c->heap, cnt, &o) != VX_OK) {
                c->vsp = sp0;
                set_limit(r, VX_L_MEMORY);
                return;
            }
            if (cnt > 0)
                memcpy(vx_obj_elems(&c->heap, o), &c->vs[sp0], cnt * sizeof(vx_val));
            c->vsp = sp0;
            set_ok(r, VX_T_ARR, o);                 /* .ok (.arr acc.reverse) */
            return;
        }
        /* match writeSlot s i v with | none => some (.err .slot, s) | some s₀ => */
        if (nd->a >= fn->nslots) {
            c->vsp = sp0;
            set_err(r, VX_E_SLOT);
            return;
        }
        if (!slot_write(c, base + nd->a, &v)) {
            c->vsp = sp0;
            set_limit(r, VX_L_MEMORY);
            return;
        }
        /* match eval P n s₀ filt with -- the filter is a failure context */
        fc_enter(c, &m);
        eval(c, fn, base, nd->c, fuel - 1, r);
        if (r->kind == VX_R_FAIL) {
            /* | some (.fail, _) => evalFor P n i filt body s₀ vs acc  (EvalFor.skip) */
            fc_fail(c, &m);
            fuel = fuel - 1;
            continue;
        }
        if (r->kind == VX_R_LIMIT) {
            c->vsp = sp0;
            return;
        }
        fc_keep(c, &m);
        if (r->kind != VX_R_OK) {                   /* | some (.brk | .ret v | .err k, s₁) */
            c->vsp = sp0;
            return;
        }
        /* | some (.ok _, s₁) => match eval P n s₁ body with */
        eval(c, fn, base, nd->d, fuel - 1, r);
        if (r->kind != VX_R_OK) {                   /* none, or pass on with s₂ */
            c->vsp = sp0;
            return;
        }
        /* | some (.ok w, s₂) => evalFor P n i filt body s₂ vs (w :: acc) */
        if (!vpush(c, &r->v)) {
            c->vsp = sp0;
            set_limit(r, VX_L_MEMORY);
            return;
        }
        fuel = fuel - 1;
    }
}

/*
 *   | n+1, s, .forE i it filt body => bindR (eval P n s it) fun v s₁ =>
 *       match v with
 *       | .arr vs => evalFor P n i filt body s₁ vs []
 *       | .int _ | .logic _ | .char _ | .tup _ | .none | .some _ => some (.err .type, s₁)
 *
 * When `it` is a PRIM range node, `eval P n s it` is unfolded -- the fuel
 * check of eval, then `evalList P (n-1) s es`, then Prim.apply .range --
 * and two int arguments are iterated without building the array.
 */
static void eval_for(vx_ctx *c, const vx_fn *fn, size_t base, const vx_node *nd,
                     uint64_t n, vx_res *r)
{
    const vx_node *it = &fn->nodes[nd->b];
    for_src src;
    memset(&src, 0, sizeof src);
    if (it->tag == VX_N_PRIM && it->op == VX_P_RANGE && !c->o->eager_range) {
        size_t sp0 = c->vsp;
        if (n == 0) {                               /* eval P 0 s it = none */
            set_limit(r, VX_L_FUEL);
            return;
        }
        eval_list(c, fn, base, it->c, it->b, n - 1, r);   /* bindL (evalList P (n-1) s es) */
        if (r->kind != VX_R_OK)
            return;
        if (it->b == 2 && c->vs[sp0].tag == VX_T_INT && c->vs[sp0 + 1].tag == VX_T_INT) {
            int64_t lo = vx_int_of(c->vs[sp0].bits), hi = vx_int_of(c->vs[sp0 + 1].bits);
            c->vsp = sp0;
            src.is_range = 1;
            src.lo = lo;
            src.empty = lo > hi;
            src.last = src.empty ? 0 : vx_bits_of(hi) - vx_bits_of(lo);
            eval_for_iter(c, fn, base, nd, n, &src, r);
            return;
        }
        vx_prim_apply(c, it->op, it->a, &c->vs[sp0], it->b, r);   /* .err .type */
        c->vsp = sp0;
        if (r->kind != VX_R_OK)
            return;
    } else {
        eval(c, fn, base, nd->b, n, r);             /* bindR (eval P n s it) */
        if (r->kind != VX_R_OK)
            return;
    }
    if (r->v.tag != VX_T_ARR) {
        set_err(r, VX_E_TYPE);
        return;
    }
    src.arr = (size_t)r->v.bits;
    src.len = vx_obj_len(&c->heap, src.arr);
    eval_for_iter(c, fn, base, nd, n, &src, r);
}

/* The value of a literal node: `.lit v`. */
static void lit_value(const vx_ctx *c, const vx_fn *fn, uint32_t e, const vx_node *nd, vx_res *r)
{
    if (nd->op == VX_LIT_INT)
        set_ok(r, VX_T_INT, vx_bits_of(nd->lit));
    else if (nd->op == VX_LIT_LOGIC)
        set_ok(r, VX_T_LOGIC, (uint64_t)nd->lit);
    else if (nd->op == VX_LIT_CHAR)
        set_ok(r, VX_T_CHAR, (uint64_t)nd->lit);
    else if (nd->op == VX_LIT_STR)
        set_ok(r, VX_T_ARR, c->strlit[fn - c->p->fns][e]);
    else if (nd->op == VX_LIT_NONE)
        set_ok(r, VX_T_NONE, 0);
    else if (nd->op == VX_LIT_REF)
        set_ok(r, VX_T_REF, (uint64_t)nd->lit);
    else
        set_void(r);
}

/* ------------------------------------------------------------ the heap */

/* The object a value refers to: `.ref a` with `g.heap[a]? = some o`. */
static const vx_obj *obj_of(const vx_ctx *c, const vx_val *v)
{
    return v->tag == VX_T_REF ? vx_objs_get(&c->objs, v->bits) : NULL;
}

/* Object cell `cell` now holds *v: when *v is a heap reference into the
   region of an active call (the deepest whose mark is at most it), remember
   the cell in that call's list, so that its return keeps what it reaches
   (#50; older cells, such as literals and the shared empty object, never
   move). */
/* The active call whose region holds heap cell `bits` (the last frame k
   with hmarks[k] <= bits: the marks never decrease), or nframes if none. */
static size_t owner_of(const vx_ctx *c, uint64_t bits)
{
    size_t lo = 0, hi = c->nframes;
    if (c->nframes == 0 || bits == 0 || bits < c->hmarks[0])
        return c->nframes;
    while (hi - lo > 1) {
        size_t mid = lo + (hi - lo) / 2;
        if (c->hmarks[mid] <= bits) lo = mid; else hi = mid;
    }
    return lo;
}

static int remember(vx_ctx *c, size_t cell, const vx_val *v)
{
    size_t k;
    if (!vx_isref(v))
        return VX_OK;
    k = owner_of(c, v->bits);
    return k == c->nframes ? VX_OK : vx_objs_remember(&c->objs, cell, k);
}

/* Field cell `cell` is about to change: when its value lies in the block a
   compaction kept for fields of the call whose region holds it, the block
   may die, so that call counts no block. */
static void field_changes(vx_ctx *c, size_t cell)
{
    const vx_val *old = &c->objs.cells[cell];
    if (vx_isref(old)) {
        size_t k = owner_of(c, old->bits);
        if (k < c->nframes && c->dmax[k] != 0 && old->bits >= c->dlo[k] && old->bits < c->dhi[k])
            c->dmax[k] = 0;
    }
}

/* Whether class tag t is one of the m tags of an ISTAG node (4m bytes of the
   bytes pool, little-endian u32s). */
static int tag_in(const vx_ctx *c, const vx_node *nd, uint64_t t)
{
    uint32_t i;
    for (i = 0; i < nd->d; i++) {
        const uint8_t *b = &c->p->bytes[nd->a + 4 * i];
        uint64_t u = (uint64_t)b[0] | (uint64_t)b[1] << 8 | (uint64_t)b[2] << 16 | (uint64_t)b[3] << 24;
        if (u == t)
            return 1;
    }
    return 0;
}

/*
 * (op.apply vs s₁.g).1 and the new object store, with vs = a[0..n):
 *
 *   | .new t, vs, g => (.ok (.ref g.heap.length), { g with heap := g.heap ++ [⟨t, vs⟩] })
 *   | .get k, [.ref a], g => match g.heap[a]? with
 *     | some o => match o.fields[k]? with | some v => (.ok v, g) | none => (.err .type, g)
 *     | none => (.err .type, g)
 *   | .set k, [.ref a, v], g => match g.heap[a]? with
 *     | some o => if k < o.fields.length then (.ok v, { g with heap := g.heap.set a … })
 *                 else (.err .type, g)
 *     | none => (.err .type, g)
 *   | .tag, [.ref a], g => match g.heap[a]? with
 *     | some o => (.ok (.int o.tag), g) | none => (.err .type, g)
 *   | .isTag us, [.ref a], g => match g.heap[a]? with
 *     | some o => (if us.contains o.tag then .ok (.ref a) else .fail, g)
 *     | none => (.err .type, g)
 *   | _, _, g => (.err .type, g)
 */
static void heap_apply(vx_ctx *c, const vx_node *nd, const vx_val *a, size_t n, vx_res *r)
{
    const vx_obj *o;
    size_t k, idx;
    if (nd->op == VX_H_NEW) {
        if (vx_objs_new(&c->objs, nd->a, a, n, &idx) != VX_OK) {
            set_limit(r, VX_L_MEMORY);
            return;
        }
        for (k = 0; k < n; k++)
            if (remember(c, c->objs.objs[idx].off + k, &a[k]) != VX_OK) {
                set_limit(r, VX_L_MEMORY);
                return;
            }
        set_ok(r, VX_T_REF, idx);
        return;
    }
    if (n != (nd->op == VX_H_SET ? 2u : 1u) || (o = obj_of(c, &a[0])) == NULL) {
        set_err(r, VX_E_TYPE);
        return;
    }
    switch (nd->op) {
    case VX_H_GET:
        if ((size_t)nd->a >= o->n) {
            set_err(r, VX_E_TYPE);
            return;
        }
        set_ok(r, c->objs.cells[o->off + nd->a].tag, c->objs.cells[o->off + nd->a].bits);
        return;
    case VX_H_SET:
        if ((size_t)nd->a >= o->n) {
            set_err(r, VX_E_TYPE);
            return;
        }
        field_changes(c, o->off + nd->a);
        if (vx_objs_set(&c->objs, a[0].bits, nd->a, &a[1], c->st.depth > 0) != VX_OK ||
            remember(c, o->off + nd->a, &a[1]) != VX_OK) {
            set_limit(r, VX_L_MEMORY);
            return;
        }
        set_ok(r, a[1].tag, a[1].bits);
        return;
    case VX_H_TAG:
        set_ok(r, VX_T_INT, vx_bits_of((int64_t)o->tag));
        return;
    default: /* VX_H_ISTAG */
        if (tag_in(c, nd, o->tag)) {
            set_ok(r, VX_T_REF, a[0].bits);
        } else {
            r->kind = VX_R_FAIL;
            r->code = 0;
        }
        return;
    }
}

/* eval P fuel s e, for node e of fn whose frame starts at slot `base`. */
static void eval_node(vx_ctx *c, const vx_fn *fn, size_t base, uint32_t e, uint64_t fuel, vx_res *r)
{
    for (;;) {
        const vx_node *nd;
        uint64_t n;
        fc_mark m;

        if (fuel == 0) {                            /* | 0, _, _ => none */
            set_limit(r, VX_L_FUEL);
            return;
        }
        if (c->o->max_steps && ++c->steps > c->o->max_steps) {
            set_limit(r, VX_L_FUEL);
            return;
        }
        n = fuel - 1;
        nd = &fn->nodes[e];
        switch (nd->tag) {
        case VX_N_LIT:
            /* | _+1, s, .lit v => some (.ok v, s) */
            lit_value(c, fn, e, nd, r);
            return;

        case VX_N_LOCAL:
            /* | _+1, s, .local i => some (readSlot s i, s)
               readSlot s i = match s.fr[i]? with | some v => .ok v | none => .err .slot */
            if (nd->a < fn->nslots)
                set_ok(r, c->st.slots[base + nd->a].tag, c->st.slots[base + nd->a].bits);
            else
                set_err(r, VX_E_SLOT);
            return;

        case VX_N_ASSIGN:
            /* | n+1, s, .assign i e => bindR (eval P n s e) fun v s₁ =>
                   match writeSlot s₁ i v with
                   | some s₂ => some (.ok v, s₂)
                   | none => some (.err .slot, s₁) */
            eval(c, fn, base, nd->b, n, r);
            if (r->kind != VX_R_OK)
                return;
            if (nd->a >= fn->nslots) {
                set_err(r, VX_E_SLOT);
                return;
            }
            if (!slot_write(c, base + nd->a, &r->v))
                set_limit(r, VX_L_MEMORY);
            return;

        case VX_N_SEQ:
            /* | n+1, s, .seq a b => bindR (eval P n s a) fun _ s₁ => eval P n s₁ b */
            eval(c, fn, base, nd->a, n, r);
            if (r->kind != VX_R_OK)
                return;
            e = nd->b;
            fuel = n;
            continue;

        case VX_N_PRIM: {
            /* | n+1, s, .prim op es => bindL (evalList P n s es) fun vs s₁ =>
                   some (op.apply vs, s₁) */
            size_t sp0 = c->vsp;
            eval_list(c, fn, base, nd->c, nd->b, n, r);
            if (r->kind != VX_R_OK)
                return;
            vx_prim_apply(c, nd->op, nd->a, &c->vs[sp0], nd->b, r);
            c->vsp = sp0;
            return;
        }

        case VX_N_CALL: {
            /* | n+1, s, .call f es => bindL (evalList P n s es) fun vs s₁ => ... (call_fn) */
            size_t sp0 = c->vsp;
            eval_list(c, fn, base, nd->c, nd->b, n, r);
            if (r->kind != VX_R_OK)
                return;
            call_fn(c, nd->a, sp0, nd->b, n, r);
            return;
        }

        case VX_N_ITE:
            /* | n+1, s, .ite c t e => match eval P n s c with
                 | none => none
                 | some (.ok _, s₁) => eval P n s₁ t
                 | some (.fail, _) => eval P n s e          -- rollback (Eval.ite_fail)
                 | some (.brk | .ret v | .err k, s₁) => pass on, with s₁ */
            fc_enter(c, &m);
            eval(c, fn, base, nd->a, n, r);
            if (r->kind == VX_R_OK) {
                fc_keep(c, &m);
                e = nd->b;
                fuel = n;
                continue;
            }
            if (r->kind == VX_R_FAIL) {
                fc_fail(c, &m);
                e = nd->c;
                fuel = n;
                continue;
            }
            if (r->kind != VX_R_LIMIT)
                fc_keep(c, &m);
            return;

        case VX_N_FOR:
            eval_for(c, fn, base, nd, n, r);
            return;

        case VX_N_LOOP:
            /* | n+1, s, .loop b => match eval P n s b with
                 | none => none
                 | some (.ok _, s₁) => eval P n s₁ (.loop b)
                 | some (.brk, s₁) => some (.ok .void, s₁)
                 | some (.fail | .ret v | .err k, s₁) => pass on, with s₁
               `eval P n s₁ (.loop b)` is unfolded: its fuel check, then the
               body with n - 1. */
            for (;;) {
                eval(c, fn, base, nd->a, n, r);
                if (r->kind == VX_R_OK) {
                    if (n == 0) {
                        set_limit(r, VX_L_FUEL);
                        return;
                    }
                    if (c->o->max_steps && ++c->steps > c->o->max_steps) {
                        set_limit(r, VX_L_FUEL);
                        return;
                    }
                    n = n - 1;
                    continue;
                }
                if (r->kind == VX_R_BRK)
                    set_void(r);
                return;
            }

        case VX_N_BRK:
            /* | _+1, s, .brk => some (.brk, s) */
            r->kind = VX_R_BRK;
            r->code = 0;
            return;

        case VX_N_RET:
            /* | n+1, s, .ret e => bindR (eval P n s e) fun v s₁ => some (.ret v, s₁) */
            eval(c, fn, base, nd->a, n, r);
            if (r->kind == VX_R_OK)
                r->kind = VX_R_RET;
            return;

        case VX_N_PRINT: {
            /* | n+1, s, .print e => bindR (eval P n s e) fun v s₁ =>
                 match printBytes v with
                 | some bs => some (.ok .void, { s₁ with out := s₁.out ++ bs })
                 | none => some (.err .type, s₁) */
            vx_val v;
            eval(c, fn, base, nd->a, n, r);
            if (r->kind != VX_R_OK)
                return;
            v = r->v;
            print_value(c, &v, r);
            return;
        }

        case VX_N_HEAP: {
            /* | n+1, s, .heap op es => bindL (evalList P n s es) fun vs s₁ =>
                   some ((op.apply vs s₁.g).1, { s₁ with g := (op.apply vs s₁.g).2 }) */
            size_t sp0 = c->vsp;
            eval_list(c, fn, base, nd->c, nd->b, n, r);
            if (r->kind != VX_R_OK)
                return;
            heap_apply(c, nd, &c->vs[sp0], nd->b, r);
            c->vsp = sp0;
            return;
        }

        default:
            /* not reachable: the loader accepts tags 0..12 only */
            set_err(r, VX_E_TYPE);
            return;
        }
    }
}

/* Bytes of C stack in use since vx_run (the safety net behind max_depth,
 * for builds whose frames are larger than the ones max_depth is sized for). */
static size_t stack_used(const vx_ctx *c)
{
    uintptr_t here = (uintptr_t)__builtin_frame_address(0);
    return here < c->stack_base ? (size_t)(c->stack_base - here) : (size_t)(here - c->stack_base);
}

/* One nested evaluation: bounds the C recursion depth. */
static void eval(vx_ctx *c, const vx_fn *fn, size_t base, uint32_t e, uint64_t fuel, vx_res *r)
{
    if (c->depth >= c->o->max_depth ||
        (c->o->stack_budget != 0 && stack_used(c) > c->o->stack_budget)) {
        set_limit(r, VX_L_DEPTH);
        return;
    }
    c->depth++;
    eval_node(c, fn, base, e, fuel, r);
    c->depth--;
}

/* ------------------------------------------------------------- the run */

/* Materialise every STR literal once, below every call's heap mark. */
static int make_literals(vx_ctx *c)
{
    const vx_program *p = c->p;
    uint32_t f, j, k;
    c->strlit = calloc(p->nfns, sizeof(size_t *));
    if (c->strlit == NULL)
        return 0;
    for (f = 0; f < p->nfns; f++) {
        const vx_fn *fn = &p->fns[f];
        for (j = 0; j < fn->nnodes; j++) {
            const vx_node *nd = &fn->nodes[j];
            size_t o;
            vx_val *el;
            if (nd->tag != VX_N_LIT || nd->op != VX_LIT_STR)
                continue;
            if (c->strlit[f] == NULL) {
                c->strlit[f] = calloc(fn->nnodes, sizeof(size_t));
                if (c->strlit[f] == NULL)
                    return 0;
            }
            if (vx_heap_alloc(&c->heap, nd->b, &o) != VX_OK)
                return 0;
            el = vx_obj_elems(&c->heap, o);
            for (k = 0; k < nd->b; k++) {
                el[k].tag = VX_T_CHAR;
                el[k].bits = p->bytes[nd->a + k];
            }
            c->strlit[f][j] = o;
        }
    }
    return 1;
}

void vx_default_opts(vx_opts *o)
{
    o->fuel = VX_DEFAULT_FUEL;
    o->max_steps = 0;
    o->max_depth = 5000;                 /* fits an 8 MiB stack, even under ASan */
    o->stack_budget = (size_t)6 << 20;
    o->max_heap = (size_t)1 << 26;     /* 1 GiB of cells */
    o->max_slots = (size_t)1 << 24;
    o->max_journal = (size_t)1 << 24;
    o->max_out = (size_t)1 << 30;
    o->max_vstack = (size_t)1 << 24;
    o->eager_range = 0;
}

/*
 * Prog.run P n = (eval P n Prog.initSt (.call P.main [])).map fun (r, s) => (r, s.out)
 *
 * with initSt = ⟨[], []⟩: an empty frame and no output.  The call node is
 * unfolded: eval's fuel check, `evalList P (n-1) s []` (its own fuel check),
 * then the call proper.
 */
void vx_run(const vx_program *p, const vx_opts *o, vx_outcome *res)
{
    vx_ctx c;
    vx_res r;
    vx_val *slots = malloc(INIT_SLOTS * sizeof(vx_val));
    vx_undo *jour = malloc(INIT_JOURNAL * sizeof(vx_undo));
    uint8_t *out = malloc(INIT_OUT);
    uint32_t f;

    memset(&c, 0, sizeof c);
    memset(res, 0, sizeof *res);
    c.p = p;
    c.o = o;
    c.stack_base = (uintptr_t)__builtin_frame_address(0);
    vx_store_init(&c.st, slots, INIT_SLOTS, jour, INIT_JOURNAL, out, INIT_OUT);
    vx_objs_init(&c.objs, o->max_heap, o->max_journal);
    c.vs = malloc(INIT_VSTACK * sizeof(vx_val));
    c.vcap = INIT_VSTACK;
    r.kind = VX_R_LIMIT;
    r.code = VX_L_MEMORY;
    if (slots != NULL && jour != NULL && out != NULL && c.vs != NULL &&
        vx_heap_init(&c.heap, o->max_heap) == VX_OK && make_literals(&c)) {
        if (o->fuel == 0) {
            set_limit(&r, VX_L_FUEL);               /* eval P 0 _ _ = none */
        } else {
            eval_list(&c, NULL, 0, 0, 0, o->fuel - 1, &r);   /* evalList P (n-1) s [] */
            if (r.kind == VX_R_OK)
                call_fn(&c, p->entry, c.vsp, 0, o->fuel - 1, &r);
        }
    }
    res->kind = r.kind;
    res->code = r.code;
    res->out = c.st.out;
    res->outlen = c.st.olen;
    res->heap_cells = c.heap.len;
    free(c.st.slots);
    free(c.st.jour);
    free(c.vs);
    free(c.scratch);
    if (c.strlit != NULL) {
        for (f = 0; f < p->nfns; f++)
            free(c.strlit[f]);
        free(c.strlit);
    }
    vx_heap_free(&c.heap);
    vx_objs_free(&c.objs);
    free(c.hmarks);
    free(c.dmax);
    free(c.dlo);
    free(c.dhi);
}

void vx_outcome_free(vx_outcome *res)
{
    free(res->out);
    res->out = NULL;
    res->outlen = 0;
}

const char *vx_err_name(int code)
{
    static const char *const names[] = { "overflow", "type", "slot", "call", "control", "user" };
    return code >= 0 && code <= VX_E_USER ? names[code] : "?";
}

const char *vx_limit_name(int code)
{
    static const char *const names[] = { "fuel exhausted", "recursion depth", "memory" };
    return code >= 0 && code <= VX_L_MEMORY ? names[code] : "?";
}

const char *vx_load_reason(int rc)
{
    static const char *const reasons[] = {
        "ok",
        "truncated input",
        "bad magic (not an OVBC file)",
        "unsupported version",
        "no functions",
        "main is not a function",
        "a function has more parameters than slots",
        "a function has no nodes",
        "a root is not a node of its function",
        "a child index is not below its node",
        "a slot is outside its function's frame",
        "a call names a function that does not exist",
        "a call's argument count differs from the callee's arity",
        "unknown node tag",
        "unknown primitive code",
        "a tupGet index on another primitive, or on the heap operation tag",
        "unknown literal kind",
        "a logic literal is not 0 or 1",
        "trailing bytes after the last function",
        "a count exceeds a limit of the loader",
        "out of memory",
        "unknown heap operation",
    };
    return rc >= 0 && rc <= VX_LOAD_LAST ? reasons[rc] : "?";
}
