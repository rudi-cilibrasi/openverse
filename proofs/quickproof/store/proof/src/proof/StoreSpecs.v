(* The specifications of the store functions the law reaches (runtime/src/store.c), over an
   abstract representation of the store: store_rep (the struct, the slot array and the journal)
   and out_rep (the output buffer).  The bodies are proved in StoreBodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require OpenverseStore.units.Store.
Require Import OpenverseStore.store.code.
Require Export OpenverseStore.proof.Model.

#[export] Instance CS : compspecs := OpenverseStore.units.Store.CS.
Definition Vprog : varspecs. mk_varspecs OpenverseStore.store.code.prog. Defined.

Definition t_val := Tstruct _vx_val noattr.
Definition t_undo := Tstruct _vx_undo noattr.
Definition t_store := Tstruct _vx_store noattr.
Definition t_mark := Tstruct _vx_mark noattr.

Definition vval (v: V) : reptype t_val := (Vlong (fst v), Vlong (snd v)).
Definition jval (e: J) : reptype t_undo :=
  (Vlong (Int64.repr (fst e)), (Vlong (fst (snd e)), Vlong (snd (snd e)))).
Definition mval (j o d: Z) : reptype t_mark :=
  (Vlong (Int64.repr j), (Vlong (Int64.repr o), Vlong (Int64.repr d))).
Definition bytes (bs: list Z) : list val := map (fun b => Vint (Int.repr b)) bs.

(* A malloc'd array of n elements: NULL is allowed only for n = 0 (malloc(0) may return NULL). *)
Definition buf (t: type) (sh: share) (n: Z) (l: list (reptype t)) (p: val) : mpred :=
  if eq_dec p nullval then !! (n = 0 /\ l = []) && emp else data_at sh (tarray t n) l p.

Definition sval (sp: val) (ns: Z) (jp: val) (jcap jlen: Z) (op: val) (ocap olen depth: Z)
  : reptype t_store :=
  (sp, (Vlong (Int64.repr ns), (jp, (Vlong (Int64.repr jcap), (Vlong (Int64.repr jlen),
   (op, (Vlong (Int64.repr ocap), (Vlong (Int64.repr olen), Vlong (Int64.repr depth))))))))).

(* The store at s: slots vs, journal js (oldest first), output length olen, depth. *)
Definition store_rep (shs shb: share) (s sp jp op: val) (jcap ocap: Z)
    (vs: list V) (js: list J) (olen depth: Z) : mpred :=
  EX jc: list (reptype t_undo),
  !! (Zlength vs <= Int64.max_unsigned /\ Zlength js <= jcap <= Int64.max_unsigned /\
      0 <= olen <= ocap /\ ocap <= Int64.max_unsigned /\ 0 <= depth <= Int64.max_unsigned /\
      Forall (fun e => 0 <= fst e < Zlength vs) js /\
      Zlength jc = jcap /\ sublist 0 (Zlength js) jc = map jval js) &&
  (data_at shs t_store (sval sp (Zlength vs) jp jcap (Zlength js) op ocap olen depth) s *
   buf t_val shb (Zlength vs) (map vval vs) sp *
   buf t_undo shb jcap jc jp).

(* The output buffer: its first Zlength os bytes are os. *)
Definition out_rep (sh: share) (ocap: Z) (os: list Z) (op: val) : mpred :=
  EX oc: list val,
  !! (Zlength oc = ocap /\ Zlength os <= ocap /\ sublist 0 (Zlength os) oc = bytes os) &&
  buf tuchar sh ocap oc op.

Definition vx_store_init_spec :=
  DECLARE _vx_store_init
  WITH s: val, shs: share, shb: share, sp: val, jp: val, op: val,
       vs: list V, jc: list (reptype t_undo), jcap: Z, oc: list val, ocap: Z
  PRE [ tptr t_store, tptr t_val, tulong, tptr t_undo, tulong, tptr tuchar, tulong ]
    PROP (writable_share shs; Zlength vs <= Int64.max_unsigned;
          0 <= jcap <= Int64.max_unsigned; 0 <= ocap <= Int64.max_unsigned;
          Zlength jc = jcap; Zlength oc = ocap)
    PARAMS (s; sp; Vlong (Int64.repr (Zlength vs)); jp; Vlong (Int64.repr jcap); op;
            Vlong (Int64.repr ocap))
    SEP (data_at_ shs t_store s; buf t_val shb (Zlength vs) (map vval vs) sp;
         buf t_undo shb jcap jc jp; buf tuchar shb ocap oc op)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (store_rep shs shb s sp jp op jcap ocap vs [] 0 0; out_rep shb ocap [] op).

Definition vx_store_get_spec :=
  DECLARE _vx_store_get
  WITH s: val, shs: share, shb: share, sp: val, jp: val, op: val, jcap: Z, ocap: Z,
       vs: list V, js: list J, olen: Z, depth: Z,
       slot: Z, pv: val, shv: share, vv: reptype t_val
  PRE [ tptr t_store, tulong, tptr t_val ]
    PROP (readable_share shs; readable_share shb; writable_share shv;
          0 <= slot <= Int64.max_unsigned)
    PARAMS (s; Vlong (Int64.repr slot); pv)
    SEP (store_rep shs shb s sp jp op jcap ocap vs js olen depth; data_at shv t_val vv pv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if slot <? Zlength vs then 0 else 3)))
    SEP (store_rep shs shb s sp jp op jcap ocap vs js olen depth;
         data_at shv t_val (if slot <? Zlength vs then vval (Znth slot vs) else vv) pv).

(* vx_store_set: VX_ESLOT (3) out of range, VX_EFULL (4) inside a context with a full journal,
   otherwise VX_OK (0), the slot written and, inside a context, the old value logged. *)
Definition set_ret (vs: list V) (js: list J) (jcap depth slot: Z) : Z :=
  if slot <? Zlength vs then (if andb (0 <? depth) (jcap <=? Zlength js) then 4 else 0) else 3.
Definition set_vs (vs: list V) (js: list J) (jcap depth slot: Z) (v: V) : list V :=
  if set_ret vs js jcap depth slot =? 0 then upd_Znth slot vs v else vs.
Definition set_js (vs: list V) (js: list J) (jcap depth slot: Z) : list J :=
  if andb (set_ret vs js jcap depth slot =? 0) (0 <? depth) then js ++ [(slot, Znth slot vs)] else js.

Definition vx_store_set_spec :=
  DECLARE _vx_store_set
  WITH s: val, shs: share, shb: share, sp: val, jp: val, op: val, jcap: Z, ocap: Z,
       vs: list V, js: list J, olen: Z, depth: Z, slot: Z, v: V
  PRE [ tptr t_store, tulong, tulong, tulong ]
    PROP (writable_share shs; writable_share shb; 0 <= slot <= Int64.max_unsigned)
    PARAMS (s; Vlong (Int64.repr slot); Vlong (fst v); Vlong (snd v))
    SEP (store_rep shs shb s sp jp op jcap ocap vs js olen depth)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (set_ret vs js jcap depth slot)))
    SEP (store_rep shs shb s sp jp op jcap ocap (set_vs vs js jcap depth slot v)
           (set_js vs js jcap depth slot) olen depth).

Definition vx_store_mark_spec :=
  DECLARE _vx_store_mark
  WITH s: val, shs: share, shb: share, sp: val, jp: val, op: val, jcap: Z, ocap: Z,
       vs: list V, js: list J, olen: Z, depth: Z, pm: val, shm: share, mv: reptype t_mark
  PRE [ tptr t_store, tptr t_mark ]
    PROP (writable_share shs; writable_share shm; depth < Int64.max_unsigned)
    PARAMS (s; pm)
    SEP (store_rep shs shb s sp jp op jcap ocap vs js olen depth; data_at shm t_mark mv pm)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (store_rep shs shb s sp jp op jcap ocap vs js olen (depth + 1);
         data_at shm t_mark (mval (Zlength js) olen depth) pm).

Definition vx_store_rollback_spec :=
  DECLARE _vx_store_rollback
  WITH s: val, shs: share, shb: share, sp: val, jp: val, op: val, jcap: Z, ocap: Z,
       vs: list V, js: list J, olen: Z, depth: Z, pm: val, shm: share, mj: Z, mo: Z, md: Z
  PRE [ tptr t_store, tptr t_mark ]
    PROP (writable_share shs; writable_share shb; readable_share shm;
          0 <= mj <= Zlength js; 0 <= mo <= Int64.max_unsigned; 0 <= md <= Int64.max_unsigned)
    PARAMS (s; pm)
    SEP (store_rep shs shb s sp jp op jcap ocap vs js olen depth;
         data_at shm t_mark (mval mj mo md) pm)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (store_rep shs shb s sp jp op jcap ocap (undo (sublist mj (Zlength js) js) vs)
           (if md =? 0 then [] else sublist 0 mj js) (Z.min olen mo) md;
         data_at shm t_mark (mval mj mo md) pm).

Definition vx_store_commit_spec :=
  DECLARE _vx_store_commit
  WITH s: val, shs: share, shb: share, sp: val, jp: val, op: val, jcap: Z, ocap: Z,
       vs: list V, js: list J, olen: Z, depth: Z, pm: val, shm: share, mj: Z, mo: Z, md: Z
  PRE [ tptr t_store, tptr t_mark ]
    PROP (writable_share shs; readable_share shm; 0 <= md <= Int64.max_unsigned)
    PARAMS (s; pm)
    SEP (store_rep shs shb s sp jp op jcap ocap vs js olen depth;
         data_at shm t_mark (mval mj mo md) pm)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (store_rep shs shb s sp jp op jcap ocap vs (if md =? 0 then [] else js) olen md;
         data_at shm t_mark (mval mj mo md) pm).

Definition vx_store_out_append_spec :=
  DECLARE _vx_store_out_append
  WITH s: val, shs: share, shb: share, sp: val, jp: val, op: val, jcap: Z, ocap: Z,
       vs: list V, js: list J, depth: Z, os: list Z, pb: val, shp: share, bs: list Z, n: Z
  PRE [ tptr t_store, tptr tuchar, tulong ]
    PROP (writable_share shs; writable_share shb; readable_share shp;
          0 <= n <= Zlength bs; Zlength bs <= Int64.max_unsigned;
          Forall (fun b => 0 <= b <= Byte.max_unsigned) bs)
    PARAMS (s; pb; Vlong (Int64.repr n))
    SEP (store_rep shs shb s sp jp op jcap ocap vs js (Zlength os) depth;
         out_rep shb ocap os op;
         data_at shp (tarray tuchar (Zlength bs)) (bytes bs) pb)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if ocap - Zlength os <? n then 4 else 0)))
    SEP (store_rep shs shb s sp jp op jcap ocap vs js
           (if ocap - Zlength os <? n then Zlength os else Zlength os + n) depth;
         out_rep shb ocap (if ocap - Zlength os <? n then os else os ++ sublist 0 n bs) op;
         data_at shp (tarray tuchar (Zlength bs)) (bytes bs) pb).

Definition vx_store_out_len_spec :=
  DECLARE _vx_store_out_len
  WITH s: val, shs: share, shb: share, sp: val, jp: val, op: val, jcap: Z, ocap: Z,
       vs: list V, js: list J, olen: Z, depth: Z
  PRE [ tptr t_store ]
    PROP (readable_share shs)
    PARAMS (s)
    SEP (store_rep shs shb s sp jp op jcap ocap vs js olen depth)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr olen))
    SEP (store_rep shs shb s sp jp op jcap ocap vs js olen depth).

(* The store functions call nothing. *)
Definition Gprog : funspecs := [].

(* Lemmas about the representation. *)

Lemma buf_local_facts: forall t sh n l p,
  buf t sh n l p |-- !! (is_pointer_or_null p).
Proof.
  intros. unfold buf. destruct (eq_dec p nullval).
  - subst. entailer!.
  - entailer!.
Qed.
#[export] Hint Resolve buf_local_facts : saturate_local.

Lemma buf_nonnull: forall t sh n l p,
  0 < n -> buf t sh n l p = data_at sh (tarray t n) l p.
Proof.
  intros. unfold buf. destruct (eq_dec p nullval); auto.
  subst. apply pred_ext.
  - Intros. lia.
  - rewrite data_at_isptr. Intros. contradiction.
Qed.

Lemma out_rep_trunc: forall sh ocap os op k,
  0 <= k <= Zlength os ->
  out_rep sh ocap os op |-- out_rep sh ocap (sublist 0 k os) op.
Proof.
  intros. unfold out_rep. Intros oc. Exists oc.
  assert (E: sublist 0 k oc = bytes (sublist 0 k os)).
  { rewrite <- (sublist_sublist00 k (Zlength os) oc) by lia.
    match goal with H: sublist 0 (Zlength os) oc = _ |- _ => rewrite H end.
    unfold bytes. rewrite sublist_map. reflexivity. }
  rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
  entailer!.
Qed.
