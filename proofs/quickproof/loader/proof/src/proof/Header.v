(* Body of load_header. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
Require Import OpenverseLoader.proof.LoadLemmas.
#[local] Existing Instance Specs.CS.

Definition byte_val (v: val) : Prop := exists x, v = Vint (Int.repr x) /\ 0 <= x <= 255.

Ltac dz :=
  repeat match goal with
  | |- context [Z.eq_dec ?a ?b] => destruct (Z.eq_dec a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  | H: context [Z.eq_dec ?a ?b] |- _ => destruct (Z.eq_dec a b)
  end; simpl in *; try congruence;
  try (exfalso; apply Int.one_not_zero; assumption);
  try (exfalso; auto; fail); auto.

Lemma fr1: forall p qa k,
  (data_at Tsh t_prog (PRG 0 0 nullval qa 0 nullval 0) p *
   malloc_token Ews (tarray tuint k) qa * data_at_ Ews (tarray tuint k) qa |-- freeable p)%logic.
Proof.
  intros. sep_apply (blk_fold (tarray tuint k) qa).
  eapply derives_trans; [ | apply (freeable_nofns p (Vint (Int.repr 0)) qa (Vint (Int.repr 0)) nullval
                                    (Vint (Int.repr 0)) k 0) ].
  rewrite blk_null. cancel.
Qed.

Lemma fr2: forall p qa qb k k',
  (data_at Tsh t_prog (PRG 0 0 nullval qa 0 qb 0) p *
   malloc_token Ews (tarray tuint k) qa * data_at_ Ews (tarray tuint k) qa *
   malloc_token Ews (tarray tuchar k') qb * data_at_ Ews (tarray tuchar k') qb |-- freeable p)%logic.
Proof.
  intros. sep_apply (blk_fold (tarray tuint k) qa). sep_apply (blk_fold (tarray tuchar k') qb).
  eapply derives_trans; [ | apply (freeable_nofns p (Vint (Int.repr 0)) qa (Vint (Int.repr 0)) qb
                                    (Vint (Int.repr 0)) k k') ].
  cancel.
Qed.

Lemma sizeof_tarray_tuint: forall k, 0 <= k -> sizeof (tarray tuint k) = 4 * k.
Proof. intros. simpl. rewrite Z.max_r by lia. lia. Qed.

Lemma pool_a0: forall q k,
  (malloc_token Ews (tarray tuint k) q * data_at_ Ews (tarray tuint k) q |-- args_pool q k nil)%logic.
Proof.
  intros. unfold args_pool.
  rewrite (data_at__tarray' Ews tuint k (vints nil ++ Zrepeat Vundef (k - Zlength (@nil Z)))).
  - cancel.
  - rewrite Zlength_nil, Z.sub_0_r. reflexivity.
Qed.

Lemma pool_b0: forall q k,
  (malloc_token Ews (tarray tuchar k) q * data_at_ Ews (tarray tuchar k) q |-- bytes_pool q k nil)%logic.
Proof.
  intros. unfold bytes_pool.
  rewrite (data_at__tarray' Ews tuchar k (vints nil ++ Zrepeat Vundef (k - Zlength (@nil Z)))).
  - cancel.
  - rewrite Zlength_nil, Z.sub_0_r. reflexivity.
Qed.

Lemma upd_fill_rep {A} {dA: Inhabitant A}: forall (z e: A) i n, 0 <= i < n ->
  upd_Znth i (Zrepeat z i ++ Zrepeat e (n - i)) z = Zrepeat z (i + 1) ++ Zrepeat e (n - (i + 1)).
Proof. intros. list_solve. Qed.

Lemma upd_fill_rep2 {A} {dA: Inhabitant A}: forall (z e v: A) i n, 0 <= i < n ->
  upd_Znth i (upd_Znth i (Zrepeat z i ++ Zrepeat e (n - i)) v) z = Zrepeat z (i + 1) ++ Zrepeat e (n - (i + 1)).
Proof. intros. rewrite upd_Znth_twice by list_solve. list_solve. Qed.

Ltac zside := first [ (rewrite ?Zlength_upd_Znth, ?Zlength_app, ?Zlength_Zrepeat by lia; lia) | list_solve ].

(* After a store into one field of element i of the function table: the element's other fields are the
   previous value's. *)
Ltac fclean EZ :=
  rewrite ?EZ;
  repeat match goal with
  | |- context [@Znth ?A ?d ?i (upd_Znth ?i ?l ?u)] => rewrite (@upd_Znth_same A d i l u) by zside
  end;
  repeat match goal with
  | |- context [upd_Znth ?i (upd_Znth ?i ?l ?x) ?y] => rewrite (@upd_Znth_twice _ i l x y) by zside
  end;
  cbn [fst snd].

Lemma body_load_header: semax_body Vprog Gprog f_load_header load_header_spec.
Proof.
  start_function.
  forward_call (r, buf, shb, bs, pos, 0, 0, v_m0, Tsh).
  Intros vret. destruct vret as [[[rc0 p0] x0] w0]. cbn [fst snd] in *.
  forward_if (EX pa: Z, EX w1: val, EX t2: Z,
    PROP (0 <= pa <= Zlength bs; t2 = 0 \/ t2 = 1; t2 = 0 -> byte_val w0 /\ byte_val w1)
    LOCAL (temp _t'2 (Vint (Int.repr t2)); lvar _entry_fn tuint v_entry_fn; lvar _nfns tuint v_nfns;
           lvar _ver tuint v_ver; lvar _m3 tuint v_m3; lvar _m2 tuint v_m2; lvar _m1 tuint v_m1;
           lvar _m0 tuint v_m0; gvars gv; temp _r r; temp _p p)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) pa 0 0) r; buf_rep shb bs buf;
         data_at Tsh tuint w0 v_m0; data_at Tsh tuint w1 v_m1;
         data_at_ Tsh tuint v_m2; data_at_ Tsh tuint v_m3; data_at_ Tsh tuint v_ver;
         data_at_ Tsh tuint v_nfns; data_at_ Tsh tuint v_entry_fn;
         data_at Tsh t_prog PRG0 p; mem_mgr gv))%assert.
  { rewrite (data_at__eq Tsh tuint v_m1). forward. Exists p0 (default_val tuint) 1. entailer!. }
  { forward_call (r, buf, shb, bs, p0, 0, 0, v_m1, Tsh).
    Intros vret. destruct vret as [[[rc1 p1] x1] w1]. cbn [fst snd] in *.
    match goal with H: rc1 = 0 \/ rc1 = 1 |- _ => destruct H as [E | E]; subst rc1 end.
    { match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [-> Hx1]; clear H end.
      forward. Exists p1 (Vint (Int.repr x1)) 0. entailer!.
      try intros _. split; [ exists x0; tauto | exists x1; split; [ reflexivity | lia ] ]. }
    { forward. Exists p1 w1 1. entailer!. } }
  Intros pa w1 t2.
  forward_if (EX pb: Z, EX w2: val, EX t4: Z,
    PROP (0 <= pb <= Zlength bs; t4 = 0 \/ t4 = 1; t4 = 0 -> byte_val w0 /\ byte_val w1 /\ byte_val w2)
    LOCAL (temp _t'4 (Vint (Int.repr t4)); lvar _entry_fn tuint v_entry_fn; lvar _nfns tuint v_nfns;
           lvar _ver tuint v_ver; lvar _m3 tuint v_m3; lvar _m2 tuint v_m2; lvar _m1 tuint v_m1;
           lvar _m0 tuint v_m0; gvars gv; temp _r r; temp _p p)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) pb 0 0) r; buf_rep shb bs buf;
         data_at Tsh tuint w0 v_m0; data_at Tsh tuint w1 v_m1; data_at Tsh tuint w2 v_m2;
         data_at_ Tsh tuint v_m3; data_at_ Tsh tuint v_ver;
         data_at_ Tsh tuint v_nfns; data_at_ Tsh tuint v_entry_fn;
         data_at Tsh t_prog PRG0 p; mem_mgr gv))%assert.
  { rewrite (data_at__eq Tsh tuint v_m2). forward. Exists pa (default_val tuint) 1. entailer!. }
  { match goal with H: t2 = 0 \/ t2 = 1 |- _ => destruct H as [ | ]; subst t2; [ | exfalso; apply Int.one_not_zero; auto ] end.
    match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as (B0 & B1) end.
    forward_call (r, buf, shb, bs, pa, 0, 0, v_m2, Tsh).
    Intros vret. destruct vret as [[[rc2 p2] x2] w2]. cbn [fst snd] in *.
    match goal with H: rc2 = 0 \/ rc2 = 1 |- _ => destruct H as [E | E]; subst rc2 end.
    { match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [-> Hx2]; clear H end.
      forward. Exists p2 (Vint (Int.repr x2)) 0. entailer!.
      try intros _. split; [ auto | split; [ auto | exists x2; split; [ reflexivity | lia ] ] ]. }
    { forward. Exists p2 w2 1. entailer!. } }
  Intros pb w2 t4.
  forward_if (EX pc: Z, EX w3: val, EX t6: Z,
    PROP (0 <= pc <= Zlength bs; t6 = 0 \/ t6 = 1;
          t6 = 0 -> byte_val w0 /\ byte_val w1 /\ byte_val w2 /\ byte_val w3)
    LOCAL (temp _t'6 (Vint (Int.repr t6)); lvar _entry_fn tuint v_entry_fn; lvar _nfns tuint v_nfns;
           lvar _ver tuint v_ver; lvar _m3 tuint v_m3; lvar _m2 tuint v_m2; lvar _m1 tuint v_m1;
           lvar _m0 tuint v_m0; gvars gv; temp _r r; temp _p p)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) pc 0 0) r; buf_rep shb bs buf;
         data_at Tsh tuint w0 v_m0; data_at Tsh tuint w1 v_m1; data_at Tsh tuint w2 v_m2;
         data_at Tsh tuint w3 v_m3; data_at_ Tsh tuint v_ver;
         data_at_ Tsh tuint v_nfns; data_at_ Tsh tuint v_entry_fn;
         data_at Tsh t_prog PRG0 p; mem_mgr gv))%assert.
  { rewrite (data_at__eq Tsh tuint v_m3). forward. Exists pb (default_val tuint) 1. entailer!. }
  { match goal with H: t4 = 0 \/ t4 = 1 |- _ => destruct H as [ | ]; subst t4; [ | exfalso; apply Int.one_not_zero; auto ] end.
    match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as (B0 & B1 & B2) end.
    forward_call (r, buf, shb, bs, pb, 0, 0, v_m3, Tsh).
    Intros vret. destruct vret as [[[rc3 p3] x3] w3]. cbn [fst snd] in *.
    match goal with H: rc3 = 0 \/ rc3 = 1 |- _ => destruct H as [E | E]; subst rc3 end.
    { match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [-> Hx3]; clear H end.
      forward. Exists p3 (Vint (Int.repr x3)) 0. entailer!.
      try intros _. split; [ auto | split; [ auto | split; [ auto | exists x3; split; [ reflexivity | lia ] ] ] ]. }
    { forward. Exists p3 w3 1. entailer!. } }
  Intros pc w3 t6.
  forward_if.
  { forward. Exists 1 pc 0 0. rewrite if_false by lia. sep_apply (freeable_PRG0 p). entailer!. }
  match goal with H: t6 = 0 \/ t6 = 1 |- _ => destruct H as [ | ]; subst t6; [ | exfalso; apply Int.one_not_zero; auto ] end.
  match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as ((y0 & -> & Y0) & (y1 & -> & Y1) &
                                                                  (y2 & -> & Y2) & (y3 & -> & Y3)) end.
  forward.
  forward_if (temp _t'8 (Vint (Int.repr (if Z.eq_dec y0 79 then if Z.eq_dec y1 86 then 0 else 1 else 1)))).
  { forward. entailer!. dz. }
  { forward. forward. entailer!. dz. }
  forward_if (temp _t'9 (Vint (Int.repr (if Z.eq_dec y0 79 then if Z.eq_dec y1 86 then
                                          if Z.eq_dec y2 66 then 0 else 1 else 1 else 1)))).
  { forward. entailer!. dz. }
  { forward. forward. entailer!. dz. }
  forward_if (temp _t'10 (Vint (Int.repr (if Z.eq_dec y0 79 then if Z.eq_dec y1 86 then
                                          if Z.eq_dec y2 66 then if Z.eq_dec y3 67 then 0 else 1 else 1 else 1 else 1)))).
  { forward. entailer!. dz. }
  { forward. forward. entailer!. dz. }
  forward_if.
  { forward. Exists 2 pc 0 0. rewrite if_false by lia. sep_apply (freeable_PRG0 p). entailer!. }
  (* version *)
  forward_call (r, buf, shb, bs, pc, 0, 0, v_ver, Tsh).
  Intros vret. destruct vret as [[[rc4 p4] vr] wv]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p4 0 0. rewrite (if_false (1 = 0)) by lia. sep_apply (freeable_PRG0 p). entailer!. }
  match goal with H: rc4 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [-> Hvr]; clear H end.
  forward. forward_if.
  { forward. Exists 3 p4 0 0. rewrite (if_false (3 = 0)) by lia. sep_apply (freeable_PRG0 p). entailer!. }
  (* nfns *)
  forward_call (r, buf, shb, bs, p4, 0, 0, v_nfns, Tsh).
  Intros vret. destruct vret as [[[rc5 p5] nf] wn]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p5 0 0. rewrite (if_false (1 = 0)) by lia. sep_apply (freeable_PRG0 p). entailer!. }
  match goal with H: rc5 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [-> Hnf]; clear H end.
  forward. forward_if.
  { forward. Exists 4 p5 0 0. rewrite (if_false (4 = 0)) by lia. sep_apply (freeable_PRG0 p). entailer!. }
  forward. forward_if.
  { forward. Exists 19 p5 0 0. rewrite (if_false (19 = 0)) by lia. sep_apply (freeable_PRG0 p). entailer!. }
  rewrite ?shl_1_16 in *. simpl_ints.
  (* main *)
  forward_call (r, buf, shb, bs, p5, 0, 0, v_entry_fn, Tsh).
  Intros vret. destruct vret as [[[rc6 p6] en] we]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p6 0 0. rewrite (if_false (1 = 0)) by lia. sep_apply (freeable_PRG0 p). entailer!. }
  match goal with H: rc6 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [-> Hen]; clear H end.
  forward. forward. forward_if.
  { forward. Exists 5 p6 0 0. rewrite (if_false (5 = 0)) by lia. sep_apply (freeable_PRG0 p). entailer!. }
  (* rest *)
  forward. forward. forward.
  rewrite i64_sub_repr.
  remember (Zlength bs - p6) as rest eqn:Erest.
  assert (Hrest: 0 <= rest <= MAXIN) by lia.
  clear Erest.
  forward.
  forward_if.
  { forward. Exists 1 p6 0 0. rewrite (if_false (1 = 0)) by lia. sep_apply (freeable_PRG0 p). entailer!. }
  assert (R22a: 0 <= rest / 22 <= rest) by (split; [ apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia ]).
  assert (R4: 0 <= rest / 4 <= rest) by (split; [ apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia ]).
  simpl_ints. rewrite ?i64_divu_repr in * by rep_lia. simpl_ints.
  assert (R22: 22 <= rest).
  { assert (nf <= rest / 22) by lia. assert (1 <= rest / 22) by lia.
    pose proof (Z.mul_div_le rest 22 ltac:(lia)). lia. }
  forward_call (tarray tuint (rest / 4), gv).
  { entailer!. simpl. rewrite Z.max_r by (apply Z.div_pos; lia).
    do 3 f_equal; lia. }
  { rewrite sizeof_tarray_tuint by (apply Z.div_pos; lia).
    rep_lia. }
  Intros qa.
  forward. forward.
  forward_if.
  { apply derives_trans with ((if eq_dec qa nullval then emp else
      malloc_token Ews (tarray tuint (rest / 4)) qa * data_at_ Ews (tarray tuint (rest / 4)) qa) * TT)%logic;
      [ cancel | apply malloc_test_null; simpl; rep_lia ]. }
  { forward. Exists 20 p6 0 0. rewrite (if_false (20 = 0)) by lia. sep_apply (freeable_PRG0 p). entailer!. }
  rewrite (if_false (qa = nullval)) by auto. Intros.
  forward.
  forward_call (tarray tuchar rest, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros qb.
  forward. forward.
  forward_if.
  { apply derives_trans with ((if eq_dec qb nullval then emp else
      malloc_token Ews (tarray tuchar rest) qb * data_at_ Ews (tarray tuchar rest) qb) * TT)%logic;
      [ cancel | apply malloc_test_null; simpl; rep_lia ]. }
  { forward. Exists 20 p6 (rest / 4) 0. rewrite (if_false (20 = 0)) by lia. sep_apply (fr1 p qa (rest / 4)). entailer!. }
  rewrite (if_false (qb = nullval)) by auto. Intros.
  forward. forward.
  forward_call (tarray t_fn nf, gv).
  { entailer!. simpl. rewrite Z.max_r by lia.
    do 3 f_equal; lia. }
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros qf.
  forward. forward.
  forward_if.
  { apply derives_trans with ((if eq_dec qf nullval then emp else
      malloc_token Ews (tarray t_fn nf) qf * data_at_ Ews (tarray t_fn nf) qf) * TT)%logic;
      [ cancel | apply malloc_test_null; simpl; rep_lia ]. }
  { forward. Exists 20 p6 (rest / 4) rest. rewrite (if_false (20 = 0)) by lia.
    sep_apply (fr2 p qa qb (rest / 4) rest). entailer!. }
  rewrite (if_false (qf = nullval)) by auto. Intros.
  rewrite (data_at__tarray Ews t_fn nf).
  forward.
  forward_loop (EX i: Z,
    PROP (0 <= i <= nf)
    LOCAL (temp _f (Vint (Int.repr i)); temp _rest (Vlong (Int64.repr rest));
           lvar _entry_fn tuint v_entry_fn; lvar _nfns tuint v_nfns;
           lvar _ver tuint v_ver; lvar _m3 tuint v_m3; lvar _m2 tuint v_m2; lvar _m1 tuint v_m1;
           lvar _m0 tuint v_m0; gvars gv; temp _r r; temp _p p)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) p6 (rest / 4) rest) r; buf_rep shb bs buf;
         data_at Tsh tuint (Vint (Int.repr y0)) v_m0; data_at Tsh tuint (Vint (Int.repr y1)) v_m1;
         data_at Tsh tuint (Vint (Int.repr y2)) v_m2; data_at Tsh tuint (Vint (Int.repr y3)) v_m3;
         data_at Tsh tuint (Vint (Int.repr vr)) v_ver; data_at Tsh tuint (Vint (Int.repr nf)) v_nfns;
         data_at Tsh tuint (Vint (Int.repr en)) v_entry_fn;
         data_at Tsh t_prog (PRG 0 0 qf qa 0 qb 0) p;
         malloc_token Ews (tarray tuint (rest / 4)) qa; data_at_ Ews (tarray tuint (rest / 4)) qa;
         malloc_token Ews (tarray tuchar rest) qb; data_at_ Ews (tarray tuchar rest) qb;
         malloc_token Ews (tarray t_fn nf) qf;
         data_at Ews (tarray t_fn nf) (Zrepeat (fn_val zero_fn) i ++ Zrepeat (default_val t_fn) (nf - i)) qf;
         mem_mgr gv))%assert
  continue: (EX i: Z,
    PROP (0 <= i < nf)
    LOCAL (temp _f (Vint (Int.repr i)); temp _rest (Vlong (Int64.repr rest));
           lvar _entry_fn tuint v_entry_fn; lvar _nfns tuint v_nfns;
           lvar _ver tuint v_ver; lvar _m3 tuint v_m3; lvar _m2 tuint v_m2; lvar _m1 tuint v_m1;
           lvar _m0 tuint v_m0; gvars gv; temp _r r; temp _p p)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) p6 (rest / 4) rest) r; buf_rep shb bs buf;
         data_at Tsh tuint (Vint (Int.repr y0)) v_m0; data_at Tsh tuint (Vint (Int.repr y1)) v_m1;
         data_at Tsh tuint (Vint (Int.repr y2)) v_m2; data_at Tsh tuint (Vint (Int.repr y3)) v_m3;
         data_at Tsh tuint (Vint (Int.repr vr)) v_ver; data_at Tsh tuint (Vint (Int.repr nf)) v_nfns;
         data_at Tsh tuint (Vint (Int.repr en)) v_entry_fn;
         data_at Tsh t_prog (PRG 0 0 qf qa 0 qb 0) p;
         malloc_token Ews (tarray tuint (rest / 4)) qa; data_at_ Ews (tarray tuint (rest / 4)) qa;
         malloc_token Ews (tarray tuchar rest) qb; data_at_ Ews (tarray tuchar rest) qb;
         malloc_token Ews (tarray t_fn nf) qf;
         data_at Ews (tarray t_fn nf) (Zrepeat (fn_val zero_fn) (i + 1)%Z ++ Zrepeat (default_val t_fn) (nf - (i + 1))%Z) qf;
         mem_mgr gv))%assert
  break: (PROP ()
    LOCAL (temp _rest (Vlong (Int64.repr rest));
           lvar _entry_fn tuint v_entry_fn; lvar _nfns tuint v_nfns;
           lvar _ver tuint v_ver; lvar _m3 tuint v_m3; lvar _m2 tuint v_m2; lvar _m1 tuint v_m1;
           lvar _m0 tuint v_m0; gvars gv; temp _r r; temp _p p)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) p6 (rest / 4) rest) r; buf_rep shb bs buf;
         data_at Tsh tuint (Vint (Int.repr y0)) v_m0; data_at Tsh tuint (Vint (Int.repr y1)) v_m1;
         data_at Tsh tuint (Vint (Int.repr y2)) v_m2; data_at Tsh tuint (Vint (Int.repr y3)) v_m3;
         data_at Tsh tuint (Vint (Int.repr vr)) v_ver; data_at Tsh tuint (Vint (Int.repr nf)) v_nfns;
         data_at Tsh tuint (Vint (Int.repr en)) v_entry_fn;
         data_at Tsh t_prog (PRG 0 0 qf qa 0 qb 0) p;
         malloc_token Ews (tarray tuint (rest / 4)) qa; data_at_ Ews (tarray tuint (rest / 4)) qa;
         malloc_token Ews (tarray tuchar rest) qb; data_at_ Ews (tarray tuchar rest) qb;
         malloc_token Ews (tarray t_fn nf) qf;
         data_at Ews (tarray t_fn nf) (Zrepeat (fn_val zero_fn) nf) qf;
         mem_mgr gv))%assert.
  - Exists 0. try change (Int.signed (Int.repr 4)) with 4. rewrite i64_divu_repr by rep_lia.
    rewrite Zrepeat_0, app_nil_l, Z.sub_0_r. entailer!.
  - Intros i. forward. forward_if.
    2: { forward. assert (E: i = nf) by lia. subst i.
         rewrite Z.sub_diag, Zrepeat_0, app_nil_r. entailer!. }
    assert (EZ: forall d, @Znth _ d i (Zrepeat (fn_val zero_fn) i ++ Zrepeat (default_val t_fn) (nf - i)) =
                          default_val t_fn).
    { intros d. rewrite Znth_app2 by (rewrite Zlength_Zrepeat; lia).
      rewrite Zlength_Zrepeat by lia. rewrite Z.sub_diag. apply Znth_Zrepeat. lia. }
    forward. forward. fclean EZ.
    forward. forward. fclean EZ.
    forward. forward. fclean EZ.
    forward. forward. fclean EZ.
    forward. forward. fclean EZ.
    forward. forward. fclean EZ.
    forward. forward. fclean EZ.
    forward. forward. fclean EZ.
    match goal with |- context [data_at Ews (tarray t_fn nf) (upd_Znth i ?L ?V) qf] =>
      replace (upd_Znth i L V) with (Zrepeat (fn_val zero_fn) (i + 1) ++ Zrepeat (default_val t_fn) (nf - (i + 1)))
    end.
    2: { symmetry.
         first [ (apply (@upd_fill_rep2 _ (fn_val zero_fn)); lia)
               | (apply (@upd_fill_rep _ (fn_val zero_fn)); lia) ]. }
    try forward.
    Exists i. entailer!.
  - Intros i. forward. Exists (i + 1). entailer!.
  - forward. forward. forward. forward. forward.
    Exists 0 p6 (rest / 4) rest.
    destruct (Z.eq_dec 0 0) as [_ | NE]; [ | congruence ].
    Exists nf en qf qa qb.
    sep_apply (pool_a0 qa (rest / 4)). sep_apply (pool_b0 qb rest).
    entailer!.
Qed.
