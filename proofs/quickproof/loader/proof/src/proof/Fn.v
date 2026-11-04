(* Body of load_fn. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
Require Import OpenverseLoader.proof.Fields.
#[local] Existing Instance Specs.CS.

(* The node table under construction, kept folded so that the entailment tactics do not unfold it. *)
Definition narr (n: Z) (L: list (reptype t_node)) (q: val) : mpred := data_at Ews (tarray t_node n) L q.
Lemma narr_fold: forall n L q, data_at Ews (tarray t_node n) L q = narr n L q.
Proof. reflexivity. Qed.

(* An error return of load_fn before the node table is allocated. *)
Ltac fn_err0 rc pos' bl :=
  forward;
  Exists rc pos' (@nil Z) bl zero_fn;
  match goal with |- context [data_at Ews t_fn ?V _] => Exists V end;
  Exists 0; rewrite app_nil_r;
  rewrite if_false by lia; unfold fn_nodes; cbn [fst snd]; rewrite blk_null;
  entailer!; unfold u32_ok; auto.

(* An error return of load_fn after the node table is allocated. *)
Ltac fn_errq rc pos' xs bl' nn q :=
  forward; Exists rc pos' xs bl' zero_fn;
  match goal with |- context [data_at Ews t_fn ?V _] => Exists V end;
  Exists nn; rewrite if_false by lia; unfold fn_nodes; cbn [fst snd]; unfold narr;
  sep_apply (blk_of_data_at (tarray t_node nn) q); entailer!.

Lemma u32_of_lt: forall (l: list Z) j, j <= Int.max_unsigned -> Forall (fun y => 0 <= y < j) l -> u32_ok l.
Proof. intros. unfold u32_ok. eapply Forall_impl; [ | eassumption ]. simpl. intros; lia. Qed.

Lemma body_load_fn: semax_body Vprog Gprog f_load_fn load_fn_spec.
Proof.
  start_function.
  set (fnp := field_address (tarray t_fn nfns) [ArraySubsc f] fns).
  unfold fn_val, zero_fn; cbn [f_arity f_nslots f_dec f_off f_len f_root f_q f_body].
  change (Zlength (@nil node)) with 0.
  set (z := Vint (Int.repr 0)).
  assert_PROP (field_compatible t_fn [] fnp) as FCf by entailer!.
  assert (FCo: field_compatible t_fn (DOT _name_off) fnp) by auto with field_compatible.
  forward. forward.
  rewrite (add_ptr_uint_field t_fn nfns f fns) by (auto; rep_lia). fold fnp.
  forward_call (r, buf, shb, bs, pos, acap, bcap, v_arity, Tsh).
  Intros vret. destruct vret as [[[rc1 p1] ar] va]. cbn [fst snd] in *.
  forward_if. { fn_err0 1 p1 bl. }
  match goal with H: rc1 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [-> Har]; clear H end.
  forward_call (r, buf, shb, bs, p1, acap, bcap, v_nslots, Tsh).
  Intros vret. destruct vret as [[[rc2 p2] ns] vn]. cbn [fst snd] in *.
  forward_if. { fn_err0 1 p2 bl. }
  match goal with H: rc2 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [-> Hns]; clear H end.
  forward_call (r, buf, shb, bs, p2, acap, bcap, v_dec, Tsh).
  Intros vret. destruct vret as [[[rc3 p3] dc] vd]. cbn [fst snd] in *.
  forward_if. { fn_err0 1 p3 bl. }
  match goal with H: rc3 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [-> Hdc]; clear H end.
  forward.
  forward_if. { fn_err0 19 p3 bl. }
  forward. forward.
  forward_if. { fn_err0 6 p3 bl. }
  forward. forward. forward. forward. forward. forward.
  forward_call (r, buf, shb, bs, p3, acap, bcap, v_namelen, Tsh).
  Intros vret. destruct vret as [[[rc4 p4] nl] vl]. cbn [fst snd] in *.
  forward_if. { fn_err0 1 p4 bl. }
  match goal with H: rc4 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [-> Hnl]; clear H end.
  rewrite ?shl_1_16, ?shl_1_22 in *. simpl_ints.
  forward.
  sep_apply (fn_take_off Ews (Vint (Int.repr ar)) (Vint (Int.repr ns)) (Vint (Int.repr dc)) z z z z nullval fnp).
  forward_call (r, buf, shb, bs, p4, acap, bcap, p, nfns, entry, fns, args, Zlength al, bytes, bl, nl,
                field_address t_fn (DOT _name_off) fnp, Ews).
  { cancel. }
  Intros vret. destruct vret as [[[rc5 p5] bl1] vo]. cbn [fst snd] in *.
  sep_apply (fn_fold_off Ews (Vint (Int.repr ar)) (Vint (Int.repr ns)) (Vint (Int.repr dc)) vo z z z nullval fnp).
  forward.
  forward_if. { fn_err0 rc5 p5 bl1. }
  match goal with H: rc5 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [Hbl1 ->]; clear H end.
  forward. forward.
  forward_call (r, buf, shb, bs, p5, acap, bcap, v_nnodes, Tsh).
  Intros vret. destruct vret as [[[rc6 p6] nn] vnn]. cbn [fst snd] in *.
  forward_if. { fn_err0 1 p6 bl1. }
  match goal with H: rc6 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [-> Hnn]; clear H end.
  forward.
  forward_if. { fn_err0 7 p6 bl1. }
  forward.
  forward_if. { fn_err0 19 p6 bl1. }
  forward. forward. forward.
  forward_if. { fn_err0 1 p6 bl1. }
  rewrite ?shl_1_16, ?shl_1_22 in *. simpl_ints.
  forward.
  forward_call (tarray t_node nn, gv).
  { entailer!. simpl. rewrite Z.max_r by lia. do 3 f_equal. lia. }
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros q.
  forward. forward.
  forward_if.
  { apply derives_trans with ((if eq_dec q nullval then emp else
      malloc_token Ews (tarray t_node nn) q * data_at_ Ews (tarray t_node nn) q) * TT)%logic;
      [ cancel | apply malloc_test_null; simpl; rep_lia ]. }
  { forward. Exists 20 p6 (@nil Z) bl1 zero_fn.
    match goal with |- context [data_at Ews t_fn ?V _] => Exists V end.
    Exists nn. rewrite app_nil_r.
    rewrite if_false by lia. unfold fn_nodes; cbn [fst snd]. rewrite blk_null.
    entailer!. unfold u32_ok; auto. }
  rewrite if_false by auto. Intros.
  forward. forward.
  forward.
  rewrite data_at__tarray.
  assert_PROP (field_compatible (tarray t_node nn) [] q) as FCq by entailer!.
  forward_loop (EX jj: Z, EX pj: Z, EX xs: list Z, EX bl2: list Z, EX nds: list node,
    PROP (0 <= jj <= nn; Zlength nds = jj; 0 <= pj <= Zlength bs; Zlength al + Zlength xs <= acap; u32_ok xs;
          Zlength bl1 <= Zlength bl2 <= bcap; bytes_ok bl2;
          forall j', 0 <= j' < jj -> node_ok nfns ns (al ++ xs) (Zlength bl2) j' (Znth j' nds))
    LOCAL (temp _j (Vint (Int.repr jj)); temp _fn fnp; lvar _root tuint v_root; lvar _nnodes tuint v_nnodes;
           lvar _namelen tuint v_namelen; lvar _dec tuint v_dec; lvar _nslots tuint v_nslots;
           lvar _arity tuint v_arity; gvars gv; temp _r r; temp _p p; temp _f (Vint (Int.repr f)))
    SEP (mem_mgr gv; malloc_token Ews (tarray t_node nn) q;
         narr nn (map node_val nds ++ Zrepeat (default_val t_node) (nn - jj)) q;
         data_at Tsh t_ld (LD buf (Zlength bs) pj acap bcap) r; buf_rep shb bs buf;
         data_at Tsh tuint (Vint (Int.repr nn)) v_nnodes;
         data_at Ews t_fn (Vint (Int.repr ar), (Vint (Int.repr ns), (Vint (Int.repr dc),
           (Vint (Int.repr (Zlength bl)), (Vint (Int.repr nl), (Vint (Int.repr nn), (z, q))))))) fnp;
         data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl2)) p;
         bytes_pool bytes bcap bl2;
         data_at Tsh tuint (Vint (Int.repr nl)) v_namelen; data_at Tsh tuint (Vint (Int.repr dc)) v_dec;
         data_at Tsh tuint (Vint (Int.repr ns)) v_nslots; data_at Tsh tuint (Vint (Int.repr ar)) v_arity;
         data_at_ Tsh tuint v_root; args_pool args acap (al ++ xs)))%assert
  continue: (EX jj: Z, EX pj: Z, EX xs: list Z, EX bl2: list Z, EX nds: list node,
    PROP (0 <= jj < nn; Zlength nds = (jj + 1)%Z; 0 <= pj <= Zlength bs; Zlength al + Zlength xs <= acap; u32_ok xs;
          Zlength bl1 <= Zlength bl2 <= bcap; bytes_ok bl2;
          forall j', (0 <= j' < jj + 1)%Z -> node_ok nfns ns (al ++ xs) (Zlength bl2) j' (Znth j' nds))
    LOCAL (temp _j (Vint (Int.repr jj)); temp _fn fnp; lvar _root tuint v_root; lvar _nnodes tuint v_nnodes;
           lvar _namelen tuint v_namelen; lvar _dec tuint v_dec; lvar _nslots tuint v_nslots;
           lvar _arity tuint v_arity; gvars gv; temp _r r; temp _p p; temp _f (Vint (Int.repr f)))
    SEP (mem_mgr gv; malloc_token Ews (tarray t_node nn) q;
         narr nn (map node_val nds ++ Zrepeat (default_val t_node) (nn - (jj + 1))%Z) q;
         data_at Tsh t_ld (LD buf (Zlength bs) pj acap bcap) r; buf_rep shb bs buf;
         data_at Tsh tuint (Vint (Int.repr nn)) v_nnodes;
         data_at Ews t_fn (Vint (Int.repr ar), (Vint (Int.repr ns), (Vint (Int.repr dc),
           (Vint (Int.repr (Zlength bl)), (Vint (Int.repr nl), (Vint (Int.repr nn), (z, q))))))) fnp;
         data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl2)) p;
         bytes_pool bytes bcap bl2;
         data_at Tsh tuint (Vint (Int.repr nl)) v_namelen; data_at Tsh tuint (Vint (Int.repr dc)) v_dec;
         data_at Tsh tuint (Vint (Int.repr ns)) v_nslots; data_at Tsh tuint (Vint (Int.repr ar)) v_arity;
         data_at_ Tsh tuint v_root; args_pool args acap (al ++ xs)))%assert
  break: (EX pj: Z, EX xs: list Z, EX bl2: list Z, EX nds: list node,
    PROP (Zlength nds = nn; 0 <= pj <= Zlength bs; Zlength al + Zlength xs <= acap; u32_ok xs;
          Zlength bl1 <= Zlength bl2 <= bcap; bytes_ok bl2;
          forall j', 0 <= j' < nn -> node_ok nfns ns (al ++ xs) (Zlength bl2) j' (Znth j' nds))
    LOCAL (temp _fn fnp; lvar _root tuint v_root; lvar _nnodes tuint v_nnodes;
           lvar _namelen tuint v_namelen; lvar _dec tuint v_dec; lvar _nslots tuint v_nslots;
           lvar _arity tuint v_arity; gvars gv; temp _r r; temp _p p; temp _f (Vint (Int.repr f)))
    SEP (mem_mgr gv; malloc_token Ews (tarray t_node nn) q;
         narr nn (map node_val nds) q;
         data_at Tsh t_ld (LD buf (Zlength bs) pj acap bcap) r; buf_rep shb bs buf;
         data_at Tsh tuint (Vint (Int.repr nn)) v_nnodes;
         data_at Ews t_fn (Vint (Int.repr ar), (Vint (Int.repr ns), (Vint (Int.repr dc),
           (Vint (Int.repr (Zlength bl)), (Vint (Int.repr nl), (Vint (Int.repr nn), (z, q))))))) fnp;
         data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl2)) p;
         bytes_pool bytes bcap bl2;
         data_at Tsh tuint (Vint (Int.repr nl)) v_namelen; data_at Tsh tuint (Vint (Int.repr dc)) v_dec;
         data_at Tsh tuint (Vint (Int.repr ns)) v_nslots; data_at Tsh tuint (Vint (Int.repr ar)) v_arity;
         data_at_ Tsh tuint v_root; args_pool args acap (al ++ xs)))%assert.
  - (* entry *)
    Exists 0 p6 (@nil Z) bl1 (@nil node). rewrite app_nil_r.
    replace (map node_val [] ++ Zrepeat (default_val t_node) (nn - 0)) with (Zrepeat (default_val t_node) nn)
      by (simpl; f_equal; lia).
    rewrite narr_fold. entailer!.
    all: first [ (unfold u32_ok; constructor) | (intros; lia) | (split; [ unfold u32_ok; constructor | intros; lia ]) ].
  - (* body *)
    Intros jj pj xs bl2 nds.
    forward.
    forward_if.
    2: { (* exit *) forward. assert (E: jj = nn) by lia. rewrite E in *.
         rewrite Z.sub_diag, Zrepeat_0, app_nil_r. Exists pj xs bl2 nds. entailer!. }
    forward. forward.
    unfold narr.
    sep_apply (SingletonHole.array_with_hole_intro Ews t_node jj nn
                 (map node_val nds ++ Zrepeat (default_val t_node) (nn - jj)) q ltac:(lia)).
    rewrite Znth_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map.
    replace (jj - Zlength nds) with 0 by lia.
    rewrite Znth_Zrepeat by lia. rewrite <- data_at__eq.
    assert (HPRE: node_pre_props shb bs pj acap bcap nfns entry (al ++ xs) bl2 ns jj).
    { unfold node_pre_props. rewrite Zlength_app. repeat split; auto; lia. }
    forward_call (r, buf, shb, bs, pj, acap, bcap, p, nfns, entry, fns, args, al ++ xs, bytes, bl2, ns, jj,
                  field_address (tarray t_node nn) [ArraySubsc jj] q).
    { entailer!; rewrite add_ptr_uint_field by (auto; rep_lia); auto. }
    Intros vret. destruct vret as [[[[[rc pj'] xs'] bl3] x] v]. cbn [fst snd] in *.
    assert (EJ: Zlength nds = jj) by lia. rewrite EJ.
    sep_apply (SingletonHole.array_with_hole_elim Ews t_node jj nn v
                 (map node_val nds ++ Zrepeat (default_val t_node) (nn - jj)) q).
    rewrite narr_fold.
    match goal with H: node_post_props _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7) end.
    forward.
    forward_if.
    { assert (P1: Zlength al + Zlength (xs ++ xs') <= acap) by (rewrite !Zlength_app in *; lia).
      assert (P2: u32_ok (xs ++ xs')).
      { apply Forall_app; split; auto. apply (u32_of_lt xs' jj); auto; rep_lia. }
      assert (P3: Zlength bl <= Zlength bl3 <= bcap) by lia.
      rewrite <- app_assoc. fn_errq rc pj' (xs ++ xs') bl3 nn q. }
    destruct (Q7 ltac:(lia)) as [-> Hx]. subst rc.
    try forward.
    Exists jj pj' (xs ++ xs') bl3 (nds ++ [x]).
    replace (upd_Znth jj (map node_val nds ++ Zrepeat (default_val t_node) (nn - jj)) (node_val x))
      with (map node_val (nds ++ [x]) ++ Zrepeat (default_val t_node) (nn - (jj + 1))).
    2: { rewrite <- EJ. rewrite upd_fill_map by lia. f_equal. f_equal.
         rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    rewrite app_assoc.
    entailer!.
    repeat match goal with |- _ /\ _ => split end.
    all: try (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil in *; rep_lia).
    all: try (apply Forall_app; split; auto; eapply u32_of_lt; [ | eassumption ]; rep_lia).
    all: try (
      let j1 := fresh "j1" in let Hj1 := fresh "Hj1" in
      intros j1 Hj1;
      destruct (zlt j1 (Zlength nds)) as [Hlt | Hge];
      [ rewrite Znth_app1 by lia; apply node_ok_mono with (Zlength bl2);
        [ match goal with H: forall _, _ -> node_ok _ _ _ _ _ (Znth _ _) |- _ => apply H; lia end | lia ]
      | assert (Ej: j1 = Zlength nds) by lia; subst j1;
        rewrite Znth_app2 by lia; rewrite Z.sub_diag, Znth_0_cons;
        match goal with H: node_ok _ _ _ _ _ _ |- _ =>
          first [ exact H | (rewrite <- EJ in H; exact H) | (rewrite EJ; exact H) ] end ]).
    all: auto.
  - (* increment *)
    Intros jj pj xs bl2 nds. forward. Exists (jj + 1) pj xs bl2 nds. entailer!.
  - (* after the loop *)
    Intros pj xs bl2 nds. try subst nn.
    forward_call (r, buf, shb, bs, pj, acap, bcap, v_root, Tsh).
    Intros vret. destruct vret as [[[rc7 p7] rt] vr]. cbn [fst snd] in *.
    forward_if.
    { fn_errq 1 p7 xs bl2 (Zlength nds) q. }
    match goal with H: rc7 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [-> Hrt]; clear H end.
    forward. forward. forward_if.
    { fn_errq 8 p7 xs bl2 (Zlength nds) q. }
    forward. forward.
    forward.
    Exists 0 p7 xs bl2 (mkF ar ns dc (Zlength bl) nl rt q nds).
    match goal with |- context [data_at Ews t_fn ?V _] => Exists V end. Exists (Zlength nds).
    destruct (Z.eq_dec 0 0) as [_ | NE]; [ | congruence ].
    unfold nodes_rep; cbn [f_q f_body]. rewrite if_false by auto.
    unfold narr.
    assert_PROP (isptr q) as Pq by entailer!.
    entailer!.
    split.
    { unfold fn_val; cbn [f_arity f_nslots f_dec f_off f_len f_root f_q f_body]. reflexivity. }
    unfold fn_ok; cbn [f_arity f_nslots f_dec f_off f_len f_root f_q f_body].
    repeat match goal with |- _ /\ _ => split end.
    all: try rep_lia.
    all: auto.
Qed.
