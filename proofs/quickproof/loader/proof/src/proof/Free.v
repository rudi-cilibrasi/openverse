(* Bodies of prog_clear and vx_free_program. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
#[local] Existing Instance Specs.CS.


Lemma Znth_any: forall {A} (d d': Inhabitant A) i (l: list A), 0 <= i < Zlength l ->
  @Znth A d i l = @Znth A d' i l.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0); [ lia | ]. apply nth_indep.
  rewrite <- ZtoNat_Zlength. lia.
Qed.

Ltac absurd_branch :=
  exfalso; first [ discriminate | contradiction
                 | match goal with H: ?a <> ?a |- _ => apply H; reflexivity end | auto ].

Ltac gen_znth E name :=
  match type of E with @Znth ?A ?dz ?i ?l = ?R =>
    assert (name: forall d: Inhabitant A, @Znth A d i l = R)
      by (intros d; rewrite (Znth_any d dz i l) by (rewrite ?Zlength_map; lia); exact E)
  end.

Lemma blk_nonnull: forall t q, q <> nullval -> blk t q = (malloc_token Ews t q * data_at_ Ews t q)%logic.
Proof. intros. unfold blk. rewrite if_false by auto. auto. Qed.

Lemma body_prog_clear: semax_body Vprog Gprog f_prog_clear prog_clear_spec.
Proof.
  start_function.
  repeat forward.
  entailer!.
Qed.

Lemma blk_test_null: forall t q P, (blk t q * P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)))%logic.
Proof. intros. unfold blk. apply malloc_test_null. pose proof (sizeof_pos t). lia. Qed.

Lemma fns_free_test: forall fns nfns L P,
  (fns_free fns nfns L * P |-- denote_tc_test_eq fns (Vlong (Int64.repr 0)))%logic.
Proof.
  intros. unfold fns_free. destruct (eq_dec fns nullval).
  - subst. simpl. entailer!.
  - Intros. sep_apply (data_at_data_at_ Ews (tarray t_fn nfns) (map fst L) fns).
    eapply derives_trans;
      [ | apply (malloc_test_null (tarray t_fn nfns) fns (iter_sepcon fblk L * P)%logic) ].
    + rewrite if_false by auto. cancel.
    + pose proof (sizeof_pos (tarray t_fn nfns)). lia.
Qed.

Lemma body_vx_free_program: semax_body Vprog Gprog f_vx_free_program vx_free_program_spec.
Proof.
  start_function.
  unfold freeable. Intros nfns ve fns args vna bytes vnb L ka kb.
  forward.
  forward_if (PROP () LOCAL (temp _p p; gvars gv)
     SEP (data_at Tsh t_prog (Vint (Int.repr nfns), (ve, (fns, (args, (vna, (bytes, vnb)))))) p;
          blk (tarray tuint ka) args; blk (tarray tuchar kb) bytes; mem_mgr gv))%assert.
  - apply derives_trans with (fns_free fns nfns L * TT)%logic; [ cancel | apply fns_free_test ].
  - unfold fns_free. rewrite if_false by auto. Intros.
    forward.
    forward_loop (EX i: Z,
      PROP (0 <= i <= nfns)
      LOCAL (temp _i (Vint (Int.repr i)); temp _p p; gvars gv)
      SEP (data_at Tsh t_prog (Vint (Int.repr nfns), (ve, (fns, (args, (vna, (bytes, vnb)))))) p;
           malloc_token Ews (tarray t_fn nfns) fns; data_at Ews (tarray t_fn nfns) (map fst L) fns;
           iter_sepcon fblk (sublist i nfns L);
           blk (tarray tuint ka) args; blk (tarray tuchar kb) bytes; mem_mgr gv))%assert
    continue: (EX i: Z,
      PROP (0 <= i < nfns)
      LOCAL (temp _i (Vint (Int.repr i)); temp _p p; gvars gv)
      SEP (data_at Tsh t_prog (Vint (Int.repr nfns), (ve, (fns, (args, (vna, (bytes, vnb)))))) p;
           malloc_token Ews (tarray t_fn nfns) fns; data_at Ews (tarray t_fn nfns) (map fst L) fns;
           iter_sepcon fblk (sublist (i + 1) nfns L);
           blk (tarray tuint ka) args; blk (tarray tuchar kb) bytes; mem_mgr gv))%assert
    break: (PROP ()
      LOCAL (temp _p p; gvars gv)
      SEP (data_at Tsh t_prog (Vint (Int.repr nfns), (ve, (fns, (args, (vna, (bytes, vnb)))))) p;
           malloc_token Ews (tarray t_fn nfns) fns; data_at Ews (tarray t_fn nfns) (map fst L) fns;
           blk (tarray tuint ka) args; blk (tarray tuchar kb) bytes; mem_mgr gv))%assert.
    + Exists 0. entailer!. rewrite sublist_same by lia. auto.
    + Intros i. forward. forward_if.
      * rewrite (sublist_split i (i + 1) nfns) by lia. rewrite iter_sepcon_app.
        rewrite sublist_len_1 by lia. simpl iter_sepcon. Intros.
        assert (EZ: Znth i (map fst L) = fst (Znth i L)) by (rewrite Znth_map by lia; reflexivity).
        destruct (Znth i L) as [fv k] eqn:EL. cbn [fst] in EZ.
        destruct fv as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & qn).
        gen_znth EZ EZa. gen_znth EL ELa.
        unfold fblk at 1. unfold fn_nodes. cbn [fst snd].
        destruct (eq_dec qn nullval) as [Eq | Nq].
        -- subst qn. rewrite blk_null. Intros.
           forward. forward.
           { entailer!. try rewrite EZa; try (rewrite Znth_map by lia; rewrite ELa); simpl; auto. }
           try rewrite EZa; try (rewrite Znth_map by lia; rewrite ELa); cbn [fst snd].
           forward_if.
           { absurd_branch. }
           forward. Exists i. entailer!.
        -- unfold blk at 1. rewrite if_false by auto. Intros.
           forward. forward.
           { entailer!. try rewrite EZa; try (rewrite Znth_map by lia; rewrite ELa); simpl; auto. }
           try rewrite EZa; try (rewrite Znth_map by lia; rewrite ELa); cbn [fst snd].
           forward_if.
           2: { absurd_branch. }
           forward. forward.
           { entailer!. try rewrite EZa; try (rewrite Znth_map by lia; rewrite ELa); simpl; auto. }
           try rewrite EZa; try (rewrite Znth_map by lia; rewrite ELa); cbn [fst snd].
           forward_call (tarray t_node k, qn, gv).
           { rewrite if_false by auto. cancel. }
           try forward.
           Exists i. entailer!.
      * forward. entailer!. rewrite sublist_nil_gen by lia. simpl. auto.
    + Intros i. forward. Exists (i + 1). entailer!.
    + forward.
      sep_apply (data_at_data_at_ Ews (tarray t_fn nfns) (map fst L) fns).
      forward_call (tarray t_fn nfns, fns, gv).
      { rewrite if_false by auto. cancel. }
      entailer!.
  - forward. unfold fns_free. rewrite if_true by auto. entailer!.
  - forward.
    forward_if (PROP () LOCAL (temp _p p; gvars gv)
      SEP (data_at Tsh t_prog (Vint (Int.repr nfns), (ve, (fns, (args, (vna, (bytes, vnb)))))) p;
           blk (tarray tuchar kb) bytes; mem_mgr gv))%assert.
    + apply derives_trans with (blk (tarray tuint ka) args * TT)%logic; [ cancel | apply blk_test_null ].
    + rewrite (blk_nonnull (tarray tuint ka) args) by auto. Intros.
      forward. forward_call (tarray tuint ka, args, gv).
      { rewrite if_false by auto. cancel. }
      entailer!.
    + forward. unfold blk at 1. rewrite if_true by auto. entailer!.
    + forward.
      forward_if (PROP () LOCAL (temp _p p; gvars gv)
        SEP (data_at Tsh t_prog (Vint (Int.repr nfns), (ve, (fns, (args, (vna, (bytes, vnb)))))) p;
             mem_mgr gv))%assert.
      * apply derives_trans with (blk (tarray tuchar kb) bytes * TT)%logic; [ cancel | apply blk_test_null ].
      * rewrite (blk_nonnull (tarray tuchar kb) bytes) by auto. Intros.
        forward. forward_call (tarray tuchar kb, bytes, gv).
        { rewrite if_false by auto. cancel. }
        entailer!.
      * forward. unfold blk. rewrite if_true by auto. entailer!.
      * sep_apply (data_at_data_at_ Tsh t_prog (Vint (Int.repr nfns), (ve, (fns, (args, (vna, (bytes, vnb)))))) p).
        forward_call (p).
        entailer!.
Qed.
