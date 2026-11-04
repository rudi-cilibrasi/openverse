(* Bodies of vx_store_init, vx_store_get, vx_store_mark, vx_store_commit, vx_store_out_len. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.store.code.
Require Import OpenverseStore.proof.StoreSpecs OpenverseStore.proof.Tac.

Lemma body_vx_store_init: semax_body Vprog Gprog f_vx_store_init vx_store_init_spec.
Proof.
  start_function.
  do 9 forward.
  unfold store_rep, out_rep. Exists jc oc.
  entailer!. list_solve.
Qed.

Lemma body_vx_store_out_len: semax_body Vprog Gprog f_vx_store_out_len vx_store_out_len_spec.
Proof.
  start_function.
  unfold store_rep. Intros jc. unfold sval.
  forward. forward.
  unfold store_rep. Exists jc. entailer!.
Qed.

Lemma body_vx_store_mark: semax_body Vprog Gprog f_vx_store_mark vx_store_mark_spec.
Proof.
  start_function.
  unfold store_rep. Intros jc. unfold sval.
  do 8 forward.
  unfold store_rep. Exists jc. unfold sval, mval. entailer!.
Qed.

Lemma body_vx_store_commit: semax_body Vprog Gprog f_vx_store_commit vx_store_commit_spec.
Proof.
  start_function.
  unfold store_rep. Intros jc. unfold sval, mval.
  forward. forward. forward.
  forward_if.
  - z64. subst md. forward. unfold store_rep. Exists jc. rewrite Z.eqb_refl. entailer!.
    list_solve.
  - z64. forward. fix_sf.
    rewrite (proj2 (Z.eqb_neq md 0)) by auto.
    unfold store_rep. Exists jc. entailer!.
Qed.

Lemma body_vx_store_get: semax_body Vprog Gprog f_vx_store_get vx_store_get_spec.
Proof.
  start_function.
  unfold store_rep. Intros jc. unfold sval.
  forward.
  forward_if.
  - z64. forward.
    rewrite (proj2 (Z.ltb_ge slot (Zlength vs))) by lia.
    unfold store_rep. Exists jc. entailer!.
  - z64.
    rewrite (buf_nonnull t_val) by lia.
    forward.
    forward.
    { entailer!. rewrite Znth_map by lia. unfold vval. simpl. auto. }
    forward.
    forward.
    forward.
    { entailer!. rewrite Znth_map by lia. unfold vval. simpl. auto. }
    forward.
    forward.
    rewrite (proj2 (Z.ltb_lt slot (Zlength vs))) by lia.
    unfold store_rep. rewrite (buf_nonnull t_val) by lia. Exists jc.
    entailer!.
    rewrite Znth_map by lia. unfold vval. simpl. cancel.
Qed.
