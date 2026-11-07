(* Lemmas and tactics for the node loaders. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
Require Import OpenverseLoader.proof.Fields.
#[local] Existing Instance Specs.CS.

Lemma npp_err: forall bs acap bcap nfns al bl nslots j rc pos' x v,
  1 <= rc <= 21 -> 0 <= pos' <= Zlength bs -> Zlength al <= acap -> Zlength bl <= bcap -> bytes_ok bl ->
  node_post_props bs acap bcap nfns al bl nslots j rc pos' [] bl x v.
Proof. intros. unfold node_post_props. rewrite Zlength_nil. repeat split; try lia; auto. Qed.

(* An error after the bytes pool grew (load_heap's isTag tags). *)
Lemma npp_err_bl: forall bs acap bcap nfns al bl bl' nslots j rc pos' x v,
  1 <= rc <= 21 -> 0 <= pos' <= Zlength bs -> Zlength al <= acap -> Zlength bl <= Zlength bl' <= bcap ->
  bytes_ok bl' -> node_post_props bs acap bcap nfns al bl nslots j rc pos' [] bl' x v.
Proof. intros. unfold node_post_props. rewrite Zlength_nil. repeat split; try lia; auto. Qed.

Lemma npp_ok: forall bs acap bcap nfns al bl nslots j rc pos' x v,
  0 <= rc <= 21 -> 0 <= pos' <= Zlength bs -> Zlength al <= acap -> Zlength bl <= bcap -> bytes_ok bl ->
  (rc = 0 -> v = node_val x /\ node_ok nfns nslots al (Zlength bl) j x) ->
  node_post_props bs acap bcap nfns al bl nslots j rc pos' [] bl x v.
Proof.
  intros. unfold node_post_props. rewrite Zlength_nil, app_nil_r.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [constructor|]. split; [lia|]. split; auto.
Qed.

Lemma args_ok_new: forall al xs j x,
  Zlength xs = n_b x -> n_c x = Zlength al -> Forall (fun y => 0 <= y < j) xs -> args_ok (al ++ xs) j x.
Proof.
  intros al xs j x H1 H2 H3. unfold args_ok. rewrite Zlength_app.
  pose proof (Zlength_nonneg al).
  split; [ lia | ]. split; [ lia | ].
  intros k Hk. rewrite H2, Znth_app2 by lia. replace (Zlength al + k - Zlength al) with k by lia.
  apply (proj1 (Forall_Znth _ _) H3 k). lia.
Qed.

Ltac node_ok_tac :=
  unfold node_ok, node_wf; cbn [n_tag n_op n_a n_b n_c n_d n_lit];
  repeat match goal with
  | |- _ /\ _ => split
  | |- _ -> _ => intro; try (exfalso; lia)
  | |- args_ok _ _ _ => apply args_ok_new; cbn [n_tag n_op n_a n_b n_c n_d n_lit]; auto
  end; try lia; try rep_lia.

Ltac pre_props :=
  match goal with H: node_pre_props _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (SH & Hbs & Hpos & Hlen & Hacap & Hbcap & Hal & Hbl & Hblok & Hnfns & Hentry & Hns & Hj) end.

Ltac ex_node nd := match goal with |- context [data_at Ews t_node ?V nd] => Exists V end.

Ltac use_rc0 :=
  match goal with
  | E: ?rc = 0, H: ?rc = 0 -> _ |- _ => subst rc; use_rc0
  | H: 0 = 0 -> ?v = _ /\ _ |- _ =>
      let Hx := fresh "Hx" in destruct (H eq_refl) as [-> Hx]; clear H
  end.


Lemma npre_pos: forall shb bs pos acap bcap nfns entry al bl nslots j pos',
  node_pre_props shb bs pos acap bcap nfns entry al bl nslots j -> 0 <= pos' <= Zlength bs ->
  node_pre_props shb bs pos' acap bcap nfns entry al bl nslots j.
Proof. unfold node_pre_props. intros. tauto. Qed.
