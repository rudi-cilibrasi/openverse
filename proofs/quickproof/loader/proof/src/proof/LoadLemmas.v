(* Lemmas about the program states: building freeable and prog_rep. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
#[local] Existing Instance Specs.CS.
Local Open Scope logic.

Definition fentry (x: fnr) : reptype t_fn * Z := (fn_val x, Zlength (f_body x)).

Lemma nodes_rep_fblk: forall x, nodes_rep x |-- fblk (fentry x).
Proof.
  intros. unfold nodes_rep, fblk, fentry, fn_nodes, fn_val. cbn [fst snd].
  destruct (eq_dec (f_q x) nullval).
  - rewrite e, blk_null. auto.
  - unfold blk. rewrite if_false by auto.
    sep_apply (data_at_data_at_ Ews (tarray t_node (Zlength (f_body x))) (map node_val (f_body x)) (f_q x)).
    cancel.
Qed.

Lemma iter_nodes_fblk: forall F, iter_sepcon nodes_rep F |-- iter_sepcon fblk (map fentry F).
Proof.
  induction F; simpl; auto. apply sepcon_derives; auto. apply nodes_rep_fblk.
Qed.

Lemma iter_fblk_zero: forall n, iter_sepcon fblk (Zrepeat (fentry zero_fn) n) = emp.
Proof.
  intros. unfold Zrepeat. induction (Z.to_nat n); simpl; auto.
  rewrite IHn0. unfold fblk, fentry, fn_nodes, fn_val. cbn [fst snd f_q]. rewrite blk_null.
  apply emp_sepcon.
Qed.

Lemma freeable_intro: forall p nfns ve fns args vna bytes vnb L ta tb,
  0 <= nfns <= Int.max_unsigned -> Zlength L = nfns -> isptr fns ->
  data_at Tsh t_prog (Vint (Int.repr nfns), (ve, (fns, (args, (vna, (bytes, vnb)))))) p *
  malloc_token Ews (tarray t_fn nfns) fns * data_at Ews (tarray t_fn nfns) (map fst L) fns *
  iter_sepcon fblk L * blk (tarray tuint ta) args * blk (tarray tuchar tb) bytes
  |-- freeable p.
Proof.
  intros. unfold freeable.
  Exists nfns ve fns args vna bytes vnb L ta tb.
  unfold fns_free. rewrite if_false by (intro E; subst; contradiction).
  entailer!.
Qed.

Lemma freeable_nofns: forall p ve args vna bytes vnb ta tb,
  data_at Tsh t_prog (Vint (Int.repr 0), (ve, (nullval, (args, (vna, (bytes, vnb)))))) p *
  blk (tarray tuint ta) args * blk (tarray tuchar tb) bytes
  |-- freeable p.
Proof.
  intros. unfold freeable.
  Exists 0 ve nullval args vna bytes vnb (@nil (reptype t_fn * Z)) ta tb.
  unfold fns_free. rewrite if_true by auto.
  entailer!.
Qed.

Lemma freeable_PRG0: forall p, data_at Tsh t_prog PRG0 p |-- freeable p.
Proof.
  intros. eapply derives_trans; [ | apply (freeable_nofns p (Vint (Int.repr 0)) nullval (Vint (Int.repr 0))
                                             nullval (Vint (Int.repr 0)) 0 0) ].
  rewrite !blk_null. cancel.
Qed.

Lemma args_pool_blk: forall args acap al, args_pool args acap al |-- blk (tarray tuint acap) args.
Proof. intros. unfold args_pool. apply blk_of_data_at. Qed.

Lemma bytes_pool_blk: forall bytes bcap bl, bytes_pool bytes bcap bl |-- blk (tarray tuchar bcap) bytes.
Proof. intros. unfold bytes_pool. apply blk_of_data_at. Qed.

Lemma args_final_blk: forall args al, args_final args al |-- blk (tarray tuint (Zlength al)) args.
Proof.
  intros. unfold args_final. destruct (Z.eq_dec (Zlength al) 0).
  - Intros. subst. rewrite blk_null. auto.
  - apply blk_of_data_at.
Qed.

Lemma bytes_final_blk: forall bytes bl, bytes_final bytes bl |-- blk (tarray tuchar (Zlength bl)) bytes.
Proof.
  intros. unfold bytes_final. destruct (Z.eq_dec (Zlength bl) 0).
  - Intros. subst. rewrite blk_null. auto.
  - apply blk_of_data_at.
Qed.

Lemma fn_ok_mono: forall nfns al ext nb nb' x,
  fn_ok nfns al nb x -> nb <= nb' -> fn_ok nfns (al ++ ext) nb' x.
Proof.
  intros nfns al ext nb nb' x (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) H.
  unfold fn_ok. repeat (split; [ auto; lia | ]).
  intros j Hj. apply node_ok_mono with nb; auto.
Qed.

Lemma prog_rep_freeable: forall p, prog_rep p |-- freeable p.
Proof.
  intros. unfold prog_rep. Intros nfns entry fns args bytes al bl F.
  destruct H as (HF & Hn & He & Hnb & Hal & Hu & Hok & Hc).
  unfold fns_rep. subst nfns.
  assert_PROP (isptr fns) as Pf by entailer!.
  sep_apply (iter_nodes_fblk F). sep_apply (args_final_blk args al). sep_apply (bytes_final_blk bytes bl).
  replace (map fn_val F) with (map fst (map fentry F)) by (rewrite map_map; reflexivity).
  eapply derives_trans; [ | apply (freeable_intro p (Zlength F) (Vint (Int.repr entry)) fns args
       (Vint (Int.repr (Zlength al))) bytes (Vint (Int.repr (Zlength bl))) (map fentry F)
       (Zlength al) (Zlength bl)) ].
  - cancel.
  - rep_lia.
  - rewrite Zlength_map. auto.
  - auto.
Qed.

Lemma blk_fold: forall t q, malloc_token Ews t q * data_at_ Ews t q |-- blk t q.
Proof. intros. rewrite data_at__eq. apply blk_of_data_at. Qed.

Lemma i64_divu_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.divu (Int64.repr a) (Int64.repr b) = Int64.repr (a / b).
Proof. intros. unfold Int64.divu. rewrite !Int64.unsigned_repr by auto. auto. Qed.

(* The function table, kept folded so that the entailment tactics do not unfold it. *)
Definition farr (n: Z) (L: list (reptype t_fn)) (fns: val) : mpred := data_at Ews (tarray t_fn n) L fns.
Lemma farr_fold: forall n L fns, data_at Ews (tarray t_fn n) L fns = farr n L fns.
Proof. reflexivity. Qed.

Lemma farr_local_facts: forall n L fns, farr n L fns |-- !! (field_compatible (tarray t_fn n) [] fns).
Proof. intros. unfold farr. entailer!. Qed.
#[export] Hint Resolve farr_local_facts : saturate_local.

Lemma freeable_loaded: forall p nfns entry fns args na bytes nb Fd ta tb,
  0 <= nfns <= Int.max_unsigned -> Zlength Fd = nfns ->
  data_at Tsh t_prog (PRG nfns entry fns args na bytes nb) p * malloc_token Ews (tarray t_fn nfns) fns *
  farr nfns (map fn_val Fd) fns * iter_sepcon nodes_rep Fd *
  blk (tarray tuint ta) args * blk (tarray tuchar tb) bytes |-- freeable p.
Proof.
  intros. assert_PROP (isptr fns) as Pf by (unfold farr; entailer!).
  sep_apply (iter_nodes_fblk Fd).
  replace (map fn_val Fd) with (map fst (map fentry Fd)) by (rewrite map_map; reflexivity).
  unfold farr.
  eapply derives_trans; [ | apply (freeable_intro p nfns (Vint (Int.repr entry)) fns args
       (Vint (Int.repr na)) bytes (Vint (Int.repr nb)) (map fentry Fd) ta tb) ]; auto.
  - cancel.
  - rewrite Zlength_map; auto.
Qed.

Lemma map_fst_partial: forall Fd f nfns fv k, Zlength Fd = f -> 0 <= f < nfns ->
  map fst (map fentry Fd ++ [(fv, k)] ++ Zrepeat (fentry zero_fn) (nfns - f - 1)) =
  upd_Znth f (map fn_val Fd ++ Zrepeat (fn_val zero_fn) (nfns - f)) fv.
Proof.
  intros. rewrite !map_app, map_map.
  replace (map (fun x => fst (fentry x)) Fd) with (map fn_val Fd) by reflexivity.
  replace (map fst [(fv, k)]) with [fv] by reflexivity.
  replace (map fst (Zrepeat (fentry zero_fn) (nfns - f - 1))) with (Zrepeat (fn_val zero_fn) (nfns - f - 1))
    by (unfold Zrepeat; rewrite map_repeat; reflexivity).
  list_solve.
Qed.

Lemma freeable_partial: forall p nfns entry fns args na bytes nb Fd f fv k ta tb,
  0 <= f < nfns -> nfns <= Int.max_unsigned -> Zlength Fd = f ->
  data_at Tsh t_prog (PRG nfns entry fns args na bytes nb) p * malloc_token Ews (tarray t_fn nfns) fns *
  farr nfns (upd_Znth f (map fn_val Fd ++ Zrepeat (fn_val zero_fn) (nfns - f)) fv) fns *
  iter_sepcon nodes_rep Fd * blk (tarray t_node k) (fn_nodes fv) *
  blk (tarray tuint ta) args * blk (tarray tuchar tb) bytes |-- freeable p.
Proof.
  intros. assert_PROP (isptr fns) as Pf by (unfold farr; entailer!).
  sep_apply (iter_nodes_fblk Fd).
  set (L := map fentry Fd ++ [(fv, k)] ++ Zrepeat (fentry zero_fn) (nfns - f - 1)).
  rewrite <- (map_fst_partial Fd f nfns fv k) by auto. fold L.
  assert (EI: iter_sepcon fblk L = iter_sepcon fblk (map fentry Fd) * blk (tarray t_node k) (fn_nodes fv)).
  { unfold L. rewrite !iter_sepcon_app, iter_fblk_zero. simpl. unfold fblk at 2. cbn [fst snd].
    rewrite sepcon_emp, sepcon_emp. auto. }
  unfold farr.
  eapply derives_trans; [ | apply (freeable_intro p nfns (Vint (Int.repr entry)) fns args
       (Vint (Int.repr na)) bytes (Vint (Int.repr nb)) L ta tb) ]; auto; try lia.
  - rewrite EI. cancel.
  - unfold L. rewrite !Zlength_app, Zlength_map, Zlength_cons, Zlength_nil, Zlength_Zrepeat by lia. lia.
Qed.
