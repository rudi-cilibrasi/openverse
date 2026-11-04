(* Lemmas and tactics shared by the body proofs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
#[local] Existing Instance Specs.CS.

Lemma i64_sub_repr a b: Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  unfold Int64.sub. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.
Lemma i64_add_repr a b: Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.
Lemma int_add_repr a b: Int.add (Int.repr a) (Int.repr b) = Int.repr (a + b).
Proof.
  unfold Int.add. apply Int.eqm_samerepr. apply Int.eqm_add; apply Int.eqm_sym, Int.eqm_unsigned_repr.
Qed.

Lemma Znth_vints: forall l i, 0 <= i < Zlength l -> Znth i (vints l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold vints. rewrite Znth_map by lia. reflexivity. Qed.

Lemma bytes_ok_Znth: forall l i, bytes_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l <= Byte.max_unsigned.
Proof. intros. apply (proj1 (Forall_Znth _ _) H); auto. Qed.

Lemma Zlength_vints: forall l, Zlength (vints l) = Zlength l.
Proof. intros. unfold vints. apply Zlength_map. Qed.

Lemma rc_zero: forall rc, 0 <= rc <= 20 -> Int.repr rc = Int.repr 0 -> rc = 0.
Proof. intros. apply repr_inj_unsigned in H0; rep_lia. Qed.

Lemma buf_rep_nonnull: forall sh bs buf, buf <> nullval ->
  buf_rep sh bs buf = data_at sh (tarray tuchar (Zlength bs)) (vints bs) buf.
Proof. intros. unfold buf_rep. rewrite if_false by auto. auto. Qed.

Lemma i64_not_repr: forall u, Int64.not u = Int64.repr (Int64.max_unsigned - Int64.unsigned u).
Proof.
  intros. rewrite Int64.not_neg. unfold Int64.add, Int64.neg.
  apply Int64.eqm_samerepr. rewrite Int64.unsigned_mone.
  eapply Int64.eqm_trans.
  - apply Int64.eqm_add; [ apply Int64.eqm_sym, Int64.eqm_unsigned_repr | apply Int64.eqm_refl ].
  - apply Int64.eqm_refl2. unfold Int64.max_unsigned. lia.
Qed.

Lemma i64_neg_not_range: forall u, Int64.max_signed < Int64.unsigned u ->
  0 <= Int64.signed (Int64.not u) <= Int64.max_signed /\
  Int64.signed (Int64.neg (Int64.not u)) = (- Int64.signed (Int64.not u))%Z.
Proof.
  intros u Hu. pose proof (Int64.unsigned_range_2 u) as R.
  rewrite i64_not_repr.
  assert (E: Int64.signed (Int64.repr (Int64.max_unsigned - Int64.unsigned u)) = Int64.max_unsigned - Int64.unsigned u).
  { apply Int64.signed_repr. rep_lia. }
  rewrite E. split; [ rep_lia | ].
  rewrite Int64.neg_repr. apply Int64.signed_repr. rep_lia.
Qed.

Ltac buf_nonnull :=
  match goal with |- context [buf_rep ?sh ?bs ?buf] =>
    let En := fresh "En" in let Nn := fresh "Nn" in
    destruct (eq_dec buf nullval) as [En|Nn];
    [ unfold buf_rep; rewrite if_true by auto; Intros; subst bs; rewrite ?Zlength_nil in *; exfalso; lia
    | rewrite (buf_rep_nonnull sh bs buf) by auto ] end.

Ltac i64s := rewrite ?i64_sub_repr, ?i64_add_repr in *; rewrite ?Int64.unsigned_repr in * by rep_lia.

Ltac simpl_ints :=
  rewrite ?i64_sub_repr, ?i64_add_repr, ?int_add_repr in *;
  rewrite ?Int64.unsigned_repr in * by rep_lia; rewrite ?Int.unsigned_repr in * by rep_lia.

Lemma shl_1_24: Int.shl (Int.repr 1) (Int.repr 24) = Int.repr 16777216.
Proof. reflexivity. Qed.
Lemma shl_1_16: Int.shl (Int.repr 1) (Int.repr 16) = Int.repr 65536.
Proof. reflexivity. Qed.
Lemma shl_1_22: Int.shl (Int.repr 1) (Int.repr 22) = Int.repr 4194304.
Proof. reflexivity. Qed.

Lemma upd_fill: forall (l: list Z) (x: Z) cap, Zlength l < cap ->
  upd_Znth (Zlength l) (vints l ++ Zrepeat Vundef (cap - Zlength l)) (Vint (Int.repr x)) =
  vints (l ++ [x]) ++ Zrepeat Vundef (cap - Zlength (l ++ [x])).
Proof. intros. unfold vints. list_solve. Qed.

Lemma bytes_ok_app: forall a b, bytes_ok a -> bytes_ok b -> bytes_ok (a ++ b).
Proof. intros. apply Forall_app; auto. Qed.

Lemma bytes_ok_sublist: forall l lo hi, bytes_ok l -> bytes_ok (sublist lo hi l).
Proof. intros. apply Forall_sublist; auto. Qed.


Lemma upd_fill_map {A B: Type} {dA: Inhabitant A} {dB: Inhabitant B}:
  forall (f: A -> B) (l: list A) (x: A) (u: B) n, Zlength l < n ->
  upd_Znth (Zlength l) (map f l ++ Zrepeat u (n - Zlength l)) (f x) =
  map f (l ++ [x]) ++ Zrepeat u (n - Zlength (l ++ [x])).
Proof. intros. list_solve. Qed.

Lemma args_ok_mono: forall al ext j x, args_ok al j x -> args_ok (al ++ ext) j x.
Proof.
  unfold args_ok. intros al ext j x (A1 & A2 & A3). rewrite Zlength_app.
  pose proof (Zlength_nonneg ext).
  split; [ lia | ]. split; [ lia | ].
  intros k Hk. rewrite Znth_app1 by (pose proof (Zlength_nonneg al); lia). auto.
Qed.

Lemma node_ok_mono: forall nfns nslots al ext nb nb' j x,
  node_ok nfns nslots al nb j x -> nb <= nb' -> node_ok nfns nslots (al ++ ext) nb' j x.
Proof.
  intros nfns nslots al ext nb nb' j x H Hnb.
  unfold node_ok in *. destruct H as (W & T & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  split; [ auto | ]. split; [ auto | ].
  split. { intros E. destruct (H0 E) as (A1 & A2 & A3). split; [ auto | ]. split; [ auto | ].
           intros E3; specialize (A3 E3); lia. }
  split; [ auto | ]. split; [ auto | ]. split; [ auto | ].
  split. { intros E. destruct (H4 E) as (A1 & A2 & A3). split; [ auto | ]. split; [ auto | ].
           apply args_ok_mono; auto. }
  split. { intros E. destruct (H5 E) as (A1 & A2). split; [ auto | ]. apply args_ok_mono; auto. }
  split; [ auto | ]. split; [ auto | ]. auto.
Qed.

(* Comparing malloc's result with NULL is defined, also for malloc(0). *)
Lemma malloc_test_null (t: type) (q: val) (P: mpred):
  0 <= sizeof t ->
  ((if eq_dec q nullval then emp else malloc_token Ews t q * data_at_ Ews t q) * P
  |-- denote_tc_test_eq q (Vlong (Int64.repr 0)))%logic.
Proof.
  intros Ht. destruct (eq_dec q nullval).
  - subst. simpl. entailer!.
  - destruct (zlt 0 (sizeof t)).
    + sep_apply (data_at__valid_ptr Ews t q); [ auto | lia | ]. entailer!.
    + sep_apply (malloc_token_valid_pointer Ews t q); [ lia | ]. entailer!.
Qed.

Lemma blk_of_data_at: forall t q v, (malloc_token Ews t q * data_at Ews t v q |-- blk t q)%logic.
Proof.
  intros. unfold blk. destruct (eq_dec q nullval).
  - subst. assert_PROP (isptr nullval) by entailer!. contradiction.
  - cancel.
Qed.

Lemma blk_null: forall t, blk t nullval = emp.
Proof. intros. unfold blk. rewrite if_true by auto. auto. Qed.

Lemma add_ptr_uint_field: forall t n i p,
  complete_type cenv_cs t = true ->
  field_compatible (tarray t n) [] p -> 0 <= i < n -> i <= Int.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr t) tuint p (Vint (Int.repr i))) =
  field_address (tarray t n) (SUB i) p.
Proof.
  intros t n i p Hc FC Hi Hm. rewrite arr_field_address by auto.
  assert (isptr p) by (destruct FC; auto).
  unfold sem_binary_operation', sem_add.
  change (classify_add (tptr t) tuint) with (add_case_pi t Unsigned). cbv iota beta.
  rewrite sem_add_pi_ptr_special; auto. lia.
Qed.

Lemma blk_local_facts: forall t q, (blk t q |-- !! is_pointer_or_null q)%logic.
Proof.
  intros. unfold blk. destruct (eq_dec q nullval).
  - subst. entailer!.
  - entailer!.
Qed.
#[export] Hint Resolve blk_local_facts : saturate_local.

Lemma fns_free_local_facts: forall fns nfns L, (fns_free fns nfns L |-- !! is_pointer_or_null fns)%logic.
Proof.
  intros. unfold fns_free. destruct (eq_dec fns nullval).
  - subst. entailer!.
  - entailer!.
Qed.
#[export] Hint Resolve fns_free_local_facts : saturate_local.
