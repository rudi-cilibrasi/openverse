(* Body of vx_store_out_append. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.store.code.
Require Import OpenverseStore.proof.StoreSpecs OpenverseStore.proof.Tac.

Lemma out_push: forall (oc: list val) (os bs: list Z) i,
  0 <= i < Zlength bs -> Zlength os + i < Zlength oc ->
  sublist 0 (Zlength os + i) oc = bytes (os ++ sublist 0 i bs) ->
  sublist 0 (Zlength os + (i + 1)) (upd_Znth (Zlength os + i) oc (Vint (Int.repr (Znth i bs)))) =
  bytes (os ++ sublist 0 (i + 1) bs).
Proof.
  intros. unfold bytes in *.
  rewrite (sublist_split 0 i (i+1)) by lia. rewrite sublist_len_1 by lia.
  rewrite app_assoc. rewrite map_app. rewrite <- H1. list_solve.
Qed.

Lemma cast_byte: forall b, 0 <= b <= Byte.max_unsigned ->
  force_val (sem_cast_i2i I8 Unsigned (Vint (Int.repr b))) = Vint (Int.repr b).
Proof.
  intros. simpl. f_equal. apply zero_ext_inrange.
  rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia.
Qed.

Lemma Znth_bytes: forall i bs, 0 <= i < Zlength bs -> Znth i (bytes bs) = Vint (Int.repr (Znth i bs)).
Proof. intros. unfold bytes. rewrite Znth_map by lia. reflexivity. Qed.

Lemma body_vx_store_out_append: semax_body Vprog Gprog f_vx_store_out_append vx_store_out_append_spec.
Proof.
  start_function.
  unfold store_rep, out_rep. Intros jc oc. unfold sval.
  forward. forward.
  forward_if.
  { rewrite sub64_repr in *. z64. forward.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    unfold store_rep, out_rep. Exists jc oc. unfold sval. entailer!. }
  rewrite sub64_repr in *. z64.
  forward_for_simple_bound n (@exp (environ -> mpred) _ Z (fun i => @exp (environ -> mpred) _ (list val) (fun oc' =>
    PROP (Zlength oc' = ocap; sublist 0 (Zlength os + i) oc' = bytes (os ++ sublist 0 i bs))
    LOCAL (temp _s s; temp _b pb; temp _n (Vlong (Int64.repr n)))
    SEP (data_at shs t_store
           (sp, (Vlong (Int64.repr (Zlength vs)), (jp, (Vlong (Int64.repr jcap),
            (Vlong (Int64.repr (Zlength js)), (op, (Vlong (Int64.repr ocap),
             (Vlong (Int64.repr (Zlength os)), Vlong (Int64.repr depth))))))))) s;
         buf t_val shb (Zlength vs) (map vval vs) sp;
         buf t_undo shb jcap jc jp;
         buf tuchar shb ocap oc' op;
         data_at shp (tarray tuchar (Zlength bs)) (bytes bs) pb)))).
  { Exists oc. rewrite sublist_nil, app_nil_r, Z.add_0_r. entailer!. }
  { rewrite (buf_nonnull tuchar) by lia.
    forward. forward. forward.
    { entailer!. unfold bytes. rewrite Znth_map by lia. 
      match goal with HF: Forall (fun b => 0 <= b <= Byte.max_unsigned) bs |- _ =>
        pose proof (proj1 (Forall_Znth _ _) HF i ltac:(lia)) end.
      simpl in *. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
    forward.
    assert (Hb: 0 <= Znth i bs <= Byte.max_unsigned).
    { match goal with HF: Forall (fun b => 0 <= b <= Byte.max_unsigned) bs |- _ =>
        exact (proj1 (Forall_Znth _ _) HF i ltac:(lia)) end. }
    rewrite !Znth_bytes by lia. rewrite cast_byte by auto.
    Exists (upd_Znth (Zlength os + i) oc' (Vint (Int.repr (Znth i bs)))).
    rewrite (buf_nonnull tuchar) by lia.
    entailer!.
    repeat split; try (apply out_push; auto; lia); try list_solve. }
  Intros oc'.
  forward. forward.
  forward.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  unfold store_rep, out_rep. Exists jc oc'. unfold sval.
  replace (Zlength (os ++ sublist 0 n bs)) with (Zlength os + n) by list_solve.
  entailer!.
Qed.
