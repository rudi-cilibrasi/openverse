(* Body of vx_store_rollback. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.store.code.
Require Import OpenverseStore.proof.StoreSpecs OpenverseStore.proof.Tac.

Lemma undo_step: forall (js: list J) vs j, 0 < j <= Zlength js ->
  undo (sublist (j-1) (Zlength js) js) vs =
  upd_Znth (fst (Znth (j-1) js)) (undo (sublist j (Zlength js) js) vs) (snd (Znth (j-1) js)).
Proof.
  intros. rewrite (sublist_next (j-1)) by lia. simpl. replace (j-1+1) with j by lia. reflexivity.
Qed.

Lemma jc_split: forall (jc: list (reptype t_undo)) (js: list J),
  Zlength js <= Zlength jc -> sublist 0 (Zlength js) jc = map jval js ->
  jc = map jval js ++ sublist (Zlength js) (Zlength jc) jc.
Proof.
  intros. rewrite <- H0. rewrite sublist_rejoin by list_solve. rewrite sublist_same; auto.
Qed.

Lemma body_vx_store_rollback: semax_body Vprog Gprog f_vx_store_rollback vx_store_rollback_spec.
Proof.
  start_function.
  unfold store_rep. Intros jc. unfold sval, mval.
  rewrite (jc_split jc js) by (auto; lia).
  assert (HR: Zlength (map jval js ++ sublist (Zlength js) (Zlength jc) jc) = Zlength jc) by list_solve.
  forget (sublist (Zlength js) (Zlength jc) jc) as R.
  subst jcap.
  forward_loop (@exp (environ -> mpred) _ Z (fun j =>
    PROP (mj <= j <= Zlength js)
    LOCAL (temp _s s; temp _m pm)
    SEP (data_at shs t_store
           (sp, (Vlong (Int64.repr (Zlength vs)), (jp, (Vlong (Int64.repr (Zlength jc)),
            (Vlong (Int64.repr j), (op, (Vlong (Int64.repr ocap), (Vlong (Int64.repr olen),
             Vlong (Int64.repr depth))))))))) s;
         buf t_val shb (Zlength vs) (map vval (undo (sublist j (Zlength js) js) vs)) sp;
         buf t_undo shb (Zlength jc) (map jval js ++ R) jp;
         data_at shm t_mark (Vlong (Int64.repr mj), (Vlong (Int64.repr mo), Vlong (Int64.repr md))) pm)))
  break: (PROP ()
    LOCAL (temp _s s; temp _m pm)
    SEP (data_at shs t_store
           (sp, (Vlong (Int64.repr (Zlength vs)), (jp, (Vlong (Int64.repr (Zlength jc)),
            (Vlong (Int64.repr mj), (op, (Vlong (Int64.repr ocap), (Vlong (Int64.repr olen),
             Vlong (Int64.repr depth))))))))) s;
         buf t_val shb (Zlength vs) (map vval (undo (sublist mj (Zlength js) js) vs)) sp;
         buf t_undo shb (Zlength jc) (map jval js ++ R) jp;
         data_at shm t_mark (Vlong (Int64.repr mj), (Vlong (Int64.repr mo), Vlong (Int64.repr md))) pm)).
  { Exists (Zlength js). rewrite sublist_nil. simpl undo. entailer!. }
  { Intros j.
    forward. forward.
    forward_if.
    2: { z64. forward. assert (j = mj) by lia. subst j. entailer!. }
    z64.
    forward. forward.
    rewrite sub64_repr. change (Int.signed (Int.repr 1)) with 1.
    rewrite (buf_nonnull t_undo) by rep_lia.
    forward. forward.
    forward.
    { entailer!. rewrite Znth_app1 by list_solve. rewrite Znth_map by list_solve. simpl; auto. }
    rewrite Znth_app1 by list_solve. rewrite Znth_map by list_solve.
    forward.
    assert (Hsl: 0 <= fst (Znth (j-1) js) < Zlength vs).
    { pose proof H7 as H7'. rewrite Forall_Znth in H7'. apply H7'. lia. }
    forward_if.
    2: { z64. lia. }
    z64.
    rewrite (buf_nonnull t_val) by rep_lia.
    forward. forward. forward. forward.
    { entailer!. rewrite Znth_app1 by list_solve. rewrite Znth_map by list_solve. simpl; auto. }
    rewrite Znth_app1 by list_solve. rewrite Znth_map by list_solve.
    destruct (Znth (j-1) js) as [sl0 [tg0 bt0]] eqn:Ee.
    unfold jval at 1 2. simpl fst in *. simpl snd in *.
    forward.
    forward. forward. forward.
    forward.
    { entailer!. rewrite Znth_app1 by list_solve. rewrite Znth_map by list_solve. rewrite Ee. simpl; auto. }
    rewrite Znth_app1 by list_solve. rewrite Znth_map by list_solve. rewrite Ee.
    unfold jval at 1. simpl fst in *. simpl snd in *.
    forward.
    Exists (j-1).
    rewrite (undo_step js vs j) by lia. rewrite Ee. simpl fst; simpl snd.
    assert (HL: 0 <= sl0 < Zlength (map vval (undo (sublist j (Zlength js) js) vs)))
      by (rewrite Zlength_map, Zlength_undo; lia).
    rewrite upd_Znth_same by (rewrite ?Zlength_upd_Znth_any; exact HL).
    rewrite upd_Znth_twice by exact HL.
    simpl fst.
    change (Vlong tg0, Vlong bt0) with (vval (tg0, bt0)).
    rewrite upd_Znth_map.
    rewrite (buf_nonnull t_val) by lia.
    rewrite (buf_nonnull t_undo) by rep_lia.
    entailer!. }
  forward. forward.
  forward_if (PROP () LOCAL (temp _s s; temp _m pm)
    SEP (data_at shs t_store
           (sp, (Vlong (Int64.repr (Zlength vs)), (jp, (Vlong (Int64.repr (Zlength jc)),
            (Vlong (Int64.repr mj), (op, (Vlong (Int64.repr ocap), (Vlong (Int64.repr (Z.min olen mo)),
             Vlong (Int64.repr depth))))))))) s;
         buf t_val shb (Zlength vs) (map vval (undo (sublist mj (Zlength js) js) vs)) sp;
         buf t_undo shb (Zlength jc) (map jval js ++ R) jp;
         data_at shm t_mark (Vlong (Int64.repr mj), (Vlong (Int64.repr mo), Vlong (Int64.repr md))) pm)).
  { z64. forward. forward. rewrite Z.min_r by lia. entailer!. }
  { z64. forward. rewrite Z.min_l by lia. entailer!. }
  forward. forward. forward.
  forward_if.
  - z64. subst md. forward.
    unfold store_rep. Exists (map jval js ++ R). rewrite Z.eqb_refl. rewrite Zlength_undo.
    entailer!. list_solve.
  - z64. forward. fix_sf.
    unfold store_rep. Exists (map jval js ++ R). rewrite (proj2 (Z.eqb_neq md 0)) by auto.
    rewrite Zlength_undo.
    unfold sval. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
    entailer!.
    repeat split; try list_solve; try (apply Forall_sublist; auto).
Qed.
