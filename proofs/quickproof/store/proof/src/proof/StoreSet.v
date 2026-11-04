(* Body of vx_store_set. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.store.code.
Require Import OpenverseStore.proof.StoreSpecs OpenverseStore.proof.Tac.

Lemma journal_push: forall (jc: list (reptype t_undo)) js e k,
  Zlength js < Zlength jc -> sublist 0 (Zlength js) jc = map jval js -> k = Zlength js + 1 ->
  sublist 0 k (upd_Znth (Zlength js) jc (jval e)) = map jval (js ++ [e]).
Proof.
  intros. subst k. rewrite map_app. rewrite <- H0. list_solve.
Qed.

Ltac fws := forward; try (solve [ entailer!; try rep_lia; rewrite ?Znth_map by rep_lia; unfold vval, jval; simpl; auto ]).

Lemma body_vx_store_set: semax_body Vprog Gprog f_vx_store_set vx_store_set_spec.
Proof.
  start_function.
  unfold store_rep. Intros jc. unfold sval. subst jcap.
  forward.
  forward_if.
  { z64. forward.
    unfold set_vs, set_js, set_ret. rewrite (proj2 (Z.ltb_ge slot (Zlength vs))) by lia. simpl.
    unfold store_rep. Exists jc. entailer!. }
  z64.
  forward.
  forward_if (EX jc': list (reptype t_undo),
    PROP (Zlength jc' = (Zlength jc);
          sublist 0 (Zlength (if 0 <? depth then js ++ [(slot, Znth slot vs)] else js)) jc' =
            map jval (if 0 <? depth then js ++ [(slot, Znth slot vs)] else js);
          Zlength (if 0 <? depth then js ++ [(slot, Znth slot vs)] else js) <= (Zlength jc);
          ~ (0 < depth /\ (Zlength jc) <= Zlength js))
    LOCAL (temp _s s; temp _slot (Vlong (Int64.repr slot)); temp _tag (Vlong (fst v));
           temp _bits (Vlong (snd v)))
    SEP (data_at shs t_store
           (sval sp (Zlength vs) jp (Zlength jc)
              (Zlength (if 0 <? depth then js ++ [(slot, Znth slot vs)] else js)) op ocap olen depth) s;
         buf t_val shb (Zlength vs) (map vval vs) sp;
         buf t_undo shb (Zlength jc) jc' jp)).
  { (* inside a context *)
    z64.
    forward. forward.
    forward_if.
    { z64. forward.
      unfold set_vs, set_js, set_ret.
      rewrite (proj2 (Z.ltb_lt slot (Zlength vs))) by lia.
      rewrite (proj2 (Z.ltb_lt 0 depth)) by lia.
      rewrite (proj2 (Z.leb_le (Zlength jc) (Zlength js))) by lia. simpl.
      unfold store_rep. Exists jc. entailer!. }
    z64.
    rewrite (buf_nonnull t_undo) by rep_lia.
    rewrite (buf_nonnull t_val) by lia.
    do 15 fws.
    Exists (upd_Znth (Zlength js) jc (jval (slot, Znth slot vs))).
    rewrite (proj2 (Z.ltb_lt 0 depth)) by lia.
    rewrite add64_repr. change (Int.signed (Int.repr 1)) with 1.
    rewrite Znth_map by lia.
    assert (Hlt: 0 <= Zlength js < Zlength jc) by rep_lia.
    rewrite !upd_Znth_same by (rewrite ?Zlength_upd_Znth_any; exact Hlt).
    rewrite !upd_Znth_twice by (rewrite ?Zlength_upd_Znth_any; exact Hlt).
    unfold vval. simpl fst; simpl snd.
    change (Vlong (Int64.repr slot), (Vlong (fst (Znth slot vs)), Vlong (snd (Znth slot vs))))
      with (jval (slot, Znth slot vs)).
    rewrite (buf_nonnull t_undo) by rep_lia.
    unfold sval. rewrite Zlength_app, Zlength_cons, Zlength_nil.
    entailer!.
    apply journal_push; auto; lia. }
  { z64. forward. Exists jc.
    rewrite (proj2 (Z.ltb_ge 0 depth)) by lia.
    entailer!. }
  Intros jc'.
  rewrite (buf_nonnull t_val) by lia.
  do 4 fws.
  forward.
  assert (Hr: set_ret vs js (Zlength jc) depth slot = 0).
  { unfold set_ret. rewrite (proj2 (Z.ltb_lt slot (Zlength vs))) by lia.
    destruct (Z.ltb_spec 0 depth); destruct (Z.leb_spec (Zlength jc) (Zlength js)); simpl; auto.
    exfalso; tauto. }
  assert (Fj: Forall (fun e : J => 0 <= fst e < Zlength vs)
                (if 0 <? depth then js ++ [(slot, Znth slot vs)] else js)).
  { destruct (0 <? depth); auto. apply Forall_app; split; auto. constructor; simpl; auto. lia. }
  unfold set_vs, set_js. rewrite Hr. rewrite Z.eqb_refl. simpl andb.
  unfold store_rep. Exists jc'.
  rewrite Znth_map by lia.
  assert (Hs: 0 <= slot < Zlength (map vval vs)) by (rewrite Zlength_map; lia).
  rewrite upd_Znth_same by (rewrite ?Zlength_upd_Znth_any; exact Hs).
  rewrite upd_Znth_twice by exact Hs.
  unfold vval at 1 2. simpl fst; simpl snd.
  change (Vlong (fst v), Vlong (snd v)) with (vval v).
  rewrite upd_Znth_map.
  rewrite (buf_nonnull t_val) by (rewrite Zlength_upd_Znth_any; lia).
  rewrite Zlength_upd_Znth_any.
  entailer!.
Qed.
