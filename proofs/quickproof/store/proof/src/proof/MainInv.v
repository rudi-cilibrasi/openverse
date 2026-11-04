(* How each operation of the law keeps main's invariant inv_ok: pure lemmas. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.proof.Law OpenverseStore.proof.MainLib.

Lemma inv_commit: forall E st, inv_ok E st -> 0 < Zlength (m_S st) ->
  let d := Zlength (m_S st) - 1 in
  inv_ok E (mkM (m_vs st) (if d =? 0 then [] else m_js st) (m_os st) (sublist 0 d (m_S st))
              (m_mk st) (m_mt st) (m_mb st) (m_mo st) (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)).
Proof.
  intros E st H HS d. destruct H.
  assert (Hd: 0 <= d) by (unfold d; lia).
  constructor; simpl; auto.
  - destruct (d =? 0); [ rewrite Zlength_nil; lia | auto ].
  - rewrite Zlength_sublist by lia. lia.
  - rewrite rev_S_last in i_chain by auto. fold d in i_chain.
    pose proof (chain_commit _ _ _ _ _ i_chain) as Hc.
    rewrite Zlength_rev, Zlength_sublist in Hc by lia. replace (d - 0) with d in Hc by lia. exact Hc.
  - intros d' Hd'. rewrite Zlength_sublist in Hd' by lia.
    destruct (i_snaps d' ltac:(lia)). constructor; simpl; rewrite ?Znth_S_sub by lia; auto.
Qed.

Lemma inv_rollback: forall E st mt' mb' mo',
  inv_ok E st -> 0 < Zlength (m_S st) ->
  let d := Zlength (m_S st) - 1 in
  let s := Znth d (m_S st) in
  Zlength mt' = 4 -> sublist 0 (e_ns E) mt' = map tagv (sn_vs s) ->
  Zlength mb' = 4 -> sublist 0 (e_ns E) mb' = map bitv (sn_vs s) ->
  Zlength mo' = 8 -> sublist 0 (Zlength (sn_os s)) mo' = bytes (sn_os s) ->
  inv_ok E (mkM (sn_vs s) (sublist 0 (sn_j s) (m_js st)) (sn_os s) (sublist 0 d (m_S st))
              (m_mk st) mt' mb' mo' (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)).
Proof.
  intros E st mt' mb' mo' H HS d s H1 H2 H3 H4 H5 H6.
  pose proof (top_facts E st H HS) as (T1 & T2 & T3 & T4 & T5). fold d s in T1, T2, T3, T4, T5.
  destruct H.
  assert (Hd: 0 <= d) by (unfold d; lia).
  destruct (i_snaps d ltac:(unfold d; lia)). fold s in s_vs, s_os, s_j, s_bytes.
  constructor; simpl; auto.
  - rewrite Zlength_sublist by lia. lia.
  - lia.
  - rewrite Zlength_sublist by lia. lia.
  - intros d' Hd'. rewrite Zlength_sublist in Hd' by lia.
    destruct (i_snaps d' ltac:(lia)). constructor; simpl; rewrite ?Znth_S_sub by lia; auto.
Qed.

Lemma inv_mark: forall E st ct' cb' co',
  inv_ok E st -> Zlength (m_S st) < 3 ->
  let d := Zlength (m_S st) in
  rows_ok (m_ct st) ct' d (map tagv (m_vs st)) 4 ->
  rows_ok (m_cb st) cb' d (map bitv (m_vs st)) 4 ->
  rows_ok (m_co st) co' d (bytes (m_os st)) 8 ->
  inv_ok E (mkM (m_vs st) (m_js st) (m_os st) (m_S st ++ [mksnap (m_vs st) (m_os st) (Zlength (m_js st))])
              (upd_Znth d (m_mk st) (mval (Zlength (m_js st)) (Zlength (m_os st)) d))
              (m_mt st) (m_mb st) (m_mo st) ct' cb' co'
              (upd_Znth d (m_cl st) (Vlong (Int64.repr (Zlength (m_os st)))))
              (upd_Znth d (m_cj st) (Vlong (Int64.repr (Zlength (m_js st)))))).
Proof.
  intros E st ct' cb' co' H HS d (C1 & C2 & C3 & C4) (B1 & B2 & B3 & B4) (O1 & O2 & O3 & O4).
  destruct H.
  assert (Hd: 0 <= d) by (unfold d; apply Zlength_nonneg).
  rewrite Zlength_map in C4, B4. unfold bytes in O4. rewrite Zlength_map in O4. fold (bytes (m_os st)) in O4.
  constructor; simpl; auto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite rev_unit. apply chain_mark. auto.
  - rewrite Zlength_upd_Znth_any. auto.
  - rewrite Zlength_upd_Znth_any. auto.
  - rewrite Zlength_upd_Znth_any. auto.
  - intros d' Hd'. rewrite Zlength_app, Zlength_cons, Zlength_nil in Hd'.
    destruct (Z.eq_dec d' d) as [E1 | E1].
    + subst d'.
      assert (Hz: Znth d (m_S st ++ [mksnap (m_vs st) (m_os st) (Zlength (m_js st))]) =
                  mksnap (m_vs st) (m_os st) (Zlength (m_js st))).
      { rewrite Znth_app2 by (unfold d; lia). replace (d - Zlength (m_S st)) with 0 by (unfold d; lia).
        apply Znth_0_cons. }
      constructor; simpl; rewrite Hz; simpl.
      * auto.
      * lia.
      * apply Zlength_nonneg.
      * auto.
      * rewrite upd_Znth_same by lia. reflexivity.
      * rewrite <- i_vs. auto.
      * rewrite <- i_vs. auto.
      * auto.
      * rewrite upd_Znth_same by lia. reflexivity.
      * rewrite upd_Znth_same by lia. reflexivity.
    + destruct (i_snaps d' ltac:(unfold d in *; lia)).
      constructor; simpl; rewrite ?Znth_S_app by (unfold d in *; lia);
        rewrite ?upd_Znth_diff by (unfold d in *; lia);
        rewrite ?C3, ?B3, ?O3 by (unfold d in *; lia); auto.
Qed.

Lemma inv_set: forall E st sl v,
  inv_ok E st -> 0 <= sl < e_ns E ->
  ~ (0 < Zlength (m_S st) /\ e_jcap E <= Zlength (m_js st)) ->
  inv_ok E (mkM (upd_Znth sl (m_vs st) v)
              (if 0 <? Zlength (m_S st) then m_js st ++ [(sl, Znth sl (m_vs st))] else m_js st)
              (m_os st) (m_S st) (m_mk st)
              (upd_Znth sl (m_mt st) (tagv v)) (upd_Znth sl (m_mb st) (bitv v))
              (m_mo st) (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)).
Proof.
  intros E st sl v H Hsl Hfull. destruct H.
  constructor; simpl; auto.
  - rewrite Zlength_upd_Znth_any. auto.
  - destruct (Z.ltb_spec 0 (Zlength (m_S st))); auto.
    rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - destruct (Z.ltb_spec 0 (Zlength (m_S st))).
    + rewrite rev_S_last in * by auto. apply chain_set_top; auto. lia.
    + assert (HS0: m_S st = []) by (apply Zlength_nil_inv; pose proof (Zlength_nonneg (m_S st)); lia).
      rewrite HS0 in *. simpl in *. auto.
  - rewrite Zlength_upd_Znth_any. auto.
  - apply pre_upd; auto. lia.
  - rewrite Zlength_upd_Znth_any. auto.
  - apply pre_upd; auto. lia.
  - intros d' Hd'. destruct (i_snaps d' Hd'). constructor; simpl; auto.
Qed.

Lemma inv_append: forall E st bs n mo',
  inv_ok E st -> 0 <= n <= Zlength bs -> n <= e_ocap E - Zlength (m_os st) ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  Zlength mo' = 8 -> sublist 0 (Zlength (m_os st) + n) mo' = bytes (m_os st ++ sublist 0 n bs) ->
  inv_ok E (mkM (m_vs st) (m_js st) (m_os st ++ sublist 0 n bs) (m_S st) (m_mk st)
              (m_mt st) (m_mb st) mo' (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)).
Proof.
  intros E st bs n mo' H Hn Hroom Hb H1 H2. destruct H.
  constructor; simpl; auto.
  - rewrite Zlength_app, Zlength_sublist by lia. lia.
  - apply Forall_app. split; auto. apply Forall_sublist. auto.
  - apply chain_append. auto.
  - rewrite Zlength_app, Zlength_sublist by lia. rewrite Z.sub_0_r. auto.
  - intros d' Hd'. destruct (i_snaps d' Hd'). constructor; simpl; auto.
Qed.
