(* The operation 1 of the law: vx_store_set. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Pick.
Require Import OpenverseStore.proof.Law OpenverseStore.proof.MainLib OpenverseStore.proof.MainInv.

Lemma set_fail: forall vs js jcap d sl v,
  set_ret vs js jcap d sl <> 0 ->
  set_vs vs js jcap d sl v = vs /\ set_js vs js jcap d sl = js.
Proof.
  intros. unfold set_vs, set_js. destruct (Z.eqb_spec (set_ret vs js jcap d sl) 0); [ contradiction | ].
  split; reflexivity.
Qed.

Lemma set_ok: forall vs js jcap d sl v,
  set_ret vs js jcap d sl = 0 ->
  set_vs vs js jcap d sl v = upd_Znth sl vs v /\
  set_js vs js jcap d sl = if 0 <? d then js ++ [(sl, Znth sl vs)] else js.
Proof.
  intros. unfold set_vs, set_js. rewrite H. split; reflexivity.
Qed.

Lemma cmpu_ge_val: forall a b,
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Cge (Int64.repr a) (Int64.repr b)) = Vint (Int.repr (if b <=? a then 1 else 0)).
Proof.
  intros. unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt a b); destruct (Z.leb_spec b a); try lia; reflexivity.
Qed.

Lemma step_set {Espec: OracleKind}: forall E k st,
  semax Delta_main (MSTk E k st) op1_stmt (normal_ret_assert (EX st': mstate, MSTk E k st')).
Proof.
  intros. unfold Delta_main, MSTk, MLOC, MSEP, op1_stmt. abbreviate_semax.
  Intros. rename H into Hinv.
  pose proof Hinv as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?].
  forward_call. Intros sl.
  assert_PROP (field_compatible tulong [] (e_tg E) /\ field_compatible tulong [] (e_bt E)) as FC by entailer!.
  destruct FC as [FCt FCb].
  sep_apply (ulong_as_bytes Tsh (e_tg E)).
  forward_call (e_tg E, 8, Tsh).
  { rewrite if_false by (intro Hn; rewrite Hn in FCt; destruct FCt; contradiction). cancel. }
  Intros bs1. rewrite if_false by (intro Hn; rewrite Hn in FCt; destruct FCt; contradiction).
  sep_apply (pick_tulong Tsh bs1 (e_tg E) H0 H1 FCt). Intros tg.
  sep_apply (ulong_as_bytes Tsh (e_bt E)).
  forward_call (e_bt E, 8, Tsh).
  { rewrite if_false by (intro Hn; rewrite Hn in FCb; destruct FCb; contradiction). cancel. }
  Intros bs2. rewrite if_false by (intro Hn; rewrite Hn in FCb; destruct FCb; contradiction).
  sep_apply (pick_tulong Tsh bs2 (e_bt E) H2 H3 FCb). Intros bt.
  forward. forward.
  forward_call (e_st E, Tsh, Ews, e_sp E, e_jp E, e_op E, e_jcap E, e_ocap E, m_vs st, m_js st,
                Zlength (m_os st), Zlength (m_S st), sl, (tg, bt)).
  forward.
  forward_if.
  { z64.
    assert (Hr: set_ret (m_vs st) (m_js st) (e_jcap E) (Zlength (m_S st)) sl = 3)
      by (unfold set_ret; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    rewrite Hr.
    assert1.
    Exists st.
    destruct (set_fail (m_vs st) (m_js st) (e_jcap E) (Zlength (m_S st)) sl (tg, bt)) as [Hv Hj];
      [ rewrite Hr; discriminate | ].
    rewrite Hv, Hj. entailer!. }
  z64.
  forward_if (temp _t'13 (Vint (Int.repr (if andb (0 <? Zlength (m_S st)) (e_jcap E <=? Zlength (m_js st)) then 1 else 0)))).
  { z64. forward. entailer!.
    rewrite cmpu_ge_val by rep_lia. rewrite (proj2 (Z.ltb_lt 0 (Zlength (m_S st)))) by lia. reflexivity. }
  { z64. forward. entailer!.
    rewrite (proj2 (Z.ltb_ge 0 (Zlength (m_S st)))) by lia. reflexivity. }
  forward_if.
  { (* the journal is full *)
    assert (Hr: set_ret (m_vs st) (m_js st) (e_jcap E) (Zlength (m_S st)) sl = 4).
    { unfold set_ret. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      destruct (andb _ _); [ reflexivity | ]. 
      match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end. }
    rewrite Hr.
    assert1.
    Exists st.
    destruct (set_fail (m_vs st) (m_js st) (e_jcap E) (Zlength (m_S st)) sl (tg, bt)) as [Hv Hj];
      [ rewrite Hr; discriminate | ].
    rewrite Hv, Hj. entailer!. }
  (* the write succeeds *)
  assert (Hb: andb (0 <? Zlength (m_S st)) (e_jcap E <=? Zlength (m_js st)) = false).
  { match goal with H: Int.repr (if _ then 1 else 0) = Int.zero |- _ => revert H end.
    destruct (andb _ _); [ | reflexivity ].
    intro H5. change Int.zero with (Int.repr 0) in H5.
    apply repr_inj_small in H5; [ discriminate | rep_lia | rep_lia ]. }
  assert (Hr: set_ret (m_vs st) (m_js st) (e_jcap E) (Zlength (m_S st)) sl = 0)
    by (unfold set_ret; rewrite (proj2 (Z.ltb_lt _ _)) by lia; rewrite Hb; reflexivity).
  assert (Hnf: ~ (0 < Zlength (m_S st) /\ e_jcap E <= Zlength (m_js st))).
  { intros [Ha Hc]. rewrite (proj2 (Z.ltb_lt _ _) Ha), (proj2 (Z.leb_le _ _) Hc) in Hb. discriminate. }
  rewrite Hr.
  assert1.
  forward. forward. forward. forward.
  forward_if (temp _mjlen (Vlong (Int64.repr (Zlength
     (if 0 <? Zlength (m_S st) then m_js st ++ [(sl, Znth sl (m_vs st))] else m_js st))))).
  { z64. forward. rewrite (proj2 (Z.ltb_lt _ _)) by lia. entailer!.
    rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity. }
  { z64. forward. rewrite (proj2 (Z.ltb_ge _ _)) by lia. entailer!. }
  destruct (set_ok (m_vs st) (m_js st) (e_jcap E) (Zlength (m_S st)) sl (tg, bt) Hr) as [Hv Hj].
  rewrite Hv, Hj.
  Exists (mkM (upd_Znth sl (m_vs st) (tg, bt))
              (if 0 <? Zlength (m_S st) then m_js st ++ [(sl, Znth sl (m_vs st))] else m_js st)
              (m_os st) (m_S st) (m_mk st)
              (upd_Znth sl (m_mt st) (Vlong tg)) (upd_Znth sl (m_mb st) (Vlong bt))
              (m_mo st) (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)).
  cbn [m_vs m_js m_os m_S m_mk m_mt m_mb m_mo m_ct m_cb m_co m_cl m_cj].
  pose proof (inv_set E st sl (tg, bt) Hinv ltac:(lia) Hnf) as Hn.
  entailer!.
Qed.
