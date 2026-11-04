(* main: the setup, the 32 steps (StepBody.step_body) and the end. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Assembly QuickProof.Pick.
Require Import OpenverseStore.proof.Law OpenverseStore.proof.MainLib OpenverseStore.proof.MainInv OpenverseStore.proof.StepBody.

Lemma malloc_test_null (t: type) (q: val) (P: mpred):
  0 <= sizeof t ->
  (if eq_dec q nullval then emp else malloc_token Ews t q * data_at_ Ews t q) * P
  |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Ht. destruct (eq_dec q nullval).
  - subst. simpl. entailer!.
  - destruct (zlt 0 (sizeof t)).
    + sep_apply (data_at__valid_ptr Ews t q); [ auto | lia | ]. entailer!.
    + sep_apply (malloc_token_valid_pointer Ews t q); [ lia | ]. entailer!.
Qed.

Lemma malloc_buf: forall t n p, 0 <= n -> (p = nullval -> n = 0) ->
  (if eq_dec p nullval then emp else malloc_token Ews (tarray t n) p * data_at_ Ews (tarray t n) p)
  |-- mtok (tarray t n) p * buf t Ews n (Zrepeat (default_val t) n) p.
Proof.
  intros t n p Hn Hp. unfold mtok, buf. destruct (eq_dec p nullval).
  - rewrite Hp by auto. entailer!.
  - rewrite data_at__tarray. cancel.
Qed.

Lemma free_buf: forall t n l p,
  mtok (tarray t n) p * buf t Ews n l p
  |-- (if eq_dec p nullval then emp else malloc_token Ews (tarray t n) p * data_at_ Ews (tarray t n) p).
Proof.
  intros. unfold mtok, buf. destruct (eq_dec p nullval).
  - entailer!.
  - sep_apply (data_at_data_at_ Ews (tarray t n) l p). cancel.
Qed.

Definition init_state (vs: list V) (mt mb: list val) : mstate :=
  mkM vs [] [] [] (Zrepeat (default_val t_mark) 3) mt mb (Zrepeat (default_val tuchar) 8)
      (Zrepeat (default_val (tarray tulong 4)) 3) (Zrepeat (default_val (tarray tulong 4)) 3)
      (Zrepeat (default_val (tarray tuchar 8)) 3) (Zrepeat (default_val tulong) 3)
      (Zrepeat (default_val tulong) 3).

Lemma Forall_Zrepeat_len: forall {A} (x: list A) n len,
  Zlength x = len -> Forall (fun r => Zlength r = len) (Zrepeat x n).
Proof.
  intros. apply Forall_forall. intros y Hy. unfold Zrepeat in Hy.
  apply repeat_spec in Hy. subst. auto.
Qed.

Lemma inv_init: forall E vs mt mb,
  0 <= e_ns E <= 4 -> 0 <= e_jcap E <= 8 -> 0 <= e_ocap E <= 8 ->
  Zlength vs = e_ns E -> Zlength mt = 4 -> sublist 0 (e_ns E) mt = map tagv vs ->
  Zlength mb = 4 -> sublist 0 (e_ns E) mb = map bitv vs ->
  inv_ok E (init_state vs mt mb).
Proof.
  intros. unfold init_state. constructor; simpl; auto; try lia.
  all: try (rewrite Zlength_nil; lia).
  all: try (apply Forall_Zrepeat_len; reflexivity).
  all: try (intros d Hd; rewrite Zlength_nil in Hd; lia).
  all: try (rewrite sublist_nil; reflexivity).
  all: try reflexivity.
  all: try (apply Forall_nil).
Qed.

Ltac bcase b :=
  destruct b;
  try (match goal with H: ?x = Int.zero |- _ =>
         exfalso; apply Int.one_not_zero; exact H end);
  try (match goal with H: ?x <> Int.zero |- _ =>
         exfalso; apply H; reflexivity end).

(* The locals' memory back to data_at_, as the stack frame wants it. *)
Ltac to_data_at_ p :=
  match goal with |- context [data_at ?sh ?t ?v p] => sep_apply (data_at_data_at_ sh t v p) end.

Lemma body_main: semax_body Vmain Gmain f_main (_main, main_spec_std whole_prog').
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call. Intros ns.
  forward_call.
  change (Int.signed (Int.repr 4)) with 4 in H0. apply assume_le in H0; [ | rep_lia | rep_lia ].
  forward_call. Intros jcap.
  forward_call.
  change (Int.signed (Int.repr 8)) with 8 in H2. apply assume_le in H2; [ | rep_lia | rep_lia ].
  forward_call. Intros ocap.
  forward_call.
  change (Int.signed (Int.repr 8)) with 8 in H4. apply assume_le in H4; [ | rep_lia | rep_lia ].
  forward_call (tarray t_val ns, gv).
  { entailer!. simpl. rewrite Z.max_r by lia. do 3 f_equal. lia. }
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros sp.
  forward_call (tarray t_undo jcap, gv).
  { entailer!. simpl. rewrite Z.max_r by lia. do 3 f_equal. lia. }
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros jp.
  forward_call (tarray tuchar ocap, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros op.
  forward_if (temp _t'7 (Vint (if andb (0 <? ns) (if eq_dec sp nullval then true else false)
                                then Int.one else Int.zero))).
  { z64. destruct (eq_dec sp nullval) as [Esp | Esp].
    - subst sp. forward.
      entailer!. rewrite (proj2 (Z.ltb_lt 0 ns)) by lia. reflexivity.
    - cbv iota. Intros.
      assert_PROP (isptr sp) as Psp by entailer!.
      forward.
      destruct sp; try contradiction.
      entailer!. rewrite andb_false_r. reflexivity. }
  { z64. forward. entailer!. rewrite (proj2 (Z.ltb_ge 0 ns)) by lia. reflexivity. }
  remember (andb (0 <? ns) (if eq_dec sp nullval then true else false)) as b1 eqn:Eb1.
  forward_if (temp _t'8 (Vint (if orb b1 (andb (0 <? jcap) (if eq_dec jp nullval then true else false))
                                then Int.one else Int.zero))).
  { bcase b1. forward. entailer!. }
  { bcase b1. simpl orb.
    forward_if.
    - z64. destruct (eq_dec jp nullval) as [Ejp | Ejp].
      + subst jp. forward. forward. entailer!. rewrite (proj2 (Z.ltb_lt 0 jcap)) by lia. reflexivity.
      + cbv iota. Intros. assert_PROP (isptr jp) as Pjp by entailer!.
        forward. forward. destruct jp; try contradiction.
        entailer!. rewrite andb_false_r. reflexivity.
    - z64. forward. entailer!. rewrite (proj2 (Z.ltb_ge 0 jcap)) by lia. reflexivity. }
  remember (andb (0 <? jcap) (if eq_dec jp nullval then true else false)) as b2 eqn:Eb2.
  forward_if (temp _t'9 (Vint (if orb (orb b1 b2) (andb (0 <? ocap) (if eq_dec op nullval then true else false))
                                then Int.one else Int.zero))).
  { bcase (orb b1 b2). forward. entailer!. }
  { bcase (orb b1 b2). simpl orb.
    forward_if.
    - z64. destruct (eq_dec op nullval) as [Eop | Eop].
      + subst op. forward. forward. entailer!. rewrite (proj2 (Z.ltb_lt 0 ocap)) by lia. reflexivity.
      + cbv iota. Intros. assert_PROP (isptr op) as Pop by entailer!.
        forward. forward. destruct op; try contradiction.
        entailer!. rewrite andb_false_r. reflexivity.
    - z64. forward. entailer!. rewrite (proj2 (Z.ltb_ge 0 ocap)) by lia. reflexivity. }
  remember (andb (0 <? ocap) (if eq_dec op nullval then true else false)) as b3 eqn:Eb3.
  forward_if (orb (orb b1 b2) b3 = false).
  { forward. Exists (Int.repr 0). entailer!. }
  { destruct (orb (orb b1 b2) b3) eqn:Eb; [ exfalso; apply Int.one_not_zero; assumption | ].
    forward. entailer!. }
  Intros.
  assert (Hsp: sp = nullval -> ns = 0).
  { intros Hn. subst sp. destruct (Z.ltb_spec 0 ns); [ | lia ].
    destruct (eq_dec nullval nullval); [ | congruence ].
    subst b1. simpl in *. discriminate. }
  assert (Hjp: jp = nullval -> jcap = 0).
  { intros Hn. subst jp. destruct (Z.ltb_spec 0 jcap); [ | lia ].
    destruct (eq_dec nullval nullval); [ | congruence ].
    subst b2. rewrite orb_true_r in *. simpl in *. discriminate. }
  assert (Hop: op = nullval -> ocap = 0).
  { intros Hn. subst op. destruct (Z.ltb_spec 0 ocap); [ | lia ].
    destruct (eq_dec nullval nullval); [ | congruence ].
    subst b3. rewrite orb_true_r in *. discriminate. }
  sep_apply (malloc_buf t_val ns sp ltac:(lia) Hsp).
  sep_apply (malloc_buf t_undo jcap jp ltac:(lia) Hjp).
  sep_apply (malloc_buf tuchar ocap op ltac:(lia) Hop).
  Intros.
  rewrite (data_at__tarray Tsh tulong 4).
  forward_for_simple_bound ns (EX i: Z, EX vsi: list V, EX mt: list val, EX mb: list val,
    PROP (Zlength vsi = i; Zlength mt = 4; sublist 0 i mt = map tagv vsi;
          Zlength mb = 4; sublist 0 i mb = map bitv vsi)
    LOCAL (temp _nslots (Vlong (Int64.repr ns)); temp _jcap (Vlong (Int64.repr jcap));
           temp _ocap (Vlong (Int64.repr ocap)); temp _slots sp; temp _jour jp; temp _out op;
           lvar _v__1 t_val v_v__1; lvar _v t_val v_v; lvar _bs (tarray tuchar 2) v_bs;
           lvar _bt tulong v_bt; lvar _tg tulong v_tg; lvar _cjlen (tarray tulong 3) v_cjlen;
           lvar _colen (tarray tulong 3) v_colen; lvar _cout (tarray (tarray tuchar 8) 3) v_cout;
           lvar _cbits (tarray (tarray tulong 4) 3) v_cbits; lvar _ctag (tarray (tarray tulong 4) 3) v_ctag;
           lvar _mout (tarray tuchar 8) v_mout; lvar _mbits (tarray tulong 4) v_mbits;
           lvar _mtag (tarray tulong 4) v_mtag; lvar _marks (tarray t_mark 3) v_marks;
           lvar _st t_store v_st; gvars gv)
    SEP (mem_mgr gv; has_ext tt;
         mtok (tarray t_val ns) sp; mtok (tarray t_undo jcap) jp; mtok (tarray tuchar ocap) op;
         buf t_val Ews ns (map vval vsi ++ Zrepeat (default_val t_val) (ns - i)) sp;
         buf t_undo Ews jcap (Zrepeat (default_val t_undo) jcap) jp;
         buf tuchar Ews ocap (Zrepeat (default_val tuchar) ocap) op;
         data_at_ Tsh t_val v_v__1; data_at_ Tsh t_val v_v; data_at_ Tsh (tarray tuchar 2) v_bs;
         data_at_ Tsh tulong v_bt; data_at_ Tsh tulong v_tg; data_at_ Tsh (tarray tulong 3) v_cjlen;
         data_at_ Tsh (tarray tulong 3) v_colen; data_at_ Tsh (tarray (tarray tuchar 8) 3) v_cout;
         data_at_ Tsh (tarray (tarray tulong 4) 3) v_cbits; data_at_ Tsh (tarray (tarray tulong 4) 3) v_ctag;
         data_at_ Tsh (tarray tuchar 8) v_mout;
         data_at Tsh (tarray tulong 4) mb v_mbits; data_at Tsh (tarray tulong 4) mt v_mtag;
         data_at_ Tsh (tarray t_mark 3) v_marks; data_at_ Tsh t_store v_st)).
  { Exists (@nil V) (Zrepeat (default_val tulong) 4) (Zrepeat (default_val tulong) 4).
    rewrite Z.sub_0_r. entailer!. }
  { Intros.
    rewrite (buf_nonnull t_val) by lia.
    sep_apply (SingletonHole.array_with_hole_intro Tsh tulong i 4 mt v_mtag); [ lia | ].
    assert_PROP (field_compatible tulong [] (field_address (tarray tulong 4) [ArraySubsc i] v_mtag))
      as FCi by entailer!.
    sep_apply (data_at_data_at_ Tsh tulong (Znth i mt) (field_address (tarray tulong 4) [ArraySubsc i] v_mtag)).
    sep_apply (ulong_as_bytes Tsh (field_address (tarray tulong 4) [ArraySubsc i] v_mtag)).
    forward_call (field_address (tarray tulong 4) [ArraySubsc i] v_mtag, 8, Tsh).
    { rewrite if_false by (intro Hn; rewrite Hn in FCi; destruct FCi; contradiction). cancel. }
    Intros bs1. rewrite if_false by (intro Hn; rewrite Hn in FCi; destruct FCi; contradiction).
    sep_apply (pick_tulong Tsh bs1 _ ltac:(assumption) ltac:(assumption) FCi). Intros t1.
    sep_apply (SingletonHole.array_with_hole_elim Tsh tulong i 4 (Vlong t1) mt v_mtag).
    sep_apply (SingletonHole.array_with_hole_intro Tsh tulong i 4 mb v_mbits); [ lia | ].
    assert_PROP (field_compatible tulong [] (field_address (tarray tulong 4) [ArraySubsc i] v_mbits))
      as FCj by entailer!.
    sep_apply (data_at_data_at_ Tsh tulong (Znth i mb) (field_address (tarray tulong 4) [ArraySubsc i] v_mbits)).
    sep_apply (ulong_as_bytes Tsh (field_address (tarray tulong 4) [ArraySubsc i] v_mbits)).
    forward_call (field_address (tarray tulong 4) [ArraySubsc i] v_mbits, 8, Tsh).
    { rewrite if_false by (intro Hn; rewrite Hn in FCj; destruct FCj; contradiction). cancel. }
    Intros bs2. rewrite if_false by (intro Hn; rewrite Hn in FCj; destruct FCj; contradiction).
    sep_apply (pick_tulong Tsh bs2 _ ltac:(assumption) ltac:(assumption) FCj). Intros t2.
    sep_apply (SingletonHole.array_with_hole_elim Tsh tulong i 4 (Vlong t2) mb v_mbits).
    forward.
    { rewrite upd_Znth_same by lia. entailer!. }
    rewrite upd_Znth_same by lia.
    forward.
    forward.
    { rewrite upd_Znth_same by lia. entailer!. }
    rewrite upd_Znth_same by lia.
    forward.
    Exists (vsi ++ [(t1, t2)]) (upd_Znth i mt (Vlong t1)) (upd_Znth i mb (Vlong t2)).
    rewrite (buf_nonnull t_val) by lia.
    assert (HL: Zlength (map vval vsi ++ Zrepeat (default_val t_val) (ns - i)) = ns) by list_solve.
    match goal with |- context [data_at Ews (tarray t_val ns) ?L sp] =>
      replace L with (map vval (vsi ++ [(t1, t2)]) ++ Zrepeat (default_val t_val) (ns - (i + 1))) end.
    2: { rewrite upd_Znth_same by (rewrite ?Zlength_upd_Znth_any; list_solve). simpl fst.
         rewrite upd_Znth_twice by list_solve.
         change (Vlong t1, Vlong t2) with (vval (t1, t2)).
         rewrite map_app. simpl map. list_solve. }
    entailer!.
    split; [ list_solve | ].
    split; [ apply (pre_snoc tagv mt vsi (Zlength vsi) (t1, t2)) | apply (pre_snoc bitv mb vsi (Zlength vsi) (t1, t2)) ];
      auto; lia. }
  Intros vs mt mb.
  rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
  forward_call (v_st, Tsh, Ews, sp, jp, op, vs, Zrepeat (default_val t_undo) jcap, jcap,
                Zrepeat (default_val tuchar) ocap, ocap).
  all: try (solve [ rewrite H6; entailer! ]).
  all: try (solve [ repeat match goal with |- _ /\ _ => split end; auto; try rep_lia;
                    rewrite Zlength_Zrepeat by lia; reflexivity ]).
  forward. forward. forward.
  pose (E := mkE gv ns jcap ocap sp jp op v_st v_marks v_mtag v_mbits v_mout v_ctag v_cbits v_cout
                 v_colen v_cjlen v_tg v_bt v_bs v_v v_v__1).
  rewrite (data_at__tarray Tsh t_mark 3).
  rewrite (data_at__tarray Tsh tuchar 8).
  rewrite (data_at__tarray Tsh (tarray tulong 4) 3).
  rewrite (data_at__tarray Tsh (tarray tuchar 8) 3).
  rewrite (data_at__tarray Tsh tulong 3).
  pose proof (inv_init E vs mt mb ltac:(unfold E; simpl; lia) ltac:(unfold E; simpl; lia) ltac:(unfold E; simpl; lia)
                ltac:(unfold E; simpl; lia) ltac:(assumption) ltac:(unfold E; simpl; assumption) ltac:(assumption)
                ltac:(unfold E; simpl; assumption)) as Hinit.
  forward_for_simple_bound 32 (EX k: Z, EX st: mstate,
    ltac:(loop_inv [inv_ok E st] (MLOC E (Zlength (m_os st)) (Zlength (m_js st)) (Zlength (m_S st)))
           (MSEP E (m_vs st) (m_js st) (Zlength (m_os st)) (Zlength (m_S st)) (m_os st)
              (m_mk st) (m_mt st) (m_mb st) (m_mo st) (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)
              (data_at_ Tsh (tarray tuchar 2) (e_bs E))))).
  { Exists (init_state vs mt mb).
    unfold E, init_state.
    cbn [e_gv e_ns e_jcap e_ocap e_sp e_jp e_op e_st e_marks e_mtag e_mbits e_mout e_ctag e_cbits
         e_cout e_colen e_cjlen e_tg e_bt e_bs e_v e_v1 m_vs m_js m_os m_S m_mk m_mt m_mb m_mo
         m_ct m_cb m_co m_cl m_cj].
    rewrite !Zlength_nil.
    entailer!. }
  { eapply semax_pre; [ | eapply semax_normal_weak; [ apply (step_body E i st) | ] ].
    - unfold MSTk, MLOC, MSEP. entailer!.
    - match goal with |- ENTAIL _, _ |-- RA_normal ?P => unfold P, abbreviate end.
      cbn [RA_normal normal_ret_assert]. Intros st'. Exists st'. unfold MSTk, MLOC, MSEP. entailer!. }
  Intros st.
  rename H6 into Hvs_init.
  match goal with H: inv_ok E st |- _ => rename H into Hinv end.
  pose proof (i_vs _ _ Hinv) as Hvs. unfold E in Hvs; simpl in Hvs.
  unfold E.
  cbn [e_gv e_ns e_jcap e_ocap e_sp e_jp e_op e_st e_marks e_mtag e_mbits e_mout e_ctag e_cbits
       e_cout e_colen e_cjlen e_tg e_bt e_bs e_v e_v1].
  rewrite (data_at__eq Tsh t_val v_v__1).
  forward_call (v_st, Tsh, Ews, sp, jp, op, jcap, ocap, m_vs st, m_js st,
                Zlength (m_os st), Zlength (m_S st), ns, v_v__1, Tsh, default_val t_val).
  rewrite (proj2 (Z.ltb_ge ns (Zlength (m_vs st)))) by lia.
  assert1.
  unfold out_rep. Intros oc.
  sep_apply (free_buf tuchar ocap oc op).
  forward_call (tarray tuchar ocap, op, gv).
  unfold store_rep. Intros jc.
  sep_apply (free_buf t_undo jcap jc jp).
  forward_call (tarray t_undo jcap, jp, gv).
  rewrite Hvs.
  sep_apply (free_buf t_val ns (map vval (m_vs st)) sp).
  forward_call (tarray t_val ns, sp, gv).
  to_data_at_ v_st. to_data_at_ v_marks. to_data_at_ v_mtag. to_data_at_ v_mbits.
  to_data_at_ v_mout. to_data_at_ v_ctag. to_data_at_ v_cbits. to_data_at_ v_cout.
  to_data_at_ v_colen. to_data_at_ v_cjlen. to_data_at_ v_v__1.
  forward.
  Exists (Int.repr 0). entailer!.
Qed.

