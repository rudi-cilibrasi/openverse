Require Import VST.floyd.proofauto.
(* The operation 4 of the law: vx_store_commit. *)
Require Import OpenverseStore.proof.Law OpenverseStore.proof.MainLib OpenverseStore.proof.MainInv.

Lemma step_commit {Espec: OracleKind}: forall E k st,
  semax Delta_main (MSTk E k st) op4_stmt (normal_ret_assert (EX st': mstate, MSTk E k st')).
Proof.
  intros. unfold Delta_main, MSTk, MLOC, MSEP, op4_stmt. abbreviate_semax.
  Intros. rename H into Hinv.
  pose proof (i_S _ _ Hinv).
  forward_if.
  2: { forward. Exists st. entailer!. }
  z64.
  forward.
  rewrite sub64_repr. change (Int.signed (Int.repr 1)) with 1.
  remember (Zlength (m_S st) - 1) as d eqn:Hd.
  destruct (i_snaps _ _ Hinv d ltac:(lia)).
  sep_apply (SingletonHole.array_with_hole_intro Tsh t_mark d 3 (m_mk st) (e_marks E)); [ lia | ].
  rewrite s_mk.
  forward_call (e_st E, Tsh, Ews, e_sp E, e_jp E, e_op E, e_jcap E, e_ocap E, m_vs st, m_js st,
                Zlength (m_os st), Zlength (m_S st),
                field_address (tarray t_mark 3) [ArraySubsc d] (e_marks E), Tsh,
                sn_j (Znth d (m_S st)), Zlength (sn_os (Znth d (m_S st))), d).
  { cancel. }
  sep_apply (SingletonHole.array_with_hole_elim Tsh t_mark d 3
               (mval (sn_j (Znth d (m_S st))) (Zlength (sn_os (Znth d (m_S st)))) d) (m_mk st) (e_marks E)).
  rewrite upd_Znth_triv by (auto; rewrite (i_mk_len _ _ Hinv); lia).
  pose proof (inv_commit E st Hinv ltac:(lia)) as Hn. simpl in Hn. rewrite <- Hd in Hn.
  forward_if.
  - z64. forward.
    Exists (mkM (m_vs st) (if d =? 0 then [] else m_js st) (m_os st) (sublist 0 d (m_S st))
              (m_mk st) (m_mt st) (m_mb st) (m_mo st) (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)).
    cbn [m_vs m_js m_os m_S m_mk m_mt m_mb m_mo m_ct m_cb m_co m_cl m_cj].
    rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
    rewrite (proj2 (Z.eqb_eq d 0)) in * by auto.
    entailer!.
  - z64. forward.
    Exists (mkM (m_vs st) (if d =? 0 then [] else m_js st) (m_os st) (sublist 0 d (m_S st))
              (m_mk st) (m_mt st) (m_mb st) (m_mo st) (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)).
    cbn [m_vs m_js m_os m_S m_mk m_mt m_mb m_mo m_ct m_cb m_co m_cl m_cj].
    rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.

    rewrite (proj2 (Z.eqb_neq d 0)) in * by auto.
    entailer!.
Qed.
