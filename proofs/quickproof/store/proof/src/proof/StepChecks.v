(* The checks at the end of each step: the store agrees with the model. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.proof.Law OpenverseStore.proof.MainLib OpenverseStore.proof.MainInv.

Lemma step_checks {Espec: OracleKind}: forall E k st,
  semax Delta_main (MSTk E k st) checks_stmt (normal_ret_assert (MSTk E k st)).
Proof.
  intros. unfold Delta_main, MSTk, MLOC, MSEP, checks_stmt. abbreviate_semax.
  Intros. rename H into Hinv.
  pose proof Hinv as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?].
  forward_call (e_st E, Tsh, Ews, e_sp E, e_jp E, e_op E, e_jcap E, e_ocap E, m_vs st, m_js st,
                Zlength (m_os st), Zlength (m_S st)).
  assert1.
  forward_for_simple_bound (e_ns E) (EX i: Z, ltac:(st_inv E k st (@nil Prop))).
  { entailer!. }
  { rewrite (data_at__eq Tsh t_val (e_v E)).
    forward_call (e_st E, Tsh, Ews, e_sp E, e_jp E, e_op E, e_jcap E, e_ocap E, m_vs st, m_js st,
                  Zlength (m_os st), Zlength (m_S st), i, e_v E, Tsh, default_val t_val).
    rewrite (proj2 (Z.ltb_lt i (Zlength (m_vs st)))) by lia.
    assert1.
    forward.
    forward.
    { rewrite (Znth_pre tagv (m_mt st) (m_vs st) (e_ns E) i) by (auto; lia). entailer!. }
    rewrite (Znth_pre tagv (m_mt st) (m_vs st) (e_ns E) i) by (auto; lia).
    unfold vval, tagv. simpl fst.
    assert1.
    forward.
    forward.
    { rewrite (Znth_pre bitv (m_mb st) (m_vs st) (e_ns E) i) by (auto; lia). entailer!. }
    rewrite (Znth_pre bitv (m_mb st) (m_vs st) (e_ns E) i) by (auto; lia).
    unfold bitv. simpl snd.
    assert1. }
  forward_for_simple_bound (Zlength (m_os st)) (EX i: Z, ltac:(st_inv E k st (@nil Prop))).
  { entailer!. }
  { unfold out_rep at 1. Intros oc.
    rewrite (buf_nonnull tuchar) by lia.
    ldpre (fun b => Vint (Int.repr b)) oc (m_os st) (Zlength (m_os st)) i.
    ldpre (fun b => Vint (Int.repr b)) (m_mo st) (m_os st) (Zlength (m_os st)) i.
    assert1.
    unfold out_rep. Exists oc. rewrite (buf_nonnull tuchar) by lia. entailer!. }
  entailer!.
Qed.
