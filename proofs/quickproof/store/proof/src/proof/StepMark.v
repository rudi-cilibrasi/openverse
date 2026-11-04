(* The operation 0 of the law: vx_store_mark and the copies of the model. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.proof.Law OpenverseStore.proof.MainLib OpenverseStore.proof.MainInv.

Lemma cast_byte': forall b, 0 <= b <= Byte.max_unsigned ->
  force_val (sem_cast_i2i I8 Unsigned (Vint (Int.repr b))) = Vint (Int.repr b).
Proof.
  intros. simpl. f_equal. apply zero_ext_inrange.
  rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia.
Qed.

Lemma step_mark {Espec: OracleKind}: forall E k st,
  semax Delta_main (MSTk E k st) op0_stmt (normal_ret_assert (EX st': mstate, MSTk E k st')).
Proof.
  intros. unfold Delta_main, MSTk, MLOC, MSEP, op0_stmt. abbreviate_semax.
  Intros. rename H into Hinv.
  pose proof Hinv as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?].
  pose proof (Zlength_nonneg (m_S st)).
  forward_if.
  2: { forward. Exists st. entailer!. }
  z64.
  remember (Zlength (m_S st)) as d eqn:Hd.
  sep_apply (SingletonHole.array_with_hole_intro Tsh t_mark d 3 (m_mk st) (e_marks E)); [ lia | ].
  forward_call (e_st E, Tsh, Ews, e_sp E, e_jp E, e_op E, e_jcap E, e_ocap E, m_vs st, m_js st,
                Zlength (m_os st), d,
                field_address (tarray t_mark 3) [ArraySubsc d] (e_marks E), Tsh, Znth d (m_mk st)).
  { cancel. }
  sep_apply (SingletonHole.array_with_hole_elim Tsh t_mark d 3
               (mval (Zlength (m_js st)) (Zlength (m_os st)) d) (m_mk st) (e_marks E)).
  forward_for_simple_bound (e_ns E) (EX i: Z, EX ct': list (list val), EX cb': list (list val),
    ltac:(loop_inv [rows_ok (m_ct st) ct' d (map tagv (sublist 0 i (m_vs st))) 4;
                    rows_ok (m_cb st) cb' d (map bitv (sublist 0 i (m_vs st))) 4]
           (temp _k (Vlong (Int64.repr k)) :: MLOC E (Zlength (m_os st)) (Zlength (m_js st)) d)
           (MSEP E (m_vs st) (m_js st) (Zlength (m_os st)) (d + 1) (m_os st)
              (upd_Znth d (m_mk st) (mval (Zlength (m_js st)) (Zlength (m_os st)) d))
              (m_mt st) (m_mb st) (m_mo st) ct' cb' (m_co st) (m_cl st) (m_cj st)
              (data_at_ Tsh (tarray tuchar 2) (e_bs E))))).
  { Exists (m_ct st) (m_cb st). entailer!.
    split; apply rows_ok_start; auto. }
  { 
    ldpre tagv (m_mt st) (m_vs st) (e_ns E) i.
    forward.
    ldpre bitv (m_mb st) (m_vs st) (e_ns E) i.
    forward.
    match goal with |- context [data_at Tsh (tarray (tarray tulong 4) 3) ?X (e_ctag E)] =>
      match goal with |- context [data_at Tsh (tarray (tarray tulong 4) 3) ?Y (e_cbits E)] =>
        Exists X Y end end.
    entailer!.
    split; apply rows_ok_step_any; auto; lia. }
  Intros ct' cb'.
  rewrite sublist_same in * by lia.
  forward_for_simple_bound (Zlength (m_os st)) (EX i: Z, EX co': list (list val),
    ltac:(loop_inv [rows_ok (m_co st) co' d (bytes (sublist 0 i (m_os st))) 8]
           (temp _k (Vlong (Int64.repr k)) :: MLOC E (Zlength (m_os st)) (Zlength (m_js st)) d)
           (MSEP E (m_vs st) (m_js st) (Zlength (m_os st)) (d + 1) (m_os st)
              (upd_Znth d (m_mk st) (mval (Zlength (m_js st)) (Zlength (m_os st)) d))
              (m_mt st) (m_mb st) (m_mo st) ct' cb' co' (m_cl st) (m_cj st)
              (data_at_ Tsh (tarray tuchar 2) (e_bs E))))).
  { Exists (m_co st). entailer!. apply rows_ok_start; auto. }
  { ldpre (fun b => Vint (Int.repr b)) (m_mo st) (m_os st) (Zlength (m_os st)) i.
    forward.
    try rewrite cast_byte' by (apply byte_at; auto; lia).
    match goal with |- context [data_at Tsh (tarray (tarray tuchar 8) 3) ?X (e_cout E)] => Exists X end.
    entailer!.
    apply (rows_ok_step_any _ (fun b => Vint (Int.repr b))); auto; lia. }
  Intros co'.
  rewrite sublist_same in * by lia.
  forward. forward. forward.
  rewrite add64_repr. change (Int.signed (Int.repr 1)) with 1.
  subst d.
  pose proof (inv_mark E st ct' cb' co' Hinv ltac:(lia) H1 H2 H3) as Hn.
  Exists (mkM (m_vs st) (m_js st) (m_os st) (m_S st ++ [mksnap (m_vs st) (m_os st) (Zlength (m_js st))])
              (upd_Znth (Zlength (m_S st)) (m_mk st) (mval (Zlength (m_js st)) (Zlength (m_os st)) (Zlength (m_S st))))
              (m_mt st) (m_mb st) (m_mo st) ct' cb' co'
              (upd_Znth (Zlength (m_S st)) (m_cl st) (Vlong (Int64.repr (Zlength (m_os st)))))
              (upd_Znth (Zlength (m_S st)) (m_cj st) (Vlong (Int64.repr (Zlength (m_js st)))))).
  cbn [m_vs m_js m_os m_S m_mk m_mt m_mb m_mo m_ct m_cb m_co m_cl m_cj].
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
Qed.
