(* The operation 3 of the law: vx_store_rollback and the restore of the model. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.proof.Law OpenverseStore.proof.MainLib OpenverseStore.proof.MainInv.

Lemma cast_byte': forall b, 0 <= b <= Byte.max_unsigned ->
  force_val (sem_cast_i2i I8 Unsigned (Vint (Int.repr b))) = Vint (Int.repr b).
Proof.
  intros. simpl. f_equal. apply zero_ext_inrange.
  rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia.
Qed.

Lemma pre_snoc_sub {A B} {dA: Inhabitant A} {dB: Inhabitant B} (f: B -> A) (l: list A) (m: list B) i:
  sublist 0 i l = map f (sublist 0 i m) -> 0 <= i < Zlength l -> i < Zlength m ->
  sublist 0 (i + 1) (upd_Znth i l (f (Znth i m))) = map f (sublist 0 (i + 1) m).
Proof.
  intros H Hl Hm. rewrite (pre_snoc f l (sublist 0 i m) i (Znth i m) H Hl).
  rewrite (sublist_split 0 i (i+1)) by lia. rewrite sublist_len_1 by lia. reflexivity.
Qed.

Ltac ldeq H i l :=
  forward;
  try (solve [ rewrite (Znth_any _ _ i l _ H) by lia; entailer! ]);
  try rewrite (Znth_any _ _ i l _ H) by lia.

Lemma step_rollback {Espec: OracleKind}: forall E k st,
  semax Delta_main (MSTk E k st) op3_stmt (normal_ret_assert (EX st': mstate, MSTk E k st')).
Proof.
  intros. unfold Delta_main, MSTk, MLOC, MSEP, op3_stmt. abbreviate_semax.
  Intros. rename H into Hinv.
  pose proof Hinv as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?].
  pose proof (Zlength_nonneg (m_S st)).
  forward_if.
  2: { forward. Exists st. entailer!. }
  z64.
  forward.
  rewrite sub64_repr. change (Int.signed (Int.repr 1)) with 1.
  pose proof (top_facts E st Hinv ltac:(lia)) as (T1 & T2 & T3 & T4 & T5).
  remember (Zlength (m_S st) - 1) as d eqn:Hd.
  remember (Znth d (m_S st)) as s eqn:Hs.
  destruct (i_snaps d ltac:(lia)). rewrite <- Hs in *.
  sep_apply (SingletonHole.array_with_hole_intro Tsh t_mark d 3 (m_mk st) (e_marks E)); [ lia | ].
  rewrite s_mk.
  forward_call (e_st E, Tsh, Ews, e_sp E, e_jp E, e_op E, e_jcap E, e_ocap E, m_vs st, m_js st,
                Zlength (m_os st), Zlength (m_S st),
                field_address (tarray t_mark 3) [ArraySubsc d] (e_marks E), Tsh,
                sn_j s, Zlength (sn_os s), d).
  { cancel. }
  sep_apply (SingletonHole.array_with_hole_elim Tsh t_mark d 3
               (mval (sn_j s) (Zlength (sn_os s)) d) (m_mk st) (e_marks E)).
  rewrite upd_Znth_triv by (auto; lia).
  rewrite T2. rewrite Z.min_r by lia.
  assert (Hj: (if d =? 0 then [] else sublist 0 (sn_j s) (m_js st)) = sublist 0 (sn_j s) (m_js st)).
  { destruct (Z.eqb_spec d 0) as [E0 | E0]; auto.
    rewrite E0 in T5. rewrite sublist_nil in T5. simpl in T5. rewrite T5. reflexivity. }
  rewrite Hj.
  sep_apply (out_rep_trunc Ews (e_ocap E) (m_os st) (e_op E) (Zlength (sn_os s)) ltac:(rep_lia)).
  rewrite T4.
  assert (Rct: Zlength (Znth d (m_ct st)) = 4) by (apply (proj1 (Forall_Znth _ _) i_ct_rows); lia).
  assert (Rcb: Zlength (Znth d (m_cb st)) = 4) by (apply (proj1 (Forall_Znth _ _) i_cb_rows); lia).
  assert (Rco: Zlength (Znth d (m_co st)) = 8) by (apply (proj1 (Forall_Znth _ _) i_co_rows); lia).
  forward_for_simple_bound (e_ns E) (EX i: Z, EX mt': list val, EX mb': list val,
    ltac:(loop_inv [Zlength mt' = 4; sublist 0 i mt' = map tagv (sublist 0 i (sn_vs s));
                    Zlength mb' = 4; sublist 0 i mb' = map bitv (sublist 0 i (sn_vs s))]
           (temp _k (Vlong (Int64.repr k)) :: MLOC E (Zlength (m_os st)) (Zlength (m_js st)) d)
           (MSEP E (sn_vs s) (sublist 0 (sn_j s) (m_js st)) (Zlength (sn_os s)) d (sn_os s)
              (m_mk st) mt' mb' (m_mo st) (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)
              (data_at_ Tsh (tarray tuchar 2) (e_bs E))))).
  { Exists (m_mt st) (m_mb st). entailer!. }
  { forward.
    { rewrite (Znth2_pre _ tagv (m_ct st) (sn_vs s) d (e_ns E) i) by (auto; rep_lia).
      entailer!. }
    rewrite (Znth2_pre _ tagv (m_ct st) (sn_vs s) d (e_ns E) i) by (auto; rep_lia).
    forward.
    forward.
    { rewrite (Znth2_pre _ bitv (m_cb st) (sn_vs s) d (e_ns E) i) by (auto; rep_lia). entailer!. }
    rewrite (Znth2_pre _ bitv (m_cb st) (sn_vs s) d (e_ns E) i) by (auto; rep_lia).
    forward.
    Exists (upd_Znth i mt' (tagv (Znth i (sn_vs s)))) (upd_Znth i mb' (bitv (Znth i (sn_vs s)))).
    entailer!.
    repeat match goal with |- _ /\ _ => split end;
      first [ apply pre_snoc_sub; auto; lia | rewrite Zlength_upd_Znth_any; auto ]. }
  Intros mt' mb'.
  rewrite (sublist_same 0 (e_ns E) (sn_vs s)) in * by lia.
  forward.
  forward_loop (EX i: Z, EX mo': list val,
    ltac:(loop_inv [0 <= i <= Zlength (sn_os s); Zlength mo' = 8;
                    sublist 0 i mo' = bytes (sublist 0 i (sn_os s))]
           (temp _i (Vlong (Int64.repr i)) :: temp _k (Vlong (Int64.repr k)) ::
            MLOC E (Zlength (m_os st)) (Zlength (m_js st)) d)
           (MSEP E (sn_vs s) (sublist 0 (sn_j s) (m_js st)) (Zlength (sn_os s)) d (sn_os s)
              (m_mk st) mt' mb' mo' (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)
              (data_at_ Tsh (tarray tuchar 2) (e_bs E)))))
  continue: (EX i: Z, EX mo': list val,
    ltac:(loop_inv [0 <= i < Zlength (sn_os s); Zlength mo' = 8;
                    sublist 0 (i + 1) mo' = bytes (sublist 0 (i + 1) (sn_os s))]
           (temp _i (Vlong (Int64.repr i)) :: temp _k (Vlong (Int64.repr k)) ::
            MLOC E (Zlength (m_os st)) (Zlength (m_js st)) d)
           (MSEP E (sn_vs s) (sublist 0 (sn_j s) (m_js st)) (Zlength (sn_os s)) d (sn_os s)
              (m_mk st) mt' mb' mo' (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)
              (data_at_ Tsh (tarray tuchar 2) (e_bs E)))))
  break: (EX mo': list val,
    ltac:(loop_inv [Zlength mo' = 8; sublist 0 (Zlength (sn_os s)) mo' = bytes (sn_os s)]
           (temp _k (Vlong (Int64.repr k)) :: MLOC E (Zlength (m_os st)) (Zlength (m_js st)) d)
           (MSEP E (sn_vs s) (sublist 0 (sn_j s) (m_js st)) (Zlength (sn_os s)) d (sn_os s)
              (m_mk st) mt' mb' mo' (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)
              (data_at_ Tsh (tarray tuchar 2) (e_bs E))))).
  { Exists 0 (m_mo st). entailer!. }
  { Intros i mo'.
    ldeq s_cl d (m_cl st).
    forward_if.
    2: { z64.
         assert (Hi: i = Zlength (sn_os s)) by lia.
         subst i. rewrite (sublist_same 0 (Zlength (sn_os s)) (sn_os s)) in * by lia.
         forward. Exists mo'. entailer!. }
    z64.
    forward.
    { rewrite (Znth2_pre _ (fun b => Vint (Int.repr b)) (m_co st) (sn_os s) d (Zlength (sn_os s)) i)
        by (auto; rep_lia).
      entailer!. apply byte_repr_range, byte_at; auto; lia. }
    rewrite (Znth2_pre _ (fun b => Vint (Int.repr b)) (m_co st) (sn_os s) d (Zlength (sn_os s)) i)
      by (auto; rep_lia).
    forward.
    try rewrite cast_byte' by (apply byte_at; auto; lia).
    match goal with |- context [data_at Tsh (tarray tuchar 8) ?X (e_mout E)] => Exists i X end.
    entailer!.
    repeat match goal with |- _ /\ _ => split end;
      first [ apply (pre_snoc_sub (fun b => Vint (Int.repr b))); auto; lia
            | rewrite Zlength_upd_Znth_any; auto | lia ]. }
  { Intros i mo'. forward. Exists (i + 1) mo'. entailer!. }
  Intros mo'.
  ldeq s_cl d (m_cl st).
  ldeq s_cj d (m_cj st).
  pose proof (inv_rollback E st mt' mb' mo' Hinv ltac:(lia)) as Hn.
  cbv zeta in Hn. rewrite <- Hd in Hn. rewrite <- Hs in Hn.
  specialize (Hn ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                 ltac:(assumption) ltac:(assumption)).
  Exists (mkM (sn_vs s) (sublist 0 (sn_j s) (m_js st)) (sn_os s) (sublist 0 d (m_S st))
              (m_mk st) mt' mb' mo' (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)).
  cbn [m_vs m_js m_os m_S m_mk m_mt m_mb m_mo m_ct m_cb m_co m_cl m_cj].
  rewrite !Zlength_sublist by lia. rewrite !Z.sub_0_r.
  entailer!.
Qed.
