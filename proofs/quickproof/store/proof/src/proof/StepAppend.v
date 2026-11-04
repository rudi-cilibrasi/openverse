(* The operation 2 of the law: vx_store_out_append. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.proof.Law OpenverseStore.proof.MainLib OpenverseStore.proof.MainInv.
Require OpenverseStore.proof.StoreAppend.

Lemma step_append {Espec: OracleKind}: forall E k st,
  semax Delta_main (MSTk E k st) op2_stmt (normal_ret_assert (EX st': mstate, MSTk E k st')).
Proof.
  intros. unfold Delta_main, MSTk, MLOC, MSEP, op2_stmt. abbreviate_semax.
  Intros. rename H into Hinv.
  pose proof Hinv as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?].
  forward_call. Intros x.
  forward.
  assert_PROP (field_compatible (tarray tuchar 2) [] (e_bs E)) as FCs by entailer!.
  forward_call (e_bs E, 2, Tsh).
  { rewrite if_false by (intro Hn; rewrite Hn in FCs; destruct FCs; contradiction). cancel. }
  Intros bs. rewrite if_false by (intro Hn; rewrite Hn in FCs; destruct FCs; contradiction).
  match goal with H: Zlength bs = 2 |- _ => rename H into Hbs end.
  assert (Hn: Int64.modu (Int64.repr x) (Int64.repr (Int.signed (Int.repr 3))) = Int64.repr (x mod 3)).
  { change (Int.signed (Int.repr 3)) with 3. unfold Int64.modu.
    rewrite !Int64.unsigned_repr by rep_lia. reflexivity. }
  rewrite Hn.
  assert (Hn3: 0 <= x mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  remember (x mod 3) as n eqn:Hnx.
  change (map (fun b => Vint (Int.repr b)) bs) with (bytes bs).
  assert (Ebs: data_at Tsh (tarray tuchar 2) (bytes bs) (e_bs E) =
               data_at Tsh (tarray tuchar (Zlength bs)) (bytes bs) (e_bs E)) by (rewrite Hbs; reflexivity).
  rewrite Ebs.
  forward_call (e_st E, Tsh, Ews, e_sp E, e_jp E, e_op E, e_jcap E, e_ocap E, m_vs st, m_js st,
                Zlength (m_S st), m_os st, e_bs E, Tsh, bs, n).
  forward_if.
  { rewrite sub64_repr in *. z64.
    rewrite (proj2 (Z.ltb_lt (e_ocap E - Zlength (m_os st)) n)) by lia.
    assert1.
    Exists st. rewrite <- Ebs. entailer!. }
  rewrite sub64_repr in *. z64.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  assert1.
  forward_for_simple_bound n (EX i: Z, EX mo': list val,
    ltac:(loop_inv [Zlength mo' = 8;
                    sublist 0 (Zlength (m_os st) + i) mo' = bytes (m_os st ++ sublist 0 i bs)]
           (temp _n (Vlong (Int64.repr n)) :: temp _k (Vlong (Int64.repr k)) ::
            MLOC E (Zlength (m_os st)) (Zlength (m_js st)) (Zlength (m_S st)))
           (MSEP E (m_vs st) (m_js st) (Zlength (m_os st) + n) (Zlength (m_S st)) (m_os st ++ sublist 0 n bs)
              (m_mk st) (m_mt st) (m_mb st) mo' (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)
              (data_at Tsh (tarray tuchar (Zlength bs)) (bytes bs) (e_bs E))))).
  { Exists (m_mo st). entailer!. rewrite ?sublist_nil, ?app_nil_r, ?Z.add_0_r. auto. }
  { assert (Hb: 0 <= Znth i bs <= Byte.max_unsigned) by (apply byte_at; auto; lia).
    forward.
    { rewrite StoreAppend.Znth_bytes by lia. entailer!; try lia. }
    rewrite StoreAppend.Znth_bytes by lia.
    forward.
    { entailer!. }
    rewrite ?StoreAppend.cast_byte by auto.
    Exists (upd_Znth (Zlength (m_os st) + i) mo' (Vint (Int.repr (Znth i bs)))).
    entailer!.
    split; [ list_solve | apply StoreAppend.out_push; auto; lia ]. apply derives_refl. }
  Intros mo'.
  forward.
  rewrite add64_repr.
  pose proof (inv_append E st bs n mo' Hinv ltac:(lia) ltac:(lia)
                ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hn'.
  Exists (mkM (m_vs st) (m_js st) (m_os st ++ sublist 0 n bs) (m_S st) (m_mk st)
              (m_mt st) (m_mb st) mo' (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)).
  cbn [m_vs m_js m_os m_S m_mk m_mt m_mb m_mo m_ct m_cb m_co m_cl m_cj].
  replace (Zlength (m_os st ++ sublist 0 n bs)) with (Zlength (m_os st) + n) by list_solve.
  rewrite <- Ebs.
  entailer!.
Qed.
