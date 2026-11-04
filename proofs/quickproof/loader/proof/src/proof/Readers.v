(* Bodies of the bounds-checked readers of load.c. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
#[local] Existing Instance Specs.CS.

Lemma body_rd_u8: semax_body Vprog Gprog f_rd_u8 rd_u8_spec.
Proof.
  start_function.
  forward. forward.
  forward_if.
  - forward. Exists 1 pos 0 (default_val tuint). unfold data_at_. entailer!.
  - i64s.
    unfold buf_rep. destruct (eq_dec buf nullval).
    { Intros. subst bs. rewrite Zlength_nil in *. lia. }
    assert (B := bytes_ok_Znth bs pos H ltac:(lia)).
    forward. forward. forward.
    { entailer!. rewrite Znth_vints by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_vints by lia.
    forward. forward. forward. forward.
    Exists 0 (pos + 1) (Znth pos bs) (Vint (Int.repr (Znth pos bs))).
    entailer!. unfold buf_rep. rewrite if_false by auto. auto.
Qed.

Lemma body_rd_child: semax_body Vprog Gprog f_rd_child rd_child_spec.
Proof.
  start_function.
  forward_call (r, buf, shb, bs, pos, acap, bcap, out, sho).
  Intros vret. destruct vret as [[[rc pos'] x] v]. cbn [fst snd] in *.
  forward_if.
  - forward. Exists 1 pos' 0 v. entailer!.
  - subst rc. destruct H7 as [-> Hx]; auto.
    forward.
    forward_if.
    + forward. Exists 9 pos' x (Vint (Int.repr x)). entailer!.
    + forward. Exists 0 pos' x (Vint (Int.repr x)). entailer!. split; [reflexivity | lia].
Qed.

Lemma body_rd_slot: semax_body Vprog Gprog f_rd_slot rd_slot_spec.
Proof.
  start_function.
  forward_call (r, buf, shb, bs, pos, acap, bcap, out, sho).
  Intros vret. destruct vret as [[[rc pos'] x] v]. cbn [fst snd] in *.
  forward_if.
  - forward. Exists 1 pos' 0 v. entailer!.
  - subst rc. destruct H7 as [-> Hx]; auto.
    forward.
    forward_if.
    + forward. Exists 10 pos' x (Vint (Int.repr x)). entailer!.
    + forward. Exists 0 pos' x (Vint (Int.repr x)). entailer!. split; [reflexivity | lia].
Qed.

Lemma body_rd_u32: semax_body Vprog Gprog f_rd_u32 rd_u32_spec.
Proof.
  start_function.
  forward. forward.
  forward_if.
  - forward. Exists 1 pos 0 (default_val tuint). unfold data_at_. entailer!.
  - i64s.
    buf_nonnull.
    assert (B0 := bytes_ok_Znth bs pos H ltac:(lia)).
    assert (B1 := bytes_ok_Znth bs (pos + 1) H ltac:(lia)).
    assert (B2 := bytes_ok_Znth bs (pos + 2) H ltac:(lia)).
    assert (B3 := bytes_ok_Znth bs (pos + 3) H ltac:(lia)).
    forward. forward. forward.
    { entailer!. rewrite Znth_vints by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_vints by lia.
    forward. forward. forward. forward.
    { entailer!. rewrite Znth_vints by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_vints by lia.
    forward. forward. forward. forward.
    { entailer!. rewrite Znth_vints by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_vints by lia.
    forward. forward. forward. forward.
    { entailer!. rewrite Znth_vints by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_vints by lia.
    forward. forward. forward. forward. forward.
    match goal with |- context [data_at sho tuint (Vint ?V) out] =>
      Exists 0 (pos + 4) (Int.unsigned V) (Vint V) end.
    entailer!.
    + split; [ rewrite Int.repr_unsigned; reflexivity | rep_lia ].
    + rewrite buf_rep_nonnull by auto. cancel.
Qed.

Lemma body_rd_i64: semax_body Vprog Gprog f_rd_i64 rd_i64_spec.
Proof.
  start_function.
  forward. forward. forward.
  forward_if.
  - forward. Exists 1 pos 0 (default_val tlong). unfold data_at_. entailer!.
  - i64s. buf_nonnull.
    forward_for_simple_bound 8 (EX k: Z, EX u: int64,
      PROP () LOCAL (temp _u (Vlong u); temp _r r; temp _out out)
      SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r;
           data_at shb (tarray tuchar (Zlength bs)) (vints bs) buf; data_at_ sho tlong out))%assert.
    + Exists (Int64.repr 0). entailer!.
    + assert (Bk := bytes_ok_Znth bs (pos + i) H ltac:(lia)).
      forward. forward. forward.
      { entailer!. rewrite Znth_vints by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite Znth_vints by lia.
      forward.
      { entailer!. rewrite (Int64.Z_mod_modulus_eq i), Z.mod_small by rep_lia.
        rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. lia. }
      match goal with |- context [temp _u (Vlong ?U)] => Exists U end. entailer!.
    + Intros u. forward. forward.
      forward_if (EX w: int64,
        PROP () LOCAL (temp _r r; temp _out out)
        SEP (data_at Tsh t_ld (LD buf (Zlength bs) (pos + 8) acap bcap) r;
             data_at shb (tarray tuchar (Zlength bs)) (vints bs) buf; data_at sho tlong (Vlong w) out))%assert.
      * forward. Exists u. entailer!.
      * assert (Hu: Int64.max_signed < Int64.unsigned u).
        { match goal with H: Int64.ltu _ u = true |- _ => rename H into Hl end.
          unfold Int64.ltu in Hl. rewrite Int64.unsigned_repr in Hl by rep_lia.
          destruct (zlt _ _); [ change Int64.max_signed with 9223372036854775807; lia | discriminate ]. }
        destruct (i64_neg_not_range u Hu) as [R1 R2].
        forward.
        { entailer!. change (Int64.signed Int64.zero) with 0. rep_lia. }
        match goal with |- context [data_at sho tlong (Vlong ?W) out] => Exists W end.
        entailer!.
      * Intros w. forward. Exists 0 (pos + 8) (Int64.signed w) (Vlong w). entailer!.
        -- rewrite Int64.repr_signed. split; [ reflexivity | apply Int64.signed_range ].
        -- rewrite buf_rep_nonnull by auto. cancel.
Qed.

