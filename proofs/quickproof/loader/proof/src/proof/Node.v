(* Body of load_node. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
Require Import OpenverseLoader.proof.Fields.
Require Import OpenverseLoader.proof.NodeLemmas.
#[local] Existing Instance Specs.CS.

Ltac ret_loader :=
  let vret := fresh "vret" in
  Intros vret; destruct vret as [[[[[rcN posN] xsN] blN] xN] vN]; cbn [fst snd] in *;
  forward; Exists rcN posN xsN blN xN vN; entailer!.

Lemma body_load_node: semax_body Vprog Gprog f_load_node load_node_spec.
Proof.
  start_function.
  match goal with H: node_pre_props _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as HPRE;
    destruct H as (SH & Hbs & Hpos & Hlen & Hacap & Hbcap & Hal & Hbl & Hblok & Hnfns & Hentry & Hns & Hj) end.
  forward_call (nd).
  unfold node_val; cbn [n_tag n_op n_a n_b n_c n_d n_lit].
  forward_call (r, buf, shb, bs, pos, acap, bcap, v_tag, Tsh).
  Intros vret. destruct vret as [[[rc1 p1] tg] vt]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  forward. forward.
  assert (HPRE1 := npre_pos _ _ _ _ _ _ _ _ _ _ _ p1 HPRE ltac:(lia)).
  assert_PROP (field_compatible t_node [] nd) as FC by entailer!.
  assert (FCa: field_compatible t_node (DOT _a) nd) by auto with field_compatible.
  assert (FCb: field_compatible t_node (DOT _b) nd) by auto with field_compatible.
  set (z := Vint (Int.repr 0)).
  set (l0 := Vlong (Int64.repr 0)).
  forward. forward_if.
  { (* LIT *) subst tg.
    change (Vint (Int.repr 0), (z, (z, (z, (z, (z, l0)))))) with (node_val (mkN 0 0 0 0 0 0 0)).
    forward_call (r, buf, shb, bs, p1, acap, bcap, p, nfns, entry, fns, args, al, bytes, bl, nslots, j, nd).
    ret_loader. }
  forward. forward_if.
  { (* LOCAL *) subst tg.
    sep_apply (node_take_a Ews (Vint (Int.repr 1)) z z z z z l0 nd).
    forward_call (r, buf, shb, bs, p1, acap, bcap, nslots, field_address t_node [StructField _a] nd, Ews).
    { cancel. }
    Intros vret. destruct vret as [[[rc2 p2] x2] v2]. cbn [fst snd] in *.
    sep_apply (node_fold_a Ews (Vint (Int.repr 1)) z v2 z z z l0 nd).
    forward.
    Exists rc2 p2 (@nil Z) bl (mkN 1 0 x2 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_ok; auto; try lia.
    intros E. subst rc2. use_rc0. split; [ reflexivity | node_ok_tac ]. }
  forward. forward_if.
  { (* ASSIGN *) subst tg.
    sep_apply (node_take_a Ews (Vint (Int.repr 2)) z z z z z l0 nd).
    forward_call (r, buf, shb, bs, p1, acap, bcap, nslots, field_address t_node [StructField _a] nd, Ews).
    { cancel. }
    Intros vret. destruct vret as [[[rc2 p2] x2] v2]. cbn [fst snd] in *.
    sep_apply (node_fold_a Ews (Vint (Int.repr 2)) z v2 z z z l0 nd).
    forward_if.
    { forward. Exists rc2 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
      rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
    use_rc0.
    sep_apply (node_take_b Ews (Vint (Int.repr 2)) z (Vint (Int.repr x2)) z z z l0 nd).
    forward_call (r, buf, shb, bs, p2, acap, bcap, j, field_address t_node [StructField _b] nd, Ews).
    { cancel. }
    Intros vret. destruct vret as [[[rc3 p3] x3] v3]. cbn [fst snd] in *.
    sep_apply (node_fold_b Ews (Vint (Int.repr 2)) z (Vint (Int.repr x2)) v3 z z l0 nd).
    forward.
    Exists rc3 p3 (@nil Z) bl (mkN 2 0 x2 x3 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_ok; auto; try lia.
    intros E. subst rc3. use_rc0. split; [ reflexivity | node_ok_tac ]. }
  forward. forward_if.
  { (* SEQ *) subst tg.
    sep_apply (node_take_a Ews (Vint (Int.repr 3)) z z z z z l0 nd).
    forward_call (r, buf, shb, bs, p1, acap, bcap, j, field_address t_node [StructField _a] nd, Ews).
    { cancel. }
    Intros vret. destruct vret as [[[rc2 p2] x2] v2]. cbn [fst snd] in *.
    sep_apply (node_fold_a Ews (Vint (Int.repr 3)) z v2 z z z l0 nd).
    forward_if.
    { forward. Exists rc2 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
      rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
    use_rc0.
    sep_apply (node_take_b Ews (Vint (Int.repr 3)) z (Vint (Int.repr x2)) z z z l0 nd).
    forward_call (r, buf, shb, bs, p2, acap, bcap, j, field_address t_node [StructField _b] nd, Ews).
    { cancel. }
    Intros vret. destruct vret as [[[rc3 p3] x3] v3]. cbn [fst snd] in *.
    sep_apply (node_fold_b Ews (Vint (Int.repr 3)) z (Vint (Int.repr x2)) v3 z z l0 nd).
    forward.
    Exists rc3 p3 (@nil Z) bl (mkN 3 0 x2 x3 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_ok; auto; try lia.
    intros E. subst rc3. use_rc0. split; [ reflexivity | node_ok_tac ]. }
  forward. forward_if.
  { (* PRIM *) subst tg.
    change (Vint (Int.repr 4), (z, (z, (z, (z, (z, l0)))))) with (node_val (mkN 4 0 0 0 0 0 0)).
    forward_call (r, buf, shb, bs, p1, acap, bcap, p, nfns, entry, fns, args, al, bytes, bl, nslots, j, nd).
    ret_loader. }
  forward. forward_if.
  { (* CALL *) subst tg.
    change (Vint (Int.repr 5), (z, (z, (z, (z, (z, l0)))))) with (node_val (mkN 5 0 0 0 0 0 0)).
    forward_call (r, buf, shb, bs, p1, acap, bcap, p, nfns, entry, fns, args, al, bytes, bl, nslots, j, nd).
    ret_loader. }
  forward. forward_if.
  { (* ITE *) subst tg.
    change (Vint (Int.repr 6), (z, (z, (z, (z, (z, l0)))))) with (node_val (mkN 6 0 0 0 0 0 0)).
    forward_call (r, buf, shb, bs, p1, acap, bcap, p, nfns, entry, fns, args, al, bytes, bl, nslots, j, nd).
    ret_loader. }
  forward. forward_if.
  { (* FOR *) subst tg.
    change (Vint (Int.repr 7), (z, (z, (z, (z, (z, l0)))))) with (node_val (mkN 7 0 0 0 0 0 0)).
    forward_call (r, buf, shb, bs, p1, acap, bcap, p, nfns, entry, fns, args, al, bytes, bl, nslots, j, nd).
    ret_loader. }
  forward.
  forward_if (temp _t'13 (Vint (Int.repr (if Z.eq_dec tg 8 then 1 else if Z.eq_dec tg 10 then 1 else 0)))).
  { forward. entailer!. }
  { forward. forward. entailer!. destruct (Z.eq_dec tg 8); [ contradiction | ].
    destruct (Z.eq_dec tg 10), (zeq tg 10); try congruence; reflexivity. }
  forward_if (temp _t'14 (Vint (Int.repr (if Z.eq_dec tg 8 then 1 else if Z.eq_dec tg 10 then 1
                                          else if Z.eq_dec tg 11 then 1 else 0)))).
  { forward. entailer!. destruct (Z.eq_dec tg 8); [ reflexivity | ].
    destruct (Z.eq_dec tg 10); [ reflexivity | ]. exfalso. auto. }
  { forward. forward. entailer!.
    destruct (Z.eq_dec tg 8); [ discriminate | ]. destruct (Z.eq_dec tg 10); [ discriminate | ].
    destruct (Z.eq_dec tg 11), (zeq tg 11); try congruence; reflexivity. }
  forward_if.
  { (* LOOP, RET, PRINT *)
    assert (Htg: tg = 8 \/ tg = 10 \/ tg = 11).
    { destruct (Z.eq_dec tg 8); [ auto | ]. destruct (Z.eq_dec tg 10); [ auto | ].
      destruct (Z.eq_dec tg 11); [ auto | ]. exfalso. auto. }
    sep_apply (node_take_a Ews (Vint (Int.repr tg)) z z z z z l0 nd).
    forward_call (r, buf, shb, bs, p1, acap, bcap, j, field_address t_node [StructField _a] nd, Ews).
    { cancel. }
    Intros vret. destruct vret as [[[rc2 p2] x2] v2]. cbn [fst snd] in *.
    sep_apply (node_fold_a Ews (Vint (Int.repr tg)) z v2 z z z l0 nd).
    forward.
    Exists rc2 p2 (@nil Z) bl (mkN tg 0 x2 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_ok; auto; try lia.
    intros E. subst rc2. use_rc0. split; [ reflexivity | node_ok_tac ]. }
  assert (Htg: tg <> 8 /\ tg <> 10 /\ tg <> 11).
  { destruct (Z.eq_dec tg 8); [ discriminate | ]. destruct (Z.eq_dec tg 10); [ discriminate | ].
    destruct (Z.eq_dec tg 11); [ discriminate | ]. auto. }
  forward. forward_if.
  { (* BRK *) subst tg. forward.
    Exists 0 p1 (@nil Z) bl (mkN 9 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_ok; auto; try lia.
    intros _. split; [ reflexivity | node_ok_tac ]. }
  forward. forward_if.
  { (* HEAP *) subst tg.
    change (Vint (Int.repr 12), (z, (z, (z, (z, (z, l0)))))) with (node_val (mkN 12 0 0 0 0 0 0)).
    forward_call (r, buf, shb, bs, p1, acap, bcap, p, nfns, entry, fns, args, al, bytes, bl, nslots, j, nd).
    ret_loader. }
  forward.
  Exists 13 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
  rewrite app_nil_r. entailer!. apply npp_err; auto; lia.
Qed.
