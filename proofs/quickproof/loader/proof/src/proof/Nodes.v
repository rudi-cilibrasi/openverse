(* Bodies of node_clear and the node loaders. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
Require Import OpenverseLoader.proof.Fields.
Require Import OpenverseLoader.proof.NodeLemmas.
#[local] Existing Instance Specs.CS.

Lemma body_node_clear: semax_body Vprog Gprog f_node_clear node_clear_spec.
Proof.
  start_function.
  repeat forward.
  entailer!.
Qed.

Lemma body_load_three: semax_body Vprog Gprog f_load_three load_three_spec.
Proof.
  start_function. pre_props.
  unfold node_val; cbn [n_tag n_op n_a n_b n_c n_d n_lit].
  assert_PROP (field_compatible t_node [] nd) as FC by entailer!.
  assert (FCa: field_compatible t_node (DOT _a) nd) by auto with field_compatible.
  assert (FCb: field_compatible t_node (DOT _b) nd) by auto with field_compatible.
  assert (FCc: field_compatible t_node (DOT _c) nd) by auto with field_compatible.
  set (z := Vint (Int.repr 0)).
  sep_apply (node_take_a Ews (Vint (Int.repr 6)) z z z z z (Vlong (Int64.repr 0)) nd).
  forward_call (r, buf, shb, bs, pos, acap, bcap, j, field_address t_node [StructField _a] nd, Ews).
  { cancel. }
  Intros vret. destruct vret as [[[rc1 p1] x1] v1]. cbn [fst snd] in *.
  sep_apply (node_fold_a Ews (Vint (Int.repr 6)) z v1 z z z (Vlong (Int64.repr 0)) nd).
  forward_if.
  { forward. Exists rc1 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  sep_apply (node_take_b Ews (Vint (Int.repr 6)) z (Vint (Int.repr x1)) z z z (Vlong (Int64.repr 0)) nd).
  forward_call (r, buf, shb, bs, p1, acap, bcap, j, field_address t_node [StructField _b] nd, Ews).
  { cancel. }
  Intros vret. destruct vret as [[[rc2 p2] x2] v2]. cbn [fst snd] in *.
  sep_apply (node_fold_b Ews (Vint (Int.repr 6)) z (Vint (Int.repr x1)) v2 z z (Vlong (Int64.repr 0)) nd).
  forward_if.
  { forward. Exists rc2 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  sep_apply (node_take_c Ews (Vint (Int.repr 6)) z (Vint (Int.repr x1)) (Vint (Int.repr x2)) z z (Vlong (Int64.repr 0)) nd).
  forward_call (r, buf, shb, bs, p2, acap, bcap, j, field_address t_node [StructField _c] nd, Ews).
  { cancel. }
  Intros vret. destruct vret as [[[rc3 p3] x3] v3]. cbn [fst snd] in *.
  sep_apply (node_fold_c Ews (Vint (Int.repr 6)) z (Vint (Int.repr x1)) (Vint (Int.repr x2)) v3 z (Vlong (Int64.repr 0)) nd).
  forward.
  Exists rc3 p3 (@nil Z) bl (mkN 6 0 x1 x2 x3 0 0). ex_node nd.
  rewrite app_nil_r. entailer!. apply npp_ok; auto; try lia.
  intros E. subst rc3. use_rc0. split; [ reflexivity | node_ok_tac ].
Qed.

Lemma body_load_for: semax_body Vprog Gprog f_load_for load_for_spec.
Proof.
  start_function. pre_props.
  unfold node_val; cbn [n_tag n_op n_a n_b n_c n_d n_lit].
  assert_PROP (field_compatible t_node [] nd) as FC by entailer!.
  assert (FCa: field_compatible t_node (DOT _a) nd) by auto with field_compatible.
  assert (FCb: field_compatible t_node (DOT _b) nd) by auto with field_compatible.
  assert (FCc: field_compatible t_node (DOT _c) nd) by auto with field_compatible.
  assert (FCd: field_compatible t_node (DOT _d) nd) by auto with field_compatible.
  set (z := Vint (Int.repr 0)).
  set (t := Vint (Int.repr 7)).
  set (l0 := Vlong (Int64.repr 0)).
  sep_apply (node_take_a Ews t z z z z z l0 nd).
  forward_call (r, buf, shb, bs, pos, acap, bcap, nslots, field_address t_node [StructField _a] nd, Ews).
  { cancel. }
  Intros vret. destruct vret as [[[rc1 p1] x1] v1]. cbn [fst snd] in *.
  sep_apply (node_fold_a Ews t z v1 z z z l0 nd).
  forward_if.
  { forward. Exists rc1 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  sep_apply (node_take_b Ews t z (Vint (Int.repr x1)) z z z l0 nd).
  forward_call (r, buf, shb, bs, p1, acap, bcap, j, field_address t_node [StructField _b] nd, Ews).
  { cancel. }
  Intros vret. destruct vret as [[[rc2 p2] x2] v2]. cbn [fst snd] in *.
  sep_apply (node_fold_b Ews t z (Vint (Int.repr x1)) v2 z z l0 nd).
  forward_if.
  { forward. Exists rc2 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  sep_apply (node_take_c Ews t z (Vint (Int.repr x1)) (Vint (Int.repr x2)) z z l0 nd).
  forward_call (r, buf, shb, bs, p2, acap, bcap, j, field_address t_node [StructField _c] nd, Ews).
  { cancel. }
  Intros vret. destruct vret as [[[rc3 p3] x3] v3]. cbn [fst snd] in *.
  sep_apply (node_fold_c Ews t z (Vint (Int.repr x1)) (Vint (Int.repr x2)) v3 z l0 nd).
  forward_if.
  { forward. Exists rc3 p3 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  sep_apply (node_take_d Ews t z (Vint (Int.repr x1)) (Vint (Int.repr x2)) (Vint (Int.repr x3)) z l0 nd).
  forward_call (r, buf, shb, bs, p3, acap, bcap, j, field_address t_node [StructField _d] nd, Ews).
  { cancel. }
  Intros vret. destruct vret as [[[rc4 p4] x4] v4]. cbn [fst snd] in *.
  sep_apply (node_fold_d Ews t z (Vint (Int.repr x1)) (Vint (Int.repr x2)) (Vint (Int.repr x3)) v4 l0 nd).
  forward.
  Exists rc4 p4 (@nil Z) bl (mkN 7 0 x1 x2 x3 x4 0). ex_node nd.
  rewrite app_nil_r. entailer!. apply npp_ok; auto; try lia.
  intros E. subst rc4. use_rc0. split; [ reflexivity | node_ok_tac ].
Qed.
