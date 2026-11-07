(* Bodies of load_prim, load_call and load_heap, which read an argument list into the args pool (load_heap,
   for an isTag, also its tags into the bytes pool). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
Require Import OpenverseLoader.proof.Fields.
Require Import OpenverseLoader.proof.NodeLemmas.
#[local] Existing Instance Specs.CS.

Lemma body_load_call: semax_body Vprog Gprog f_load_call load_call_spec.
Proof.
  start_function. pre_props.
  unfold node_val; cbn [n_tag n_op n_a n_b n_c n_d n_lit].
  assert_PROP (field_compatible t_node [] nd) as FC by entailer!.
  assert (FCc: field_compatible t_node (DOT _c) nd) by auto with field_compatible.
  set (z := Vint (Int.repr 0)).
  set (l0 := Vlong (Int64.repr 0)).
  forward_call (r, buf, shb, bs, pos, acap, bcap, v_fn, Tsh).
  Intros vret. destruct vret as [[[rc1 p1] fn] vf]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  forward. forward.
  forward_if.
  { forward. Exists 11 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  forward_call (r, buf, shb, bs, p1, acap, bcap, v_n, Tsh).
  Intros vret. destruct vret as [[[rc2 p2] n] vn]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  forward. forward. forward. forward. forward.
  sep_apply (node_take_c Ews (Vint (Int.repr 5)) z (Vint (Int.repr fn)) (Vint (Int.repr n)) z z l0 nd).
  forward_call (r, buf, shb, bs, p2, acap, bcap, p, nfns, entry, fns, args, al, bytes, Zlength bl, j, n,
                field_address t_node [StructField _c] nd, Ews).
  { cancel. }
  Intros vret. destruct vret as [[[rc3 p3] xs] vc]. cbn [fst snd] in *.
  sep_apply (node_fold_c Ews (Vint (Int.repr 5)) z (Vint (Int.repr fn)) (Vint (Int.repr n)) vc z l0 nd).
  forward.
  Exists rc3 p3 xs bl (mkN 5 0 fn n (Zlength al) 0 0). ex_node nd.
  entailer!.
  unfold node_post_props. split; [ lia | ]. split; [ lia | ]. split; [ lia | ]. split; [ auto | ].
  split; [ lia | ]. split; [ auto | ].
  intros E. subst rc3.
  match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [Hxs Hvc]; clear H end.
  subst vc. split; [ reflexivity | ].
  node_ok_tac.
Qed.

Lemma body_load_prim: semax_body Vprog Gprog f_load_prim load_prim_spec.
Proof.
  start_function. pre_props.
  unfold node_val; cbn [n_tag n_op n_a n_b n_c n_d n_lit].
  assert_PROP (field_compatible t_node [] nd) as FC by entailer!.
  assert (FCc: field_compatible t_node (DOT _c) nd) by auto with field_compatible.
  set (z := Vint (Int.repr 0)).
  set (l0 := Vlong (Int64.repr 0)).
  forward_call (r, buf, shb, bs, pos, acap, bcap, v_code, Tsh).
  Intros vret. destruct vret as [[[rc1 p1] code] vco]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  forward.
  forward_if.
  { forward. Exists 14 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  forward_call (r, buf, shb, bs, p1, acap, bcap, v_k, Tsh).
  Intros vret. destruct vret as [[[rc2 p2] k] vk]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  forward.
  forward_if (temp _t'3 (Vint (Int.repr (if Z.eq_dec k 0 then 0 else if Z.eq_dec code 25 then 0 else 1)))).
  { forward. forward. entailer!. destruct (Z.eq_dec k 0); [ contradiction | ].
    destruct (zeq code 25), (Z.eq_dec code 25); try congruence; reflexivity. }
  { forward. entailer!. }
  forward_if.
  { forward. Exists 15 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  assert (Kok: k = 0 \/ code = 25).
  { destruct (Z.eq_dec k 0); [ left; auto | ]. destruct (Z.eq_dec code 25); [ right; auto | ].
    exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
  forward_call (r, buf, shb, bs, p2, acap, bcap, v_n, Tsh).
  Intros vret. destruct vret as [[[rc3 p3] n] vn]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p3 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  forward. forward. forward. forward. forward. forward. forward.
  sep_apply (node_take_c Ews (Vint (Int.repr 4)) (Vint (Int.repr code)) (Vint (Int.repr k)) (Vint (Int.repr n)) z z l0 nd).
  forward_call (r, buf, shb, bs, p3, acap, bcap, p, nfns, entry, fns, args, al, bytes, Zlength bl, j, n,
                field_address t_node [StructField _c] nd, Ews).
  { cancel. }
  Intros vret. destruct vret as [[[rc4 p4] xs] vc]. cbn [fst snd] in *.
  sep_apply (node_fold_c Ews (Vint (Int.repr 4)) (Vint (Int.repr code)) (Vint (Int.repr k)) (Vint (Int.repr n)) vc z l0 nd).
  forward.
  Exists rc4 p4 xs bl (mkN 4 code k n (Zlength al) 0 0). ex_node nd.
  entailer!.
  unfold node_post_props. split; [ lia | ]. split; [ lia | ]. split; [ lia | ]. split; [ auto | ].
  split; [ lia | ]. split; [ auto | ].
  intros E. subst rc4.
  match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [Hxs Hvc]; clear H end.
  subst vc. split; [ reflexivity | ].
  node_ok_tac.
Qed.

Lemma body_load_heap: semax_body Vprog Gprog f_load_heap load_heap_spec.
Proof.
  start_function. pre_props.
  unfold node_val; cbn [n_tag n_op n_a n_b n_c n_d n_lit].
  assert_PROP (field_compatible t_node [] nd) as FC by entailer!.
  assert (FCa: field_compatible t_node (DOT _a) nd) by auto with field_compatible.
  assert (FCc: field_compatible t_node (DOT _c) nd) by auto with field_compatible.
  forward_call (r, buf, shb, bs, pos, acap, bcap, v_op, Tsh).
  Intros vret. destruct vret as [[[rc1 p1] op] vo]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  forward.
  forward_if.
  { forward. Exists 21 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  forward_call (r, buf, shb, bs, p1, acap, bcap, v_k, Tsh).
  Intros vret. destruct vret as [[[rc2 p2] k] vk]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  forward. forward.
  forward.
  (* After the op-specific part: the field a (isTag: the offset of its tags), the field d (isTag: m) and
     the bytes pool. *)
  forward_if (EX bl1: list Z, EX a: Z, EX d: Z, EX pos1: Z,
    PROP (0 <= pos1 <= Zlength bs; Zlength bl <= Zlength bl1 <= bcap; bytes_ok bl1;
          0 <= a <= Int.max_unsigned; 0 <= d <= Int.max_unsigned; a = 0 \/ op <> 3;
          op = 4 -> d <= 4194304 /\ 4 * d <= Zlength bl1 /\ a <= Zlength bl1 - 4 * d)
    LOCAL (lvar _n tuint v_n; lvar _k tuint v_k; lvar _op tuint v_op; temp _r r; temp _p p;
           temp _j (Vint (Int.repr j)); temp _nd nd)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos1 acap bcap) r; buf_rep shb bs buf;
         data_at_ Tsh tuint v_op; data_at_ Tsh tuint v_k; data_at_ Tsh tuint v_n;
         data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl1)) p;
         args_pool args acap al; bytes_pool bytes bcap bl1;
         data_at Ews t_node (Vint (Int.repr 12), (Vint (Int.repr op), (Vint (Int.repr a),
           (Vint (Int.repr 0), (Vint (Int.repr 0), (Vint (Int.repr d), Vlong (Int64.repr 0))))))) nd))%assert.
  - (* ISTAG: m tags of 4 bytes into the bytes pool *)
    forward.
    forward_if.
    { forward. Exists 19 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
      rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
    rewrite ?shl_1_22 in *. simpl_ints.
    forward. forward.
    forward.
    sep_apply (node_take_a Ews (Vint (Int.repr 12)) (Vint (Int.repr op)) (Vint (Int.repr 0)) (Vint (Int.repr 0))
                 (Vint (Int.repr 0)) (Vint (Int.repr k)) (Vlong (Int64.repr 0)) nd).
    forward_call (r, buf, shb, bs, p2, acap, bcap, p, nfns, entry, fns, args, Zlength al, bytes, bl, 4 * k,
                  field_address t_node [StructField _a] nd, Ews).
    { cancel. }
    Intros vret. destruct vret as [[[rc3 p3] bl1] va]. cbn [fst snd] in *.
    sep_apply (node_fold_a Ews (Vint (Int.repr 12)) (Vint (Int.repr op)) va (Vint (Int.repr 0))
                 (Vint (Int.repr 0)) (Vint (Int.repr k)) (Vlong (Int64.repr 0)) nd).
    forward.
    forward_if.
    { forward. Exists rc3 p3 (@nil Z) bl1 (mkN 0 0 0 0 0 0 0). ex_node nd.
      rewrite app_nil_r. entailer!. apply npp_err_bl; auto; lia. }
    match goal with H: rc3 = 0 -> _ |- _ => destruct (H ltac:(lia)) as [Hbl1 ->]; clear H end.
    forward.
    Exists bl1 (Zlength bl) k p3. entailer!.
  - (* the other ops: k is the field a, and 0 for tag *)
    forward.
    forward_if (temp _t'4 (Vint (Int.repr (if Z.eq_dec k 0 then 0 else if Z.eq_dec op 3 then 1 else 0)))).
    { forward. forward. entailer!. destruct (Z.eq_dec k 0); [ contradiction | ].
      destruct (zeq op 3), (Z.eq_dec op 3); try congruence; reflexivity. }
    { forward. entailer!. }
    forward_if.
    { forward. Exists 15 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
      rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
    assert (Kok: k = 0 \/ op <> 3).
    { destruct (Z.eq_dec k 0); [ left; auto | ]. destruct (Z.eq_dec op 3); [ | right; auto ].
      exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
    forward. forward.
    Exists bl k 0 p2. entailer!.
  - Intros bl1 a d pos1.
    forward_call (r, buf, shb, bs, pos1, acap, bcap, v_n, Tsh).
    Intros vret. destruct vret as [[[rc4 p4] n] vn]. cbn [fst snd] in *.
    forward_if.
    { forward. Exists 1 p4 (@nil Z) bl1 (mkN 0 0 0 0 0 0 0). ex_node nd.
      rewrite app_nil_r. entailer!. apply npp_err_bl; auto; lia. }
    use_rc0.
    forward. forward. forward.
    sep_apply (node_take_c Ews (Vint (Int.repr 12)) (Vint (Int.repr op)) (Vint (Int.repr a)) (Vint (Int.repr n))
                 (Vint (Int.repr 0)) (Vint (Int.repr d)) (Vlong (Int64.repr 0)) nd).
    forward_call (r, buf, shb, bs, p4, acap, bcap, p, nfns, entry, fns, args, al, bytes, Zlength bl1, j, n,
                  field_address t_node [StructField _c] nd, Ews).
    { cancel. }
    Intros vret. destruct vret as [[[rc5 p5] xs] vc]. cbn [fst snd] in *.
    sep_apply (node_fold_c Ews (Vint (Int.repr 12)) (Vint (Int.repr op)) (Vint (Int.repr a)) (Vint (Int.repr n)) vc
                 (Vint (Int.repr d)) (Vlong (Int64.repr 0)) nd).
    forward.
    Exists rc5 p5 xs bl1 (mkN 12 op a n (Zlength al) d 0). ex_node nd.
    entailer!.
    unfold node_post_props. split; [ lia | ]. split; [ lia | ]. split; [ lia | ]. split; [ auto | ].
    split; [ lia | ]. split; [ auto | ].
    intros E. subst rc5.
    match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [Hxs Hvc]; clear H end.
    subst vc. split; [ reflexivity | ].
    node_ok_tac.
Qed.
