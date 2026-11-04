(* ArithBasic: the bodies of vx_add, vx_sub, vx_mul, vx_neg and vx_abs. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseArith.arith.code.
Require Import OpenverseArith.proof.ArithZ OpenverseArith.proof.ArithTac.
Require Import OpenverseArith.proof.ArithSpecs.
#[export] Existing Instance ArithSpecs.CS.

Lemma body_vx_add: semax_body Vprog Gprog f_vx_add vx_add_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if in64 (a + b) then 0 else 1)));
                             temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)); temp _out out)
              SEP (data_at sh tlong v out)).
  - simpl64. forward. entailer!. simpl64. zcases.
  - simpl64. forward. entailer!. simpl64. zcases.
  - forward_if.
    + forward. case64 (a + b); [ lia | ]. unfold st_of, out_of. rewrite E. entailer!.
    + case64 (a + b); [ | exfalso; apply Int.one_not_zero; auto ].
      forward. forward. unfold st_of, out_of. rewrite E. simpl64. entailer!.
Qed.

Lemma body_vx_sub: semax_body Vprog Gprog f_vx_sub vx_sub_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if in64 (a - b) then 0 else 1)));
                             temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)); temp _out out)
              SEP (data_at sh tlong v out)).
  - simpl64. forward. entailer!. simpl64. zcases.
  - simpl64. forward. entailer!. simpl64. zcases.
  - forward_if.
    + forward. case64 (a - b); [ lia | ]. unfold st_of, out_of. rewrite E. entailer!.
    + case64 (a - b); [ | exfalso; apply Int.one_not_zero; auto ].
      forward. forward. unfold st_of, out_of. rewrite E. simpl64. entailer!.
Qed.

Lemma body_vx_mul: semax_body Vprog Gprog f_vx_mul vx_mul_spec.
Proof.
  start_function.
  forward.
  forward_if (PROP () LOCAL (temp _ovf (Vint (Int.repr (if in64 (a * b) then 0 else 1)));
                             temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)); temp _out out)
              SEP (data_at sh tlong v out)).
  - simpl64. forward_if.
    + simpl64. forward. { tc_div. } entailer!. simpl64. pose proof (mul_ovf_pp a b H1 H2). zcases.
    + simpl64. forward. { tc_div. } entailer!. simpl64. pose proof (mul_ovf_pn a b H1 ltac:(lia)). zcases.
  - simpl64. forward_if.
    + simpl64. forward_if.
      * simpl64. forward. { tc_div. } entailer!. simpl64. pose proof (mul_ovf_np a b H2 H3). zcases.
      * simpl64. forward_if.
        -- simpl64. forward. { tc_div. } entailer!. simpl64. pose proof (mul_ovf_nn a b H2 H4). zcases.
        -- simpl64. forward. entailer!. replace b with 0 by lia. rewrite Z.mul_0_r. reflexivity.
    + simpl64. forward. entailer!. replace a with 0 by lia. reflexivity.
  - forward_if.
    + forward. case64 (a * b); [ lia | ]. unfold st_of, out_of. rewrite E. entailer!.
    + case64 (a * b); [ | exfalso; apply Int.one_not_zero; auto ].
      forward. forward. unfold st_of, out_of. rewrite E. simpl64. entailer!.
Qed.

Lemma body_vx_neg: semax_body Vprog Gprog f_vx_neg vx_neg_spec.
Proof.
  start_function.
  forward_if.
  - simpl64. subst a. forward.
  - simpl64. forward.
    { entailer!. rewrite Int64.signed_zero. rep_lia. }
    forward. unfold st_of, out_of. rewrite in64_true by rep_lia. entailer!.
    simpl. rewrite neg64_repr. apply derives_refl.
Qed.

Lemma body_vx_abs: semax_body Vprog Gprog f_vx_abs vx_abs_spec.
Proof.
  start_function.
  forward_if.
  - simpl64. forward_call (a, out, sh, v). forward. rewrite Z.abs_neq by lia. entailer!.
  - simpl64. forward. forward. unfold st_of, out_of. rewrite Z.abs_eq by lia. rewrite in64_true by rep_lia.
    entailer!.
Qed.
