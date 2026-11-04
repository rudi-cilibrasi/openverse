(* Helpers: the specifications and body proofs of the harness's static helpers (harness/arith_exact.c):
   add_fits, sub_fits and mul_fits return whether a + b, a - b, a * b fit in int64_t, and c_floordiv,
   c_ceildiv, c_quotient and c_modulo return the floor, ceiling, Euclidean quotient and Euclidean
   remainder of a / b, for b <> 0 and (a, b) <> (INT64_MIN, -1). *)
Require Import VST.floyd.proofauto.
Require Import OpenverseArith.harness.arith_exact.code.
Require Import OpenverseArith.proof.ArithZ OpenverseArith.proof.ArithTac.

#[export] Instance CS : compspecs. make_compspecs OpenverseArith.harness.arith_exact.code.prog. Defined.
Definition Vprog : varspecs. mk_varspecs OpenverseArith.harness.arith_exact.code.prog. Defined.

Definition add_fits_spec :=
  DECLARE _add_fits
  WITH a: Z, b: Z
  PRE [ tlong, tlong ]
    PROP (MIN <= a <= MAX; MIN <= b <= MAX)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (Z.b2z (in64 (a + b))))) SEP ().

Definition sub_fits_spec :=
  DECLARE _sub_fits
  WITH a: Z, b: Z
  PRE [ tlong, tlong ]
    PROP (MIN <= a <= MAX; MIN <= b <= MAX)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (Z.b2z (in64 (a - b))))) SEP ().

Definition mul_fits_spec :=
  DECLARE _mul_fits
  WITH a: Z, b: Z
  PRE [ tlong, tlong ]
    PROP (MIN <= a <= MAX; MIN <= b <= MAX)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (Z.b2z (in64 (a * b))))) SEP ().

Definition c_floordiv_spec :=
  DECLARE _c_floordiv
  WITH a: Z, b: Z
  PRE [ tlong, tlong ]
    PROP (MIN <= a <= MAX; MIN <= b <= MAX; b <> 0; ~ (a = MIN /\ b = -1))
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP ()
  POST [ tlong ]
    PROP () RETURN (Vlong (Int64.repr (a / b))) SEP ().

Definition c_ceildiv_spec :=
  DECLARE _c_ceildiv
  WITH a: Z, b: Z
  PRE [ tlong, tlong ]
    PROP (MIN <= a <= MAX; MIN <= b <= MAX; b <> 0; ~ (a = MIN /\ b = -1))
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP ()
  POST [ tlong ]
    PROP () RETURN (Vlong (Int64.repr (ceildiv a b))) SEP ().

Definition c_quotient_spec :=
  DECLARE _c_quotient
  WITH a: Z, b: Z
  PRE [ tlong, tlong ]
    PROP (MIN <= a <= MAX; MIN <= b <= MAX; b <> 0; ~ (a = MIN /\ b = -1))
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP ()
  POST [ tlong ]
    PROP () RETURN (Vlong (Int64.repr (ediv a b))) SEP ().

Definition c_modulo_spec :=
  DECLARE _c_modulo
  WITH a: Z, b: Z
  PRE [ tlong, tlong ]
    PROP (MIN <= a <= MAX; MIN <= b <= MAX; b <> 0; ~ (a = MIN /\ b = -1))
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP ()
  POST [ tlong ]
    PROP () RETURN (Vlong (Int64.repr (emod a b))) SEP ().

Definition Gprog : funspecs := [].

Lemma body_add_fits: semax_body Vprog Gprog f_add_fits add_fits_spec.
Proof.
  start_function.
  forward_if.
  - simpl64. forward. entailer!. simpl64. zcases.
  - simpl64. forward. entailer!. simpl64. zcases.
Qed.

Lemma body_sub_fits: semax_body Vprog Gprog f_sub_fits sub_fits_spec.
Proof.
  start_function.
  forward_if.
  - simpl64. forward. entailer!. simpl64. zcases.
  - simpl64. forward. entailer!. simpl64. zcases.
Qed.

Lemma body_mul_fits: semax_body Vprog Gprog f_mul_fits mul_fits_spec.
Proof.
  start_function.
  forward_if.
  - simpl64. subst b. forward. rewrite Z.mul_0_r. entailer!.
  - simpl64. forward_if.
    + simpl64. subst b. forward. entailer!. simpl64. pose proof (mul_fits_m1 a H). zcases.
    + simpl64. forward_if.
      * simpl64. pose proof (mul_fits_pos a b ltac:(lia)).
        forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (Z.b2z (in64 (a * b)))));
                                   temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b))) SEP ()).
        -- tc_div.
        -- simpl64. forward. { tc_div. } entailer!. simpl64. zcases.
        -- simpl64. forward. entailer!. simpl64. zcases.
        -- forward.
      * simpl64. pose proof (mul_fits_neg a b ltac:(lia)).
        forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr (Z.b2z (in64 (a * b)))));
                                   temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b))) SEP ()).
        -- tc_div.
        -- simpl64. forward. { tc_div. } entailer!. simpl64. zcases.
        -- simpl64. forward. entailer!. simpl64. zcases.
        -- forward.
Qed.

Lemma body_c_floordiv: semax_body Vprog Gprog f_c_floordiv c_floordiv_spec.
Proof.
  start_function.
  forward. { tc_div. } forward. { tc_div. } simpl64.
  forward_if (PROP ()
              LOCAL (temp _t'1 (Vint (Int.repr (Z.b2z (floor_adj_b a b))));
                     temp _r (Vlong (Int64.repr (Z.rem a b))); temp _q (Vlong (Int64.repr (Z.quot a b)));
                     temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)))
              SEP ()).
  - simpl64. forward. entailer!. simpl64. zcases.
  - simpl64. forward. entailer!. simpl64. zcases.
  - forward_if.
    + destruct (floor_adj_b a b) eqn:F; [ | int_contra ].
      destruct (floor_adj_true a b H H1 F) as [E S].
      forward.
    + destruct (floor_adj_b a b) eqn:F; [ int_contra | ].
      pose proof (floor_adj_false a b H1 F) as E. forward.
Qed.

Lemma body_c_ceildiv: semax_body Vprog Gprog f_c_ceildiv c_ceildiv_spec.
Proof.
  start_function.
  forward. { tc_div. } forward. { tc_div. } simpl64.
  forward_if (PROP ()
              LOCAL (temp _t'1 (Vint (Int.repr (Z.b2z (ceil_adj_b a b))));
                     temp _r (Vlong (Int64.repr (Z.rem a b))); temp _q (Vlong (Int64.repr (Z.quot a b)));
                     temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)))
              SEP ()).
  - simpl64. forward. entailer!. simpl64. zcases.
  - simpl64. forward. entailer!. simpl64. zcases.
  - forward_if.
    + destruct (ceil_adj_b a b) eqn:F; [ | int_contra ].
      destruct (ceil_adj_true a b H H1 F) as [E S].
      forward.
    + destruct (ceil_adj_b a b) eqn:F; [ int_contra | ].
      pose proof (ceil_adj_false a b H1 F) as E. forward.
Qed.

Lemma body_c_quotient: semax_body Vprog Gprog f_c_quotient c_quotient_spec.
Proof.
  start_function.
  forward. { tc_div. } forward. { tc_div. } simpl64.
  forward_if.
  - simpl64. pose proof (quot_small a b H H1 ltac:(lia)).
    forward_if.
    + simpl64. forward. entailer!. rewrite ediv_neg_pos by lia. reflexivity.
    + simpl64. forward. entailer!. rewrite ediv_neg_neg by lia. reflexivity.
  - simpl64. forward. entailer!. rewrite ediv_nonneg by lia. reflexivity.
Qed.

Lemma body_c_modulo: semax_body Vprog Gprog f_c_modulo c_modulo_spec.
Proof.
  start_function.
  forward. { tc_div. } simpl64.
  pose proof (Z.rem_bound_abs a b H1).
  forward_if.
  - simpl64. forward_if.
    + simpl64. forward. entailer!. rewrite emod_neg_pos by lia. reflexivity.
    + simpl64. forward. entailer!. rewrite emod_neg_neg by lia. reflexivity.
  - simpl64. forward. entailer!. rewrite emod_nonneg by lia. reflexivity.
Qed.
