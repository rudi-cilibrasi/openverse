(* ArithDiv: the bodies of vx_floordiv, vx_ceildiv, vx_quotient and vx_modulo. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseArith.arith.code.
Require Import OpenverseArith.proof.ArithZ OpenverseArith.proof.ArithTac.
Require Import OpenverseArith.proof.ArithSpecs.
#[export] Existing Instance ArithSpecs.CS.

Lemma body_vx_floordiv: semax_body Vprog Gprog f_vx_floordiv vx_floordiv_spec.
Proof.
  start_function.
  forward_if.
  - simpl64. subst b. forward.
  - simpl64. forward_if.
    + simpl64. subst b. forward_call (a, out, sh, v). forward. rewrite div_m1. entailer!.
    + simpl64. forward. { tc_div. } forward. { tc_div. } simpl64.
      forward_if (PROP ()
                  LOCAL (temp _t'2 (Vint (Int.repr (Z.b2z (floor_adj_b a b))));
                         temp _r (Vlong (Int64.repr (Z.rem a b))); temp _q (Vlong (Int64.repr (Z.quot a b)));
                         temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)); temp _out out)
                  SEP (data_at sh tlong v out)).
      * simpl64. forward. entailer!. simpl64. zcases.
      * simpl64. forward. entailer!. simpl64. zcases.
      * forward_if (PROP ()
                    LOCAL (temp _q (Vlong (Int64.repr (a / b)));
                           temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)); temp _out out)
                    SEP (data_at sh tlong v out)).
        -- destruct (floor_adj_b a b) eqn:F; [ | int_contra ].
           destruct (floor_adj_true a b H N F) as [E S].
           forward. entailer!. rewrite E. reflexivity.
        -- destruct (floor_adj_b a b) eqn:F; [ int_contra | ].
           forward. entailer!. rewrite (floor_adj_false a b N F). reflexivity.
        -- pose proof (div_fits a b H H0 N ltac:(lia)).
           forward. forward. unfold div_st, div_out, st_of, out_of.
           rewrite (proj2 (Z.eqb_neq b 0) N), in64_true by auto. entailer!.
Qed.

Lemma body_vx_ceildiv: semax_body Vprog Gprog f_vx_ceildiv vx_ceildiv_spec.
Proof.
  start_function.
  forward_if.
  - simpl64. subst b. forward.
  - simpl64. forward_if.
    + simpl64. subst b. forward_call (a, out, sh, v). forward. rewrite ceildiv_m1. entailer!.
    + simpl64. forward. { tc_div. } forward. { tc_div. } simpl64.
      forward_if (PROP ()
                  LOCAL (temp _t'2 (Vint (Int.repr (Z.b2z (ceil_adj_b a b))));
                         temp _r (Vlong (Int64.repr (Z.rem a b))); temp _q (Vlong (Int64.repr (Z.quot a b)));
                         temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)); temp _out out)
                  SEP (data_at sh tlong v out)).
      * simpl64. forward. entailer!. simpl64. zcases.
      * simpl64. forward. entailer!. simpl64. zcases.
      * forward_if (PROP ()
                    LOCAL (temp _q (Vlong (Int64.repr (ceildiv a b)));
                           temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)); temp _out out)
                    SEP (data_at sh tlong v out)).
        -- destruct (ceil_adj_b a b) eqn:F; [ | int_contra ].
           destruct (ceil_adj_true a b H N F) as [E S].
           forward. entailer!. rewrite E. reflexivity.
        -- destruct (ceil_adj_b a b) eqn:F; [ int_contra | ].
           forward. entailer!. rewrite (ceil_adj_false a b N F). reflexivity.
        -- pose proof (ceildiv_fits a b H H0 N ltac:(lia)).
           forward. forward. unfold div_st, div_out, st_of, out_of.
           rewrite (proj2 (Z.eqb_neq b 0) N), in64_true by auto. entailer!.
Qed.

Lemma body_vx_quotient: semax_body Vprog Gprog f_vx_quotient vx_quotient_spec.
Proof.
  start_function.
  forward_if.
  - simpl64. subst b. forward.
  - simpl64. forward_if.
    + simpl64. subst b. forward_call (a, out, sh, v). forward. rewrite ediv_m1. entailer!.
    + simpl64. forward. { tc_div. } forward. { tc_div. } simpl64.
      forward_if (PROP ()
                  LOCAL (temp _q (Vlong (Int64.repr (ediv a b)));
                         temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)); temp _out out)
                  SEP (data_at sh tlong v out)).
      * simpl64. pose proof (quot_small a b H N ltac:(lia)).
        forward_if.
        -- simpl64. forward. entailer!. rewrite ediv_neg_pos by lia. reflexivity.
        -- simpl64. forward. entailer!. rewrite ediv_neg_neg by lia. reflexivity.
      * simpl64. forward. entailer!. rewrite ediv_nonneg by lia. reflexivity.
      * pose proof (ediv_fits a b H H0 N ltac:(lia)).
        forward. forward. unfold div_st, div_out, st_of, out_of.
        rewrite (proj2 (Z.eqb_neq b 0) N), in64_true by auto. entailer!.
Qed.

Lemma body_vx_modulo: semax_body Vprog Gprog f_vx_modulo vx_modulo_spec.
Proof.
  start_function.
  forward_if.
  - simpl64. subst b. forward.
  - simpl64. forward_if.
    + simpl64. subst b. forward. forward. rewrite emod_m1. entailer!.
    + simpl64. forward. { tc_div. } simpl64.
      pose proof (Z.rem_bound_abs a b N).
      forward_if (PROP ()
                  LOCAL (temp _r (Vlong (Int64.repr (emod a b)));
                         temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b)); temp _out out)
                  SEP (data_at sh tlong v out)).
      * simpl64. forward_if.
        -- simpl64. forward. entailer!. rewrite emod_neg_pos by lia. reflexivity.
        -- simpl64. forward. entailer!. rewrite emod_neg_neg by lia. reflexivity.
      * simpl64. forward. entailer!. rewrite emod_nonneg by lia. reflexivity.
      * forward. forward. rewrite (proj2 (Z.eqb_neq b 0) N). entailer!.
Qed.
