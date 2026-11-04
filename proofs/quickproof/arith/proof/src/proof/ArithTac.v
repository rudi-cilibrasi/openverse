(* ArithTac: tactics for the body proofs of arith.c and of the harness's helpers: Int64 values,
   comparisons and arithmetic on in-range operands, to Z.  No compspecs here. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseArith.proof.ArithZ.

Lemma in64_dec: forall z,
  (in64 z = true /\ MIN <= z <= MAX) \/ (in64 z = false /\ ~ (MIN <= z <= MAX)).
Proof.
  intros. destruct (in64 z) eqn:E; [ left; split; auto; apply in64_spec; auto | right; split; auto ].
  intro X. apply in64_spec in X. congruence.
Qed.

Ltac case64 z := let E := fresh "E" in let P := fresh "P" in
  destruct (in64_dec z) as [[E P] | [E P]]; rewrite ?E in *.

Lemma repr64_inj: forall x y, MIN <= x <= MAX -> MIN <= y <= MAX -> Int64.repr x = Int64.repr y -> x = y.
Proof. intros. apply (f_equal Int64.signed) in H1. rewrite !Int64.signed_repr in H1 by lia. auto. Qed.

(* Int64 comparisons and arithmetic on in-range values, to Z *)
Ltac simpl64 :=
  repeat match goal with
  | H: context [Int64.zero] |- _ => change Int64.zero with (Int64.repr 0) in H
  | H: context [Int64.mone] |- _ => change Int64.mone with (Int64.repr (-1)) in H
  | H: context [Int.signed (Int.repr 1)] |- _ => change (Int.signed (Int.repr 1)) with 1 in H
  | |- context [Int.signed (Int.repr 1)] => change (Int.signed (Int.repr 1)) with 1
  | H: context [Int.signed (Int.neg (Int.repr 1))] |- _ => change (Int.signed (Int.neg (Int.repr 1))) with (-1) in H
  | |- context [Int.signed (Int.neg (Int.repr 1))] => change (Int.signed (Int.neg (Int.repr 1))) with (-1)
  | |- context [Int64.sub (Int64.neg (Int64.repr 9223372036854775807)) (Int64.repr 1)] =>
      rewrite min_signed_expr
  | H: context [Int64.sub (Int64.neg (Int64.repr 9223372036854775807)) (Int64.repr 1)] |- _ =>
      rewrite min_signed_expr in H
  | H: Int64.eq (Int64.repr ?x) (Int64.repr ?y) = true |- _ =>
      rewrite (eq_repr x y) in H by rep_lia; apply Z.eqb_eq in H
  | H: Int64.eq (Int64.repr ?x) (Int64.repr ?y) = false |- _ =>
      rewrite (eq_repr x y) in H by rep_lia; apply Z.eqb_neq in H
  | H: Int64.lt (Int64.repr ?x) (Int64.repr ?y) = true |- _ =>
      rewrite (lt_repr x y) in H by rep_lia; apply Z.ltb_lt in H
  | H: Int64.lt (Int64.repr ?x) (Int64.repr ?y) = false |- _ =>
      rewrite (lt_repr x y) in H by rep_lia; apply Z.ltb_ge in H
  | H: Int64.repr ?x = Int64.repr ?y |- _ =>
      apply repr64_inj in H; [ | rep_lia | rep_lia ]
  | H: Int64.repr ?x <> Int64.repr ?y |- _ =>
      let N := fresh "N" in let E := fresh in
      assert (N: x <> y) by (intro E; apply H; rewrite E; reflexivity); clear H
  | |- context [9223372036854775807] => change 9223372036854775807 with MAX
  | H: context [9223372036854775807] |- _ => change 9223372036854775807 with MAX in H
  | |- context [Z.sub (Z.opp Int64.max_signed) 1] => change (Z.sub (Z.opp Int64.max_signed) 1) with MIN
  | H: context [Z.sub (Z.opp Int64.max_signed) 1] |- _ =>
      change (Z.sub (Z.opp Int64.max_signed) 1) with MIN in H
  | H: context [Int64.signed (Int64.repr ?x)] |- _ => rewrite (Int64.signed_repr x) in H by rep_lia
  | |- context [Int64.signed (Int64.repr ?x)] => rewrite (Int64.signed_repr x) by rep_lia
  | |- context [Int64.cmp Cgt ?x ?y] => change (Int64.cmp Cgt x y) with (Int64.lt y x)
  | |- context [Int64.cmp Clt ?x ?y] => change (Int64.cmp Clt x y) with (Int64.lt x y)
  | |- context [Int64.cmp Cge ?x ?y] => change (Int64.cmp Cge x y) with (negb (Int64.lt x y))
  | |- context [Int64.cmp Cle ?x ?y] => change (Int64.cmp Cle x y) with (negb (Int64.lt y x))
  | |- context [Int64.cmp Ceq ?x ?y] => change (Int64.cmp Ceq x y) with (Int64.eq x y)
  | |- context [Int64.cmp Cne ?x ?y] => change (Int64.cmp Cne x y) with (negb (Int64.eq x y))
  | |- context [Z.quot ?x ?y] =>
      lazymatch goal with
      | _: MIN <= Z.quot x y <= MAX |- _ => fail
      | _ => assert (MIN <= Z.quot x y <= MAX) by (apply quot_range; rep_lia)
      end
  | |- context [Z.rem ?x ?y] =>
      lazymatch goal with
      | _: MIN <= Z.rem x y <= MAX |- _ => fail
      | _ => assert (MIN <= Z.rem x y <= MAX) by (apply rem_range; rep_lia)
      end
  | H: context [Z.quot ?x ?y] |- _ =>
      lazymatch goal with
      | _: MIN <= Z.quot x y <= MAX |- _ => fail
      | _ => assert (MIN <= Z.quot x y <= MAX) by (apply quot_range; rep_lia)
      end
  | H: context [Int64.divs (Int64.repr ?x) (Int64.repr ?y)] |- _ => rewrite (divs_repr x y) in H by rep_lia
  | H: context [Int64.mods (Int64.repr ?x) (Int64.repr ?y)] |- _ => rewrite (mods_repr x y) in H by rep_lia
  | |- context [Int64.lt (Int64.repr ?x) (Int64.repr ?y)] => rewrite (lt_repr x y) by rep_lia
  | |- context [Int64.eq (Int64.repr ?x) (Int64.repr ?y)] => rewrite (eq_repr x y) by rep_lia
  | |- context [Int64.divs (Int64.repr ?x) (Int64.repr ?y)] => rewrite (divs_repr x y) by rep_lia
  | |- context [Int64.mods (Int64.repr ?x) (Int64.repr ?y)] => rewrite (mods_repr x y) by rep_lia
  | |- context [Int64.add (Int64.repr ?x) (Int64.repr ?y)] => rewrite (add64_repr x y)
  | |- context [Int64.sub (Int64.repr ?x) (Int64.repr ?y)] => rewrite (sub64_repr x y)
  | |- context [Int64.mul (Int64.repr ?x) (Int64.repr ?y)] => rewrite (mul64_repr x y)
  | |- context [Int64.neg (Int64.repr ?x)] => rewrite (neg64_repr x)
  end.

Lemma div_tc: forall x y, MIN <= x <= MAX -> MIN <= y <= MAX -> y <> 0 -> ~ (x = MIN /\ y = -1) ->
  Int64.repr y <> Int64.zero /\ ~ (Int64.repr x = Int64.repr MIN /\ Int64.repr y = Int64.mone).
Proof.
  intros x y Hx Hy H0 H1. split.
  - intro E. apply (f_equal Int64.signed) in E. rewrite Int64.signed_repr in E by lia. apply H0. exact E.
  - intros [E1 E2]. apply (f_equal Int64.signed) in E1, E2. rewrite !Int64.signed_repr in E1 by rep_lia.
    rewrite Int64.signed_repr in E2 by lia. apply H1. split; auto.
Qed.

Ltac tc_div := entailer!; simpl64; apply div_tc; rep_lia.

(* The branches of `if (c)` where the join set c to an int that is zero or not *)
Ltac int_contra :=
  exfalso;
  match goal with
  | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
  | H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H
  | H: false = true |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  end.

(* Case on every boolean test of the goal, and close each case *)
Ltac zcases :=
  unfold st_of, out_of, div_st, div_out, floor_adj_b, ceil_adj_b in *;
  repeat match goal with
  | |- context [in64 ?z] => case64 z
  | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
  | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
  | |- context [zlt ?x ?y] => destruct (zlt x y)
  | |- context [zeq ?x ?y] => destruct (zeq x y)
  end;
  simpl; first [ reflexivity | exfalso; rep_lia | idtac ].

