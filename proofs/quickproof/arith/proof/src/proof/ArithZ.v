(* ArithZ: the mathematics of the int operations of runtime/src/arith.c, in Z.

   - in64 z: z is a value of int64_t (Res.ofInt does not overflow).
   - The four divisions, for b <> 0: Z.div (floor), ceildiv (ceiling), ediv and emod (Euclidean,
     0 <= emod a b < |b|), and how C's truncating / and % (Z.quot and Z.rem) compute them.
   - The overflow tests of vx_mul and of the harness's mul_fits, both equivalent to in64 (a * b).
   - The ranges that show no intermediate C expression overflows.
   - Int64 bridges: CompCert's divs, mods, lt and eq on in-range values. *)
Require Import VST.floyd.proofauto.

Open Scope Z_scope.

Notation MIN := Int64.min_signed.
Notation MAX := Int64.max_signed.

Definition in64 (z: Z) : bool := (MIN <=? z) && (z <=? MAX).

Lemma in64_spec: forall z, in64 z = true <-> MIN <= z <= MAX.
Proof. intros. unfold in64. rewrite andb_true_iff, !Z.leb_le. tauto. Qed.

Lemma in64_true: forall z, MIN <= z <= MAX -> in64 z = true.
Proof. intros. apply in64_spec; auto. Qed.

Lemma in64_false: forall z, ~ (MIN <= z <= MAX) -> in64 z = false.
Proof. intros. destruct (in64 z) eqn:E; auto. apply in64_spec in E. contradiction. Qed.

(* The return codes of openverse.h *)
Definition VX_OK := 0.
Definition VX_FAIL := 1.
Definition VX_OVERFLOW := 2.

(* Res.ofInt z: VX_OK and z when z fits in int64_t, else VX_OVERFLOW and *out unchanged *)
Definition st_of (z: Z) : Z := if in64 z then VX_OK else VX_OVERFLOW.
Definition out_of (z: Z) (v: val) : val := if in64 z then Vlong (Int64.repr z) else v.

(* if b = 0 then fail else Res.ofInt z *)
Definition div_st (b z: Z) : Z := if b =? 0 then VX_FAIL else st_of z.
Definition div_out (b z: Z) (v: val) : val := if b =? 0 then v else out_of z v.

Lemma st_of_ok: forall z, MIN <= z <= MAX -> st_of z = VX_OK.
Proof. intros. unfold st_of. rewrite in64_true; auto. Qed.
Lemma out_of_ok: forall z v, MIN <= z <= MAX -> out_of z v = Vlong (Int64.repr z).
Proof. intros. unfold out_of. rewrite in64_true; auto. Qed.
Lemma st_of_ovf: forall z, ~ (MIN <= z <= MAX) -> st_of z = VX_OVERFLOW.
Proof. intros. unfold st_of. rewrite in64_false; auto. Qed.
Lemma out_of_ovf: forall z v, ~ (MIN <= z <= MAX) -> out_of z v = v.
Proof. intros. unfold out_of. rewrite in64_false; auto. Qed.
Lemma div_st_zero: forall z, div_st 0 z = VX_FAIL.
Proof. reflexivity. Qed.
Lemma div_out_zero: forall z v, div_out 0 z v = v.
Proof. reflexivity. Qed.
Lemma div_st_nz: forall b z, b <> 0 -> div_st b z = st_of z.
Proof. intros. unfold div_st. rewrite (proj2 (Z.eqb_neq b 0) H). reflexivity. Qed.
Lemma div_out_nz: forall b z v, b <> 0 -> div_out b z v = out_of z v.
Proof. intros. unfold div_out. rewrite (proj2 (Z.eqb_neq b 0) H). reflexivity. Qed.

(* The ceiling and the Euclidean quotient and remainder (Lean's Int.ediv / Int.emod for b <> 0). *)
Definition ceildiv (a b: Z) : Z := - ((- a) / b).
Definition ediv (a b: Z) : Z := Z.sgn b * (a / Z.abs b).
Definition emod (a b: Z) : Z := a mod Z.abs b.

Lemma ceildiv_spec: forall a b, 0 < b -> b * (ceildiv a b - 1) < a <= b * ceildiv a b.
Proof.
  intros. unfold ceildiv.
  pose proof (Z.div_mod (- a) b ltac:(lia)). pose proof (Z.mod_pos_bound (- a) b H). nia.
Qed.

Lemma ediv_emod_spec: forall a b, b <> 0 ->
  a = b * ediv a b + emod a b /\ 0 <= emod a b < Z.abs b.
Proof.
  intros. unfold ediv, emod.
  pose proof (Z.div_mod a (Z.abs b) ltac:(lia)). pose proof (Z.mod_pos_bound a (Z.abs b) ltac:(lia)).
  split; [ | lia ].
  destruct (Z.ltb_spec 0 b).
  - rewrite Z.sgn_pos, Z.abs_eq in * by lia. lia.
  - rewrite Z.sgn_neg, Z.abs_neq in * by lia. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* Truncating division                                                    *)
(* ---------------------------------------------------------------------- *)

Ltac quot_facts a b :=
  let Hb := fresh in
  assert (Hb: b <> 0) by lia;
  pose proof (Z.quot_rem' a b);
  pose proof (Z.rem_bound_abs a b Hb);
  pose proof (Z.rem_nonneg a b Hb);
  pose proof (Z.rem_nonpos a b Hb).

(* A nonzero remainder means |b| >= 2. *)
Lemma rem_nonzero_b: forall a b, b <> 0 -> Z.rem a b <> 0 -> 2 <= Z.abs b.
Proof. intros. pose proof (Z.rem_bound_abs a b H). lia. Qed.

Lemma rem_m1: forall a, Z.rem a (-1) = 0.
Proof. intros. pose proof (Z.rem_bound_abs a (-1) ltac:(lia)). lia. Qed.

Lemma quot_m1: forall a, Z.quot a (-1) = - a.
Proof. intros. pose proof (Z.quot_rem' a (-1)). rewrite rem_m1 in H. lia. Qed.

Lemma quot_range: forall a b,
  MIN <= a <= MAX -> MIN <= b <= MAX -> b <> 0 -> ~ (a = MIN /\ b = -1) ->
  MIN <= Z.quot a b <= MAX.
Proof.
  intros a b Ha Hb H0 H1.
  destruct (Z.eq_dec b 1) as [-> | N1]; [ rewrite Z.quot_1_r; lia | ].
  destruct (Z.eq_dec b (-1)) as [-> | N2].
  { rewrite quot_m1. rep_lia. }
  assert (Habs: Z.abs (Z.quot a b) <= Int64.max_signed).
  { rewrite <- Z.quot_abs by lia. rewrite Z.quot_div_nonneg by lia.
    apply Z.div_le_upper_bound; [ lia | ]. rep_lia. }
  rep_lia.
Qed.

(* When the remainder is nonzero, the quotient is at most 2^62 in size: q +- 1 cannot overflow. *)
Lemma quot_small: forall a b,
  MIN <= a <= MAX -> b <> 0 -> Z.rem a b <> 0 -> - 2 ^ 62 <= Z.quot a b <= 2 ^ 62.
Proof.
  intros a b Ha H0 H1. pose proof (rem_nonzero_b a b H0 H1).
  assert (Habs: Z.abs (Z.quot a b) <= 2 ^ 62).
  { rewrite <- Z.quot_abs by lia. rewrite Z.quot_div_nonneg by lia.
    apply Z.le_trans with (Z.abs a / 2).
    - apply Z.div_le_compat_l; lia.
    - apply Z.div_le_upper_bound; [ lia | ]. rep_lia. }
  lia.
Qed.

Lemma rem_range: forall a b, MIN <= b <= MAX -> b <> 0 -> MIN <= Z.rem a b <= MAX.
Proof. intros. pose proof (Z.rem_bound_abs a b H0). rep_lia. Qed.

(* ---------------------------------------------------------------------- *)
(* The divisions from the truncated quotient and remainder                *)
(* ---------------------------------------------------------------------- *)

(* c_floordiv / vx_floordiv: q - 1 when r != 0 and the signs of r and b differ *)
Lemma floor_adj: forall a b, b <> 0 -> Z.rem a b <> 0 -> (Z.rem a b < 0 <-> ~ b < 0) ->
  a / b = Z.quot a b - 1.
Proof.
  intros. quot_facts a b. symmetry. apply Z.div_unique with (Z.rem a b + b); lia.
Qed.

Lemma floor_noadj: forall a b, b <> 0 -> (Z.rem a b = 0 \/ (Z.rem a b < 0 <-> b < 0)) ->
  a / b = Z.quot a b.
Proof.
  intros. quot_facts a b. symmetry. apply Z.div_unique with (Z.rem a b); lia.
Qed.

(* c_ceildiv / vx_ceildiv: q + 1 when r != 0 and the signs of r and b agree *)
Lemma ceil_adj: forall a b, b <> 0 -> Z.rem a b <> 0 -> (Z.rem a b < 0 <-> b < 0) ->
  ceildiv a b = Z.quot a b + 1.
Proof.
  intros. quot_facts a b. unfold ceildiv.
  assert (E: - a / b = - Z.quot a b - 1); [ | lia ].
  symmetry. apply Z.div_unique with (b - Z.rem a b); lia.
Qed.

Lemma ceil_noadj: forall a b, b <> 0 -> (Z.rem a b = 0 \/ (Z.rem a b < 0 <-> ~ b < 0)) ->
  ceildiv a b = Z.quot a b.
Proof.
  intros. quot_facts a b. unfold ceildiv.
  assert (E: - a / b = - Z.quot a b); [ | lia ].
  symmetry. apply Z.div_unique with (- Z.rem a b); lia.
Qed.

(* c_quotient / vx_quotient *)
Lemma ediv_neg_pos: forall a b, 0 < b -> Z.rem a b < 0 -> ediv a b = Z.quot a b - 1.
Proof.
  intros. quot_facts a b. unfold ediv. rewrite Z.sgn_pos, Z.abs_eq by lia. rewrite Z.mul_1_l.
  symmetry. apply Z.div_unique with (Z.rem a b + b); lia.
Qed.

Lemma ediv_neg_neg: forall a b, b < 0 -> Z.rem a b < 0 -> ediv a b = Z.quot a b + 1.
Proof.
  intros. quot_facts a b. unfold ediv. rewrite Z.sgn_neg, Z.abs_neq by lia.
  assert (E: a / - b = - Z.quot a b - 1); [ | lia ].
  symmetry. apply Z.div_unique with (Z.rem a b - b); lia.
Qed.

Lemma ediv_nonneg: forall a b, b <> 0 -> 0 <= Z.rem a b -> ediv a b = Z.quot a b.
Proof.
  intros. quot_facts a b. unfold ediv.
  destruct (Z.ltb_spec 0 b).
  - rewrite Z.sgn_pos, Z.abs_eq by lia. rewrite Z.mul_1_l.
    symmetry. apply Z.div_unique with (Z.rem a b); lia.
  - rewrite Z.sgn_neg, Z.abs_neq by lia.
    assert (E: a / - b = - Z.quot a b); [ | lia ].
    symmetry. apply Z.div_unique with (Z.rem a b); lia.
Qed.

(* c_modulo / vx_modulo *)
Lemma emod_neg_pos: forall a b, 0 < b -> Z.rem a b < 0 -> emod a b = Z.rem a b + b.
Proof.
  intros. quot_facts a b. unfold emod. rewrite Z.abs_eq by lia.
  symmetry. apply Z.mod_unique with (Z.quot a b - 1); lia.
Qed.

Lemma emod_neg_neg: forall a b, b < 0 -> Z.rem a b < 0 -> emod a b = Z.rem a b - b.
Proof.
  intros. quot_facts a b. unfold emod. rewrite Z.abs_neq by lia.
  symmetry. apply Z.mod_unique with (- Z.quot a b - 1); lia.
Qed.

Lemma emod_nonneg: forall a b, b <> 0 -> 0 <= Z.rem a b -> emod a b = Z.rem a b.
Proof.
  intros. quot_facts a b. unfold emod.
  destruct (Z.ltb_spec 0 b).
  - rewrite Z.abs_eq by lia. symmetry. apply Z.mod_unique with (Z.quot a b); lia.
  - rewrite Z.abs_neq by lia. symmetry. apply Z.mod_unique with (- Z.quot a b); lia.
Qed.

(* b = -1, where the code calls vx_neg (or stores 0) *)
Lemma div_m1: forall a, a / -1 = - a.
Proof. intros. symmetry. apply Z.div_unique with 0; lia. Qed.

Lemma ceildiv_m1: forall a, ceildiv a (-1) = - a.
Proof. intros. unfold ceildiv. rewrite div_m1. lia. Qed.

Lemma ediv_m1: forall a, ediv a (-1) = - a.
Proof. intros. unfold ediv. change (Z.sgn (-1)) with (-1). change (Z.abs (-1)) with 1. rewrite Z.div_1_r. lia. Qed.

Lemma emod_m1: forall a, emod a (-1) = 0.
Proof. intros. unfold emod. change (Z.abs (-1)) with 1. apply Z.mod_1_r. Qed.

(* The tests `r != 0 && ((r < 0) != (b < 0))` of floordiv and `r != 0 && ((r < 0) == (b < 0))` of ceildiv *)
Definition floor_adj_b (a b: Z) : bool := negb (Z.rem a b =? 0) && xorb (Z.rem a b <? 0) (b <? 0).
Definition ceil_adj_b (a b: Z) : bool := negb (Z.rem a b =? 0) && Bool.eqb (Z.rem a b <? 0) (b <? 0).

Lemma floor_adj_true: forall a b, MIN <= a <= MAX -> b <> 0 -> floor_adj_b a b = true ->
  a / b = Z.quot a b - 1 /\ - 2 ^ 62 <= Z.quot a b <= 2 ^ 62.
Proof.
  unfold floor_adj_b. intros a b Ha H0 F.
  destruct (Z.eqb_spec (Z.rem a b) 0); [ discriminate | ].
  split; [ | apply quot_small; auto ].
  apply floor_adj; auto.
  destruct (Z.ltb_spec (Z.rem a b) 0), (Z.ltb_spec b 0); simpl in F; try discriminate; split; intros; lia.
Qed.

Lemma floor_adj_false: forall a b, b <> 0 -> floor_adj_b a b = false -> a / b = Z.quot a b.
Proof.
  unfold floor_adj_b. intros a b H0 F. apply floor_noadj; auto.
  destruct (Z.eqb_spec (Z.rem a b) 0); [ left; auto | right ].
  destruct (Z.ltb_spec (Z.rem a b) 0), (Z.ltb_spec b 0); simpl in F; try discriminate; split; intros; lia.
Qed.

Lemma ceil_adj_true: forall a b, MIN <= a <= MAX -> b <> 0 -> ceil_adj_b a b = true ->
  ceildiv a b = Z.quot a b + 1 /\ - 2 ^ 62 <= Z.quot a b <= 2 ^ 62.
Proof.
  unfold ceil_adj_b. intros a b Ha H0 F.
  destruct (Z.eqb_spec (Z.rem a b) 0); [ discriminate | ].
  split; [ | apply quot_small; auto ].
  apply ceil_adj; auto.
  destruct (Z.ltb_spec (Z.rem a b) 0), (Z.ltb_spec b 0); simpl in F; try discriminate; split; intros; lia.
Qed.

Lemma ceil_adj_false: forall a b, b <> 0 -> ceil_adj_b a b = false -> ceildiv a b = Z.quot a b.
Proof.
  unfold ceil_adj_b. intros a b H0 F. apply ceil_noadj; auto.
  destruct (Z.eqb_spec (Z.rem a b) 0); [ left; auto | right ].
  destruct (Z.ltb_spec (Z.rem a b) 0), (Z.ltb_spec b 0); simpl in F; try discriminate; split; intros; lia.
Qed.

(* The results fit, except at (INT64_MIN, -1) *)
Ltac sd := first [ assumption | lia | (left; lia) | (right; lia) | tauto ].
Lemma div_fits: forall a b,
  MIN <= a <= MAX -> MIN <= b <= MAX -> b <> 0 -> ~ (a = MIN /\ b = -1) -> MIN <= a / b <= MAX.
Proof.
  intros a b Ha Hb H0 H1. pose proof (quot_range a b Ha Hb H0 H1).
  destruct (Z.eq_dec (Z.rem a b) 0) as [R | R].
  - rewrite floor_noadj by sd. lia.
  - pose proof (quot_small a b Ha H0 R).
    destruct (Z.ltb_spec (Z.rem a b) 0), (Z.ltb_spec b 0).
    + rewrite floor_noadj by sd. lia.
    + rewrite floor_adj by sd. rep_lia.
    + rewrite floor_adj by sd. rep_lia.
    + rewrite floor_noadj by sd. lia.
Qed.

Lemma ceildiv_fits: forall a b,
  MIN <= a <= MAX -> MIN <= b <= MAX -> b <> 0 -> ~ (a = MIN /\ b = -1) -> MIN <= ceildiv a b <= MAX.
Proof.
  intros a b Ha Hb H0 H1. pose proof (quot_range a b Ha Hb H0 H1).
  destruct (Z.eq_dec (Z.rem a b) 0) as [R | R].
  - rewrite ceil_noadj by sd. lia.
  - pose proof (quot_small a b Ha H0 R).
    destruct (Z.ltb_spec (Z.rem a b) 0), (Z.ltb_spec b 0).
    + rewrite ceil_adj by sd. rep_lia.
    + rewrite ceil_noadj by sd. lia.
    + rewrite ceil_noadj by sd. lia.
    + rewrite ceil_adj by sd. rep_lia.
Qed.

Lemma ediv_fits: forall a b,
  MIN <= a <= MAX -> MIN <= b <= MAX -> b <> 0 -> ~ (a = MIN /\ b = -1) -> MIN <= ediv a b <= MAX.
Proof.
  intros a b Ha Hb H0 H1. pose proof (quot_range a b Ha Hb H0 H1).
  destruct (Z.ltb_spec (Z.rem a b) 0).
  - pose proof (quot_small a b Ha H0 ltac:(lia)).
    destruct (Z.ltb_spec 0 b).
    + rewrite ediv_neg_pos by sd. rep_lia.
    + rewrite ediv_neg_neg by sd. rep_lia.
  - rewrite ediv_nonneg by sd. lia.
Qed.

Lemma emod_fits: forall a b, MIN <= b <= MAX -> b <> 0 -> MIN <= emod a b <= MAX.
Proof. intros. pose proof (ediv_emod_spec a b H0). rep_lia. Qed.

Lemma min_m1_div: in64 (MIN / -1) = false.
Proof. reflexivity. Qed.
Lemma min_m1_ceildiv: in64 (ceildiv MIN (-1)) = false.
Proof. reflexivity. Qed.
Lemma min_m1_ediv: in64 (ediv MIN (-1)) = false.
Proof. reflexivity. Qed.
Lemma min_m1_emod: emod MIN (-1) = 0.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Multiplication: comparisons with a truncated quotient                  *)
(* ---------------------------------------------------------------------- *)

Lemma le_quot_pos_nonneg: forall x b c, 0 < b -> 0 <= c -> (x <= Z.quot c b <-> x * b <= c).
Proof. intros. quot_facts c b. split; intros; nia. Qed.

Lemma quot_le_pos_nonpos: forall x b c, 0 < b -> c <= 0 -> (Z.quot c b <= x <-> c <= x * b).
Proof. intros. quot_facts c b. split; intros; nia. Qed.

Lemma quot_le_neg_nonneg: forall x b c, b < 0 -> 0 <= c -> (Z.quot c b <= x <-> x * b <= c).
Proof. intros. quot_facts c b. split; intros; nia. Qed.

Lemma le_quot_neg_nonpos: forall x b c, b < 0 -> c <= 0 -> (x <= Z.quot c b <-> c <= x * b).
Proof. intros. quot_facts c b. split; intros; nia. Qed.

(* vx_mul's four tests, each equivalent to the overflow of a * b *)
Lemma mul_ovf_pp: forall a b, 0 < a -> 0 < b ->
  (Z.quot MAX b < a <-> ~ (MIN <= a * b <= MAX)).
Proof.
  intros. pose proof (le_quot_pos_nonneg a b MAX H0 ltac:(rep_lia)).
  assert (0 < a * b) by nia. rep_lia.
Qed.

Lemma mul_ovf_pn: forall a b, 0 < a -> b <= 0 ->
  (b < Z.quot MIN a <-> ~ (MIN <= a * b <= MAX)).
Proof.
  intros. pose proof (quot_le_pos_nonpos b a MIN H ltac:(rep_lia)). rewrite (Z.mul_comm b a) in H1.
  assert (a * b <= 0) by nia. rep_lia.
Qed.

Lemma mul_ovf_np: forall a b, a < 0 -> 0 < b ->
  (a < Z.quot MIN b <-> ~ (MIN <= a * b <= MAX)).
Proof.
  intros. pose proof (quot_le_pos_nonpos a b MIN H0 ltac:(rep_lia)).
  assert (a * b < 0) by nia. rep_lia.
Qed.

Lemma mul_ovf_nn: forall a b, a < 0 -> b < 0 ->
  (b < Z.quot MAX a <-> ~ (MIN <= a * b <= MAX)).
Proof.
  intros. pose proof (quot_le_neg_nonneg b a MAX H ltac:(rep_lia)). rewrite (Z.mul_comm b a) in H1.
  assert (0 < a * b) by nia. rep_lia.
Qed.

(* mul_fits's tests *)
Lemma mul_fits_m1: forall a, MIN <= a <= MAX -> (a <> MIN <-> MIN <= a * -1 <= MAX).
Proof. intros. rep_lia. Qed.

Lemma mul_fits_pos: forall a b, 0 < b ->
  (Z.quot MIN b <= a /\ a <= Z.quot MAX b <-> MIN <= a * b <= MAX).
Proof.
  intros. pose proof (le_quot_pos_nonneg a b MAX H ltac:(rep_lia)).
  pose proof (quot_le_pos_nonpos a b MIN H ltac:(rep_lia)). rep_lia.
Qed.

Lemma mul_fits_neg: forall a b, b < 0 ->
  (Z.quot MAX b <= a /\ a <= Z.quot MIN b <-> MIN <= a * b <= MAX).
Proof.
  intros. pose proof (quot_le_neg_nonneg a b MAX H ltac:(rep_lia)).
  pose proof (le_quot_neg_nonpos a b MIN H ltac:(rep_lia)). rep_lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* Int64 on in-range values                                               *)
(* ---------------------------------------------------------------------- *)

Lemma divs_repr: forall x y, MIN <= x <= MAX -> MIN <= y <= MAX ->
  Int64.divs (Int64.repr x) (Int64.repr y) = Int64.repr (Z.quot x y).
Proof. intros. unfold Int64.divs. rewrite !Int64.signed_repr by lia. reflexivity. Qed.

Lemma mods_repr: forall x y, MIN <= x <= MAX -> MIN <= y <= MAX ->
  Int64.mods (Int64.repr x) (Int64.repr y) = Int64.repr (Z.rem x y).
Proof. intros. unfold Int64.mods. rewrite !Int64.signed_repr by lia. reflexivity. Qed.

Lemma lt_repr: forall x y, MIN <= x <= MAX -> MIN <= y <= MAX ->
  Int64.lt (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.lt. rewrite !Int64.signed_repr by lia.
  destruct (zlt x y), (Z.ltb_spec x y); auto; lia.
Qed.

Lemma eq_repr: forall x y, MIN <= x <= MAX -> MIN <= y <= MAX ->
  Int64.eq (Int64.repr x) (Int64.repr y) = (x =? y).
Proof.
  intros. pose proof (Int64.eq_spec (Int64.repr x) (Int64.repr y)).
  destruct (Int64.eq (Int64.repr x) (Int64.repr y)), (Z.eqb_spec x y); auto.
  - apply (f_equal Int64.signed) in H1. rewrite !Int64.signed_repr in H1 by lia. contradiction.
  - subst. contradiction.
Qed.

Lemma min_signed_expr:
  Int64.sub (Int64.neg (Int64.repr 9223372036854775807)) (Int64.repr 1) = Int64.repr MIN.
Proof. apply Int64.same_if_eq. vm_compute. reflexivity. Qed.
