(* Small arithmetic helpers for size_t / int comparisons in the proofs. *)
Require Import VST.floyd.proofauto.

Lemma repr64_inj: forall a b,
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.repr a = Int64.repr b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal Int64.unsigned) in E.
  rewrite !Int64.unsigned_repr in E by lia. exact E.
Qed.

Lemma ltu64_true: forall a b,
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = true -> a < b.
Proof.
  intros. unfold Int64.ltu in H1. rewrite !Int64.unsigned_repr in H1 by lia.
  destruct (zlt a b); [ auto | discriminate ].
Qed.

Lemma ltu64_false: forall a b,
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = false -> b <= a.
Proof.
  intros. unfold Int64.ltu in H1. rewrite !Int64.unsigned_repr in H1 by lia.
  destruct (zlt a b); [ discriminate | lia ].
Qed.

Lemma repr_inj_small: forall a b,
  0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.repr a = Int.repr b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal Int.unsigned) in E.
  rewrite !Int.unsigned_repr in E by lia. exact E.
Qed.

(* Turn the comparison facts forward_if leaves into facts on Z. *)
Ltac z64 :=
  repeat match goal with
  | H: Int64.repr ?a = Int64.zero |- _ =>
      change Int64.zero with (Int64.repr 0) in H
  | H: Int64.repr ?a <> Int64.zero |- _ =>
      change Int64.zero with (Int64.repr 0) in H
  | H: Int64.repr ?a = Int64.repr ?b |- _ =>
      apply repr64_inj in H; [ | rep_lia | rep_lia ]
  | H: Int64.repr ?a <> Int64.repr ?b |- _ =>
      let E := fresh in
      assert (E: a <> b) by (let Heq := fresh in intro Heq; rewrite Heq in H; contradiction); clear H
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
      apply ltu64_true in H; [ | rep_lia | rep_lia ]
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = false |- _ =>
      apply ltu64_false in H; [ | rep_lia | rep_lia ]
  | H: context [Int64.unsigned (Int64.repr ?a)] |- _ =>
      rewrite (Int64.unsigned_repr a) in H by rep_lia
  | H: context [Int.unsigned (Int.repr ?a)] |- _ =>
      rewrite (Int.unsigned_repr a) in H by rep_lia
  end.

(* After the implicit return at the end of a void function without locals. *)
Ltac fix_sf :=
  unfold stackframe_of; simpl fn_vars; simpl fold_right;
  change (fun _ : environ => emp) with (@emp (environ -> mpred) _ _); rewrite sepcon_emp.

(* forward, closing the bounds / range side conditions it leaves. *)
Ltac fw := forward; try (solve [ entailer!; try rep_lia ]).
