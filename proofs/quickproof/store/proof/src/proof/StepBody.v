(* One iteration of main's loop: op = nondet_u8(), the operation it selects, the checks. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.proof.Law OpenverseStore.proof.MainLib.
Require Import OpenverseStore.proof.StepMark OpenverseStore.proof.StepSet OpenverseStore.proof.StepAppend
  OpenverseStore.proof.StepRollback OpenverseStore.proof.StepCommit OpenverseStore.proof.StepChecks.

Ltac use_step L :=
  eapply semax_pre; [ | eapply semax_normal_weak; [ apply L | ] ];
  [ unfold MSTk, MLOC, MSEP; entailer!
  | match goal with |- ENTAIL _, _ |-- RA_normal ?P => unfold P, abbreviate end;
    simpl RA_normal; apply andp_left2; apply derives_refl ].

Lemma step_body {Espec: OracleKind}: forall E k st,
  semax Delta_main (MSTk E k st) body_stmt (normal_ret_assert (EX st': mstate, MSTk E k st')).
Proof.
  intros. unfold Delta_main, body_stmt. abbreviate_semax.
  unfold MSTk at 1, MLOC, MSEP. Intros.
  forward_call. Intros opv.
  forward_if (EX st': mstate, MSTk E k st').
  { use_step step_mark. }
  forward_if.
  { use_step step_set. }
  forward_if.
  { use_step step_append. }
  forward_if.
  { use_step step_rollback. }
  forward_if.
  { use_step step_commit. }
  { forward. unfold MSTk, MLOC, MSEP. Exists st. entailer!. }
  Intros st'.
  eapply semax_normal_weak; [ apply step_checks | ].
  match goal with |- ENTAIL _, _ |-- RA_normal ?P => unfold P, abbreviate end.
  cbn [RA_normal normal_ret_assert]. apply andp_left2. Exists st'. apply derives_refl.
Qed.
