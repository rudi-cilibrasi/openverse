(* The functional model of the transactional store (runtime/src/store.c) and of the harness's
   failure contexts.  Pure Rocq: no separation logic.

   A value is a pair of 64-bit words (tag, bits); a journal entry is (slot, old value).  undo
   replays a journal segment newest first, exactly as vx_store_rollback's loop does.  chain is
   the invariant that ties the open failure contexts (innermost first) to the journal: each
   context's snapshot is what undoing the journal down to its mark gives, and the outer contexts
   are related in the same way to the state at the mark. *)
Require Import VST.floyd.proofauto.

(* Notations, not definitions, so that lia sees one Zlength for a list of either. *)
Notation V := (int64 * int64)%type (only parsing).
Notation J := (Z * (int64 * int64))%type (only parsing).

Fixpoint undo (seg: list J) (vs: list V) : list V :=
  match seg with
  | [] => vs
  | e :: seg' => upd_Znth (fst e) (undo seg' vs) (snd e)
  end.

Lemma Zlength_upd_Znth_any {A} (i: Z) (l: list A) (x: A) :
  Zlength (upd_Znth i l x) = Zlength l.
Proof.
  unfold upd_Znth. destruct (Sumbool.sumbool_and _ _ _ _ _ _); [ | reflexivity ].
  destruct a. list_solve.
Qed.

Lemma Zlength_undo: forall seg vs, Zlength (undo seg vs) = Zlength vs.
Proof.
  induction seg; simpl; intros; auto. rewrite Zlength_upd_Znth_any. auto.
Qed.

Lemma undo_app: forall l1 l2 vs, undo (l1 ++ l2) vs = undo l1 (undo l2 vs).
Proof.
  induction l1; simpl; intros; auto. rewrite IHl1; auto.
Qed.

Lemma undo_nil: forall vs, undo [] vs = vs.
Proof. reflexivity. Qed.

Lemma undo_set: forall sl (vs: list V) v,
  0 <= sl < Zlength vs ->
  undo [(sl, Znth sl vs)] (upd_Znth sl vs v) = vs.
Proof.
  intros. simpl. list_solve.
Qed.

Lemma sublist_snoc {A} (lo: Z) (l: list A) (x: A) :
  0 <= lo <= Zlength l ->
  sublist lo (Zlength (l ++ [x])) (l ++ [x]) = sublist lo (Zlength l) l ++ [x].
Proof.
  intros. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite sublist_app' by list_solve.
  f_equal. rewrite sublist_same; auto. list_solve.
Qed.

Lemma sublist0_snoc {A} (hi: Z) (l: list A) (x: A) :
  0 <= hi <= Zlength l ->
  sublist 0 hi (l ++ [x]) = sublist 0 hi l.
Proof. intros. rewrite sublist_app1 by list_solve. reflexivity. Qed.

(* One open failure context: the slots, the output and the journal length at its mark. *)
Record snap := mksnap { sn_vs : list V; sn_os : list Z; sn_j : Z }.

(* The contexts, innermost first. *)
Fixpoint chain (js: list J) (vs: list V) (os: list Z) (S: list snap) : Prop :=
  match S with
  | [] => js = []
  | s :: S' =>
      0 <= sn_j s <= Zlength js /\
      undo (sublist (sn_j s) (Zlength js) js) vs = sn_vs s /\
      Zlength (sn_os s) <= Zlength os /\
      sublist 0 (Zlength (sn_os s)) os = sn_os s /\
      chain (sublist 0 (sn_j s) js) (sn_vs s) (sn_os s) S'
  end.

Lemma chain_nil_js: forall js vs os, chain js vs os [] -> js = [].
Proof. simpl; auto. Qed.

Lemma chain_mark: forall js vs os S,
  chain js vs os S -> chain js vs os (mksnap vs os (Zlength js) :: S).
Proof.
  intros. simpl. split; [ split; [ list_solve | lia ] | ].
  rewrite sublist_nil. split; [ reflexivity | ].
  split; [ lia | ]. rewrite sublist_same by lia. split; [ reflexivity | ].
  rewrite sublist_same by lia. auto.
Qed.

Lemma chain_set_top: forall js vs os s S sl v,
  chain js vs os (s :: S) -> 0 <= sl < Zlength vs ->
  chain (js ++ [(sl, Znth sl vs)]) (upd_Znth sl vs v) os (s :: S).
Proof.
  intros js vs os s S sl v (H1 & H2 & H3 & H4 & H5) Hsl. simpl.
  split; [ list_solve | ].
  split.
  { rewrite sublist_snoc by lia.
    rewrite undo_app. rewrite undo_set by auto. auto. }
  split; [ auto | ]. split; [ auto | ].
  rewrite sublist0_snoc by lia. auto.
Qed.

Lemma chain_set_nil: forall js vs vs' os,
  chain js vs os [] -> chain js vs' os [].
Proof. simpl; auto. Qed.

Lemma chain_append: forall S js vs os x,
  chain js vs os S -> chain js vs (os ++ x) S.
Proof.
  destruct S as [| s S]; simpl; intros js vs os x H; auto.
  destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [ auto | ]. split; [ auto | ].
  split; [ list_solve | ]. split; [ | auto ].
  rewrite sublist_app1 by list_solve. auto.
Qed.

(* Leaving the innermost context after a failure: the state at its mark, with the journal cut back. *)
Lemma chain_rollback: forall js vs os s S,
  chain js vs os (s :: S) ->
  (if Zlength S =? 0 then [] else sublist 0 (sn_j s) js) = sublist 0 (sn_j s) js /\
  chain (sublist 0 (sn_j s) js) (sn_vs s) (sn_os s) S.
Proof.
  intros js vs os s S (H1 & H2 & H3 & H4 & H5). split; auto.
  destruct S as [| s2 S2].
  - simpl in H5. rewrite H5. reflexivity.
  - rewrite Zlength_cons. pose proof (Zlength_nonneg S2).
    destruct (Z.eqb_spec (Z.succ (Zlength S2)) 0); [ lia | reflexivity ].
Qed.

Lemma chain_extend: forall S js j vs sv os so,
  chain (sublist 0 j js) sv so S ->
  0 <= j <= Zlength js ->
  undo (sublist j (Zlength js) js) vs = sv ->
  Zlength so <= Zlength os ->
  sublist 0 (Zlength so) os = so ->
  S <> [] ->
  chain js vs os S.
Proof.
  intros [| s2 S2] js j vs sv os so H Hj Hu Ho Hso HS; [ congruence | ].
  destruct H as (H1 & H2 & H3 & H4 & H5).
  rewrite Zlength_sublist in H1 by lia. rewrite Z.sub_0_r in H1.
  rewrite Zlength_sublist in H2 by lia. rewrite Z.sub_0_r in H2.
  rewrite sublist_sublist0 in H2 by lia.
  rewrite sublist_sublist00 in H5 by lia.
  simpl. split; [ lia | ].
  split.
  { rewrite <- (sublist_rejoin (sn_j s2) j (Zlength js) js) by lia.
    rewrite undo_app. rewrite Hu. exact H2. }
  split; [ lia | ].
  split.
  { transitivity (sublist 0 (Zlength (sn_os s2)) so); [ | exact H4 ].
    pose proof (Zlength_nonneg (sn_os s2)).
    rewrite <- Hso. rewrite sublist_sublist00 by lia. reflexivity. }
  exact H5.
Qed.

(* Leaving the innermost context after a success: the effects stay. *)
Lemma chain_commit: forall js vs os s S,
  chain js vs os (s :: S) ->
  chain (if Zlength S =? 0 then [] else js) vs os S.
Proof.
  intros js vs os s S H.
  destruct S as [| s2 S2].
  - simpl. reflexivity.
  - rewrite Zlength_cons. pose proof (Zlength_nonneg S2).
    destruct (Z.eqb_spec (Z.succ (Zlength S2)) 0); [ lia | ].
    destruct H as (H1 & H2 & H3 & H4 & H5).
    eapply chain_extend; eauto. congruence.
Qed.

Lemma chain_facts: forall js vs os s S,
  chain js vs os (s :: S) ->
  0 <= sn_j s <= Zlength js /\ Zlength (sn_vs s) = Zlength vs /\
  Zlength (sn_os s) <= Zlength os /\ sublist 0 (Zlength (sn_os s)) os = sn_os s.
Proof.
  intros js vs os s S (H1 & H2 & H3 & H4 & H5).
  split; auto. split; auto. rewrite <- H2. apply Zlength_undo.
Qed.

(* The first context (the outermost) is entered with an empty journal. *)
Lemma chain_depth0: forall js vs os, chain js vs os [] -> Zlength js = 0.
Proof. intros. simpl in H. subst. reflexivity. Qed.
