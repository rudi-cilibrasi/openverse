(* Lemmas for main: lists with a known prefix, the rows of main's copy arrays, and how each
   operation of the law keeps inv_ok. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseStore.proof.Law.

(* ---------------------------------------------------------------------- *)
(* Prefixes                                                                *)
(* ---------------------------------------------------------------------- *)

Lemma Znth_pre {A B} {dA: Inhabitant A} {dB: Inhabitant B} (f: B -> A) (l: list A) (m: list B) n i:
  sublist 0 n l = map f m -> 0 <= i < n -> n <= Zlength l -> Znth i l = f (Znth i m).
Proof.
  intros H Hi Hn.
  assert (Hm: Zlength m = n).
  { apply (f_equal (@Zlength A)) in H. rewrite Zlength_sublist, Zlength_map in H by lia. lia. }
  transitivity (Znth i (sublist 0 n l)).
  - rewrite Znth_sublist by lia. f_equal; lia.
  - rewrite H. apply Znth_map. lia.
Qed.

Lemma pre_len {A B} (f: B -> A) (l: list A) (m: list B) n:
  sublist 0 n l = map f m -> 0 <= n <= Zlength l -> Zlength m = n.
Proof.
  intros H Hn. apply (f_equal (@Zlength A)) in H. rewrite Zlength_sublist, Zlength_map in H by lia. lia.
Qed.

Lemma pre_upd {A B} {dA: Inhabitant A} {dB: Inhabitant B} (f: B -> A) (l: list A) (m: list B) n i x:
  sublist 0 n l = map f m -> 0 <= i < n -> n <= Zlength l ->
  sublist 0 n (upd_Znth i l (f x)) = map f (upd_Znth i m x).
Proof.
  intros H Hi Hn. pose proof (pre_len f l m n H ltac:(lia)).
  rewrite <- upd_Znth_map. rewrite <- H. rewrite sublist_upd_Znth_lr by lia.
  f_equal. lia.
Qed.

Lemma pre_snoc {A B} {dA: Inhabitant A} (f: B -> A) (l: list A) (m: list B) i x:
  sublist 0 i l = map f m -> 0 <= i < Zlength l ->
  sublist 0 (i + 1) (upd_Znth i l (f x)) = map f (m ++ [x]).
Proof.
  intros H Hi. pose proof (pre_len f l m i H ltac:(lia)).
  rewrite map_app. rewrite <- H. simpl map.
  rewrite (sublist_split 0 i (i+1)) by list_solve.
  f_equal.
  - rewrite sublist_upd_Znth_l by lia. reflexivity.
  - rewrite sublist_len_1 by list_solve. rewrite upd_Znth_same by lia. reflexivity.
Qed.

Lemma pre_shrink {A B} (f: B -> A) (l: list A) (m: list B) n k:
  sublist 0 n l = map f m -> 0 <= k <= n -> n <= Zlength l ->
  sublist 0 k l = map f (sublist 0 k m).
Proof.
  intros H Hk Hn. pose proof (pre_len f l m n H ltac:(lia)).
  rewrite <- sublist_map. rewrite <- H. rewrite sublist_sublist00 by lia. reflexivity.
Qed.

Lemma pre_app {A B} (f: B -> A) (l: list A) (m: list B):
  0 <= Zlength m <= Zlength l -> sublist 0 (Zlength m) l = map f m -> True.
Proof. auto. Qed.

(* ---------------------------------------------------------------------- *)
(* Rows of a two-dimensional array, row d being filled.                    *)
(* ---------------------------------------------------------------------- *)

Definition rows_ok {A} {dA: Inhabitant A} (old new: list (list A)) (d: Z) (pre: list A) (len: Z) : Prop :=
  Zlength new = 3 /\ Forall (fun r => Zlength r = len) new /\
  (forall d', 0 <= d' < 3 -> d' <> d -> Znth d' new = Znth d' old) /\
  sublist 0 (Zlength pre) (Znth d new) = pre.

Lemma rows_ok_start {A} {dA: Inhabitant A} (old: list (list A)) d len:
  Zlength old = 3 -> Forall (fun r => Zlength r = len) old -> rows_ok old old d [] len.
Proof.
  intros. split; [ auto | ]. split; [ auto | ]. split; [ auto | ].
  rewrite Zlength_nil, sublist_nil. reflexivity.
Qed.

Lemma rows_ok_step {A} {dA: Inhabitant A} (old new: list (list A)) d pre len x:
  rows_ok old new d pre len -> 0 <= d < 3 -> Zlength pre < len ->
  rows_ok old (upd_Znth d new (upd_Znth (Zlength pre) (Znth d new) x)) d (pre ++ [x]) len.
Proof.
  intros (H1 & H2 & H3 & H4) Hd Hp.
  assert (Hr: Zlength (Znth d new) = len) by (apply (proj1 (Forall_Znth _ _) H2); lia).
  pose proof (Zlength_nonneg pre).
  split; [ list_solve | ].
  split.
  { apply Forall_upd_Znth; auto. list_solve. }
  split.
  { intros. rewrite upd_Znth_diff by lia. auto. }
  rewrite upd_Znth_same by lia.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite (sublist_split 0 (Zlength pre) (Zlength pre + Z.succ 0)) by list_solve.
  rewrite sublist_upd_Znth_l by lia. rewrite H4.
  f_equal. rewrite sublist_len_1 by list_solve. rewrite upd_Znth_same by lia. reflexivity.
Qed.

Lemma rows_ok_step_map {A B} {dA: Inhabitant A} {dB: Inhabitant B} (f: B -> A)
    (old new: list (list A)) d (l: list B) i len:
  rows_ok old new d (map f (sublist 0 i l)) len -> 0 <= d < 3 -> 0 <= i < Zlength l -> i < len ->
  rows_ok old (upd_Znth d new (upd_Znth i (Znth d new) (f (Znth i l)))) d (map f (sublist 0 (i+1) l)) len.
Proof.
  intros H Hd Hi Hl.
  assert (Hz: Zlength (map f (sublist 0 i l)) = i) by (rewrite Zlength_map, Zlength_sublist; lia).
  pose proof (rows_ok_step old new d (map f (sublist 0 i l)) len (f (Znth i l)) H Hd ltac:(lia)) as H1.
  rewrite Hz in H1.
  replace (map f (sublist 0 (i + 1) l)) with (map f (sublist 0 i l) ++ [f (Znth i l)]); auto.
  rewrite (sublist_split 0 i (i+1)) by lia. rewrite sublist_len_1 by lia.
  rewrite map_app. reflexivity.
Qed.

Lemma Znth_std {A} (d1 d2: Inhabitant A) i (l: list A):
  0 <= i < Zlength l -> @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros Hi. unfold Znth. destruct (Z_lt_dec i 0); [ lia | ].
  apply nth_indep. rewrite Zlength_correct in Hi. lia.
Qed.

(* The same, with the default value of the rows that VST's stores use (dR is not an instance, so
   that it is never chosen by typeclass resolution). *)
Lemma rows_ok_step_any {A B} {dA: Inhabitant A} {dB: Inhabitant B} (dR: list A) (f: B -> A)
    (old new: list (list A)) d (l: list B) i len:
  rows_ok old new d (map f (sublist 0 i l)) len -> 0 <= d < 3 -> 0 <= i < Zlength l -> i < len ->
  rows_ok old (upd_Znth d new (upd_Znth i (@Znth (list A) dR d new) (f (Znth i l)))) d
    (map f (sublist 0 (i+1) l)) len.
Proof.
  intros H Hd Hi Hl. rewrite (Znth_std dR (@Inhabitant_list A) d new) by (destruct H as [H1 _]; lia).
  apply rows_ok_step_map; auto.
Qed.

(* A load of rows[d][i] where row d has a known prefix. *)
Lemma Znth2_pre {A B} {dA: Inhabitant A} {dB: Inhabitant B} (dR: list A) (f: B -> A)
    (rows: list (list A)) (m: list B) d n i:
  sublist 0 n (@Znth (list A) Inhabitant_list d rows) = map f m -> 0 <= d < Zlength rows -> 0 <= i < n ->
  n <= Zlength (@Znth (list A) Inhabitant_list d rows) ->
  Znth i (@Znth (list A) dR d rows) = f (Znth i m).
Proof.
  intros H Hd Hi Hn. rewrite (Znth_std dR (@Inhabitant_list A) d rows) by lia.
  apply (Znth_pre f _ _ n); auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The open contexts                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma S_last: forall (S: list snap), 0 < Zlength S ->
  S = sublist 0 (Zlength S - 1) S ++ [Znth (Zlength S - 1) S].
Proof.
  intros. rewrite <- sublist_len_1 by lia. rewrite sublist_rejoin by lia.
  rewrite sublist_same by lia. reflexivity.
Qed.

Lemma rev_S_last: forall (S: list snap), 0 < Zlength S ->
  rev S = Znth (Zlength S - 1) S :: rev (sublist 0 (Zlength S - 1) S).
Proof.
  intros. rewrite (S_last S) at 1 by auto. rewrite rev_app_distr. reflexivity.
Qed.

Lemma Znth_S_app: forall (S: list snap) s d, 0 <= d < Zlength S -> Znth d (S ++ [s]) = Znth d S.
Proof. intros. rewrite Znth_app1 by lia. reflexivity. Qed.

Lemma Znth_S_sub: forall (S: list snap) n d, 0 <= d < n -> n <= Zlength S -> Znth d (sublist 0 n S) = Znth d S.
Proof. intros. rewrite Znth_sublist by lia. f_equal; lia. Qed.

(* The facts of the top context, d = Zlength S - 1. *)
Lemma top_facts: forall E st,
  inv_ok E st -> 0 < Zlength (m_S st) ->
  let s := Znth (Zlength (m_S st) - 1) (m_S st) in
  0 <= sn_j s <= Zlength (m_js st) /\
  undo (sublist (sn_j s) (Zlength (m_js st)) (m_js st)) (m_vs st) = sn_vs s /\
  Zlength (sn_os s) <= Zlength (m_os st) /\
  sublist 0 (Zlength (sn_os s)) (m_os st) = sn_os s /\
  chain (sublist 0 (sn_j s) (m_js st)) (sn_vs s) (sn_os s) (rev (sublist 0 (Zlength (m_S st) - 1) (m_S st))).
Proof.
  intros E st Hinv HS s.
  pose proof (i_chain _ _ Hinv) as Hch.
  rewrite rev_S_last in Hch by auto. exact Hch.
Qed.

Lemma byte_at: forall (l: list Z) i,
  Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> 0 <= i < Zlength l ->
  0 <= Znth i l <= Byte.max_unsigned.
Proof. intros. apply (proj1 (Forall_Znth _ _) H). auto. Qed.

Lemma byte_repr_range: forall b, 0 <= b <= Byte.max_unsigned ->
  Int.unsigned (Int.repr b) <= Byte.max_unsigned.
Proof. intros. rewrite Int.unsigned_repr by rep_lia. lia. Qed.

(* An equation on Znth, for any default value (VST's loads choose their own). *)
Lemma Znth_any {A} (d1 d2: Inhabitant A) i (l: list A) v:
  @Znth A d1 i l = v -> 0 <= i < Zlength l -> @Znth A d2 i l = v.
Proof.
  intros H Hi. rewrite <- H. unfold Znth. destruct (Z_lt_dec i 0); [ lia | ].
  apply nth_indep. rewrite Zlength_correct in Hi. lia.
Qed.

(* qp_assume(a <= b) on size_t. *)
Lemma assume_le: forall a b,
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int.repr (Z.b2z (negb (Int64.ltu (Int64.repr b) (Int64.repr a)))) <> Int.zero -> a <= b.
Proof.
  intros a b Ha Hb H. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by lia.
  destruct (zlt b a); [ simpl in H; contradiction | lia ].
Qed.

(* pick(x) on a uint64_t x: nondet_bytes writes its 8 bytes. *)
Lemma ulong_as_bytes: forall sh q,
  data_at_ sh tulong q |-- data_at_ sh (tarray tuchar 8) q.
Proof.
  intros. rewrite !data_at__memory_block. Intros.
  change (sizeof tulong) with 8. change (sizeof (tarray tuchar 8)) with 8.
  apply andp_right; [ | apply derives_refl ].
  apply prop_right.
  destruct H as (Hp & Hl & Hs & Ha & Hn).
  repeat split; auto.
  destruct q; try contradiction. simpl.
  apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [ reflexivity | ]. apply Z.divide_1_l.
Qed.

(* ---------------------------------------------------------------------- *)
(* Tactics for main's steps                                                *)
(* ---------------------------------------------------------------------- *)

(* qp_assert(c) for a c that holds. *)
Ltac assert1 :=
  forward_call (Int.one);
  try (solve [ entailer!; try (rewrite ?Int64.eq_true, ?Int.eq_true; reflexivity) ]).

(* A load of l[i] where sublist 0 n l = map f m. *)
Ltac ldpre f l m n i :=
  forward;
  try (solve [ rewrite (Znth_pre f l m n i) by (auto; lia); entailer!;
               try (apply byte_repr_range, byte_at; auto; lia) ]);
  try rewrite (Znth_pre f l m n i) by (auto; lia).
