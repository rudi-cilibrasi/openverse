(* One field of a struct as a separate cell, for the readers that write through &nd->a or &fn->name_off. *)
Require Import VST.floyd.proofauto.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
#[local] Existing Instance Specs.CS.
Local Open Scope logic.

Definition node_hole_a sh (vt vo vb vc vd vl nd: val) : mpred :=
  field_at sh t_node [StructField _tag] vt nd * field_at sh t_node [StructField _op] vo nd *
  field_at sh t_node [StructField _b] vb nd * field_at sh t_node [StructField _c] vc nd *
  field_at sh t_node [StructField _d] vd nd * field_at sh t_node [StructField _lit] vl nd.

Definition node_hole_b sh (vt vo va vc vd vl nd: val) : mpred :=
  field_at sh t_node [StructField _tag] vt nd * field_at sh t_node [StructField _op] vo nd *
  field_at sh t_node [StructField _a] va nd * field_at sh t_node [StructField _c] vc nd *
  field_at sh t_node [StructField _d] vd nd * field_at sh t_node [StructField _lit] vl nd.

Definition node_hole_c sh (vt vo va vb vd vl nd: val) : mpred :=
  field_at sh t_node [StructField _tag] vt nd * field_at sh t_node [StructField _op] vo nd *
  field_at sh t_node [StructField _a] va nd * field_at sh t_node [StructField _b] vb nd *
  field_at sh t_node [StructField _d] vd nd * field_at sh t_node [StructField _lit] vl nd.

Definition node_hole_d sh (vt vo va vb vc vl nd: val) : mpred :=
  field_at sh t_node [StructField _tag] vt nd * field_at sh t_node [StructField _op] vo nd *
  field_at sh t_node [StructField _a] va nd * field_at sh t_node [StructField _b] vb nd *
  field_at sh t_node [StructField _c] vc nd * field_at sh t_node [StructField _lit] vl nd.

Lemma node_split_a sh (vt vo va vb vc vd vl nd: val):
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd |--
  data_at sh tuint va (field_address t_node [StructField _a] nd) * node_hole_a sh vt vo vb vc vd vl nd.
Proof.
  unfold_data_at (data_at _ _ _ nd). rewrite (field_at_data_at sh t_node [StructField _a]).
  unfold node_hole_a. cancel.
Qed.

Lemma node_fold_a sh (vt vo va vb vc vd vl nd: val):
  data_at sh tuint va (field_address t_node [StructField _a] nd) * node_hole_a sh vt vo vb vc vd vl nd |--
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd.
Proof.
  unfold_data_at (data_at _ _ _ nd). rewrite (field_at_data_at sh t_node [StructField _a]).
  unfold node_hole_a. cancel.
Qed.

Lemma node_split_b sh (vt vo va vb vc vd vl nd: val):
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd |--
  data_at sh tuint vb (field_address t_node [StructField _b] nd) * node_hole_b sh vt vo va vc vd vl nd.
Proof.
  unfold_data_at (data_at _ _ _ nd). rewrite (field_at_data_at sh t_node [StructField _b]).
  unfold node_hole_b. cancel.
Qed.

Lemma node_fold_b sh (vt vo va vb vc vd vl nd: val):
  data_at sh tuint vb (field_address t_node [StructField _b] nd) * node_hole_b sh vt vo va vc vd vl nd |--
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd.
Proof.
  unfold_data_at (data_at _ _ _ nd). rewrite (field_at_data_at sh t_node [StructField _b]).
  unfold node_hole_b. cancel.
Qed.

Lemma node_split_c sh (vt vo va vb vc vd vl nd: val):
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd |--
  data_at sh tuint vc (field_address t_node [StructField _c] nd) * node_hole_c sh vt vo va vb vd vl nd.
Proof.
  unfold_data_at (data_at _ _ _ nd). rewrite (field_at_data_at sh t_node [StructField _c]).
  unfold node_hole_c. cancel.
Qed.

Lemma node_fold_c sh (vt vo va vb vc vd vl nd: val):
  data_at sh tuint vc (field_address t_node [StructField _c] nd) * node_hole_c sh vt vo va vb vd vl nd |--
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd.
Proof.
  unfold_data_at (data_at _ _ _ nd). rewrite (field_at_data_at sh t_node [StructField _c]).
  unfold node_hole_c. cancel.
Qed.

Lemma node_split_d sh (vt vo va vb vc vd vl nd: val):
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd |--
  data_at sh tuint vd (field_address t_node [StructField _d] nd) * node_hole_d sh vt vo va vb vc vl nd.
Proof.
  unfold_data_at (data_at _ _ _ nd). rewrite (field_at_data_at sh t_node [StructField _d]).
  unfold node_hole_d. cancel.
Qed.

Lemma node_fold_d sh (vt vo va vb vc vd vl nd: val):
  data_at sh tuint vd (field_address t_node [StructField _d] nd) * node_hole_d sh vt vo va vb vc vl nd |--
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd.
Proof.
  unfold_data_at (data_at _ _ _ nd). rewrite (field_at_data_at sh t_node [StructField _d]).
  unfold node_hole_d. cancel.
Qed.

(* struct vx_fn: arity, nslots, decides, name_off, name_len, nnodes, root, nodes *)
Definition fn_hole_off sh (v0 v1 v2 v4 v5 v6 v7 fp: val) : mpred :=
  field_at sh t_fn [StructField _arity] v0 fp * field_at sh t_fn [StructField _nslots] v1 fp *
  field_at sh t_fn [StructField _decides] v2 fp * field_at sh t_fn [StructField _name_len] v4 fp *
  field_at sh t_fn [StructField _nnodes] v5 fp * field_at sh t_fn [StructField _root] v6 fp *
  field_at sh t_fn [StructField _nodes] v7 fp * spacer sh 28 32 fp.

Lemma fn_split_off sh (v0 v1 v2 v3 v4 v5 v6 v7 fp: val):
  data_at sh t_fn (v0, (v1, (v2, (v3, (v4, (v5, (v6, v7))))))) fp |--
  data_at sh tuint v3 (field_address t_fn [StructField _name_off] fp) * fn_hole_off sh v0 v1 v2 v4 v5 v6 v7 fp.
Proof.
  unfold_data_at (data_at _ _ _ fp). rewrite (field_at_data_at sh t_fn [StructField _name_off]).
  unfold fn_hole_off. cancel.
Qed.

Lemma fn_fold_off sh (v0 v1 v2 v3 v4 v5 v6 v7 fp: val):
  data_at sh tuint v3 (field_address t_fn [StructField _name_off] fp) * fn_hole_off sh v0 v1 v2 v4 v5 v6 v7 fp |--
  data_at sh t_fn (v0, (v1, (v2, (v3, (v4, (v5, (v6, v7))))))) fp.
Proof.
  unfold_data_at (data_at _ _ _ fp). rewrite (field_at_data_at sh t_fn [StructField _name_off]).
  unfold fn_hole_off. cancel.
Qed.

(* The same, forgetting the old value of the field (the readers overwrite it). *)
Lemma node_take_a sh (vt vo va vb vc vd vl nd: val):
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd |--
  data_at_ sh tuint (field_address t_node [StructField _a] nd) * node_hole_a sh vt vo vb vc vd vl nd.
Proof. sep_apply node_split_a. cancel. Qed.
Lemma node_take_b sh (vt vo va vb vc vd vl nd: val):
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd |--
  data_at_ sh tuint (field_address t_node [StructField _b] nd) * node_hole_b sh vt vo va vc vd vl nd.
Proof. sep_apply node_split_b. cancel. Qed.
Lemma node_take_c sh (vt vo va vb vc vd vl nd: val):
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd |--
  data_at_ sh tuint (field_address t_node [StructField _c] nd) * node_hole_c sh vt vo va vb vd vl nd.
Proof. sep_apply node_split_c. cancel. Qed.
Lemma node_take_d sh (vt vo va vb vc vd vl nd: val):
  data_at sh t_node (vt, (vo, (va, (vb, (vc, (vd, vl)))))) nd |--
  data_at_ sh tuint (field_address t_node [StructField _d] nd) * node_hole_d sh vt vo va vb vc vl nd.
Proof. sep_apply node_split_d. cancel. Qed.
Lemma fn_take_off sh (v0 v1 v2 v3 v4 v5 v6 v7 fp: val):
  data_at sh t_fn (v0, (v1, (v2, (v3, (v4, (v5, (v6, v7))))))) fp |--
  data_at_ sh tuint (field_address t_fn [StructField _name_off] fp) * fn_hole_off sh v0 v1 v2 v4 v5 v6 v7 fp.
Proof. sep_apply fn_split_off. cancel. Qed.
