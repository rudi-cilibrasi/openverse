(* The law's program and the state of main's loop.

   whole_prog' is built exactly as whole_prog in src/contracts/store_rollback_model.v (the same
   tactic on the same units), so the two are convertible; main is proved here for whole_prog'.
   The program has the composites of store.c and no others, so the store unit's compspecs serve
   as the law's (the contract's harness_safe_by_specs checks this by computation). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Export QuickProof.Env.
Require QuickProof.Link.
Require OpenverseStore.units.Store.
Require OpenverseStore.harness.store_rollback_model.code.
Require Export OpenverseStore.proof.StoreSpecs.
Require Export OpenverseStore.proof.Tac.
Require Export OpenverseStore.harness.store_rollback_model.code.

Module Harness.
  #[local] Instance CS : compspecs. make_compspecs OpenverseStore.harness.store_rollback_model.code.prog. Defined.
  Definition qp := ltac:(QPprog OpenverseStore.harness.store_rollback_model.code.prog).
End Harness.

Definition whole_prog' := ltac:(QPlink_progs Harness.qp Store.qp).

Definition Vmain : varspecs := QPvarspecs whole_prog'.

(* What main calls. *)
Definition Gmain : funspecs :=
  [vx_store_init_spec; vx_store_get_spec; vx_store_set_spec; vx_store_mark_spec;
   vx_store_rollback_spec; vx_store_commit_spec; vx_store_out_append_spec; vx_store_out_len_spec;
   nondet_size_spec; nondet_u8_spec; nondet_bytes_spec; gp_assume_spec; gp_assert_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec')].

Definition Delta_main : tycontext := func_tycontext f_main Vmain Gmain nil.

(* ---------------------------------------------------------------------- *)
(* The state of main's loop.                                               *)
(* ---------------------------------------------------------------------- *)

(* What stays fixed: the globals, the sizes, the three buffers and main's locals. *)
Record menv := mkE {
  e_gv: globals; e_ns: Z; e_jcap: Z; e_ocap: Z; e_sp: val; e_jp: val; e_op: val;
  e_st: val; e_marks: val; e_mtag: val; e_mbits: val; e_mout: val; e_ctag: val; e_cbits: val;
  e_cout: val; e_colen: val; e_cjlen: val; e_tg: val; e_bt: val; e_bs: val; e_v: val; e_v1: val }.

#[export] Instance snap_inh : Inhabitant snap := mksnap [] [] 0.

(* What changes: the model (vs, js, os), the open contexts S (outermost first) and the contents of
   main's arrays. *)
Record mstate := mkM {
  m_vs: list V; m_js: list J; m_os: list Z; m_S: list snap;
  m_mk: list (reptype t_mark); m_mt: list val; m_mb: list val; m_mo: list val;
  m_ct: list (list val); m_cb: list (list val); m_co: list (list val); m_cl: list val; m_cj: list val }.

Definition tagv (v: V) : val := Vlong (fst v).
Definition bitv (v: V) : val := Vlong (snd v).

(* Context d (0 = outermost) as main's arrays record it. *)
Record snap_ok (ns: Z) (st: mstate) (d: Z) : Prop := {
  s_vs: Zlength (sn_vs (Znth d (m_S st))) = ns;
  s_os: Zlength (sn_os (Znth d (m_S st))) <= 8;
  s_j: 0 <= sn_j (Znth d (m_S st));
  s_bytes: Forall (fun b => 0 <= b <= Byte.max_unsigned) (sn_os (Znth d (m_S st)));
  s_mk: Znth d (m_mk st) = mval (sn_j (Znth d (m_S st))) (Zlength (sn_os (Znth d (m_S st)))) d;
  s_ct: sublist 0 ns (Znth d (m_ct st)) = map tagv (sn_vs (Znth d (m_S st)));
  s_cb: sublist 0 ns (Znth d (m_cb st)) = map bitv (sn_vs (Znth d (m_S st)));
  s_co: sublist 0 (Zlength (sn_os (Znth d (m_S st)))) (Znth d (m_co st)) = bytes (sn_os (Znth d (m_S st)));
  s_cl: Znth d (m_cl st) = Vlong (Int64.repr (Zlength (sn_os (Znth d (m_S st)))));
  s_cj: Znth d (m_cj st) = Vlong (Int64.repr (sn_j (Znth d (m_S st))))
}.

Record inv_ok (E: menv) (st: mstate) : Prop := {
  i_ns: 0 <= e_ns E <= 4;
  i_jcap: 0 <= e_jcap E <= 8;
  i_ocap: 0 <= e_ocap E <= 8;
  i_vs: Zlength (m_vs st) = e_ns E;
  i_js: Zlength (m_js st) <= e_jcap E;
  i_os: Zlength (m_os st) <= e_ocap E;
  i_S: Zlength (m_S st) <= 3;
  i_bytes: Forall (fun b => 0 <= b <= Byte.max_unsigned) (m_os st);
  i_chain: chain (m_js st) (m_vs st) (m_os st) (rev (m_S st));
  i_mt_len: Zlength (m_mt st) = 4;
  i_mt: sublist 0 (e_ns E) (m_mt st) = map tagv (m_vs st);
  i_mb_len: Zlength (m_mb st) = 4;
  i_mb: sublist 0 (e_ns E) (m_mb st) = map bitv (m_vs st);
  i_mo_len: Zlength (m_mo st) = 8;
  i_mo: sublist 0 (Zlength (m_os st)) (m_mo st) = bytes (m_os st);
  i_mk_len: Zlength (m_mk st) = 3;
  i_ct_len: Zlength (m_ct st) = 3;
  i_cb_len: Zlength (m_cb st) = 3;
  i_co_len: Zlength (m_co st) = 3;
  i_cl_len: Zlength (m_cl st) = 3;
  i_cj_len: Zlength (m_cj st) = 3;
  i_ct_rows: Forall (fun r => Zlength r = 4) (m_ct st);
  i_cb_rows: Forall (fun r => Zlength r = 4) (m_cb st);
  i_co_rows: Forall (fun r => Zlength r = 8) (m_co st);
  i_snaps: forall d, 0 <= d < Zlength (m_S st) -> snap_ok (e_ns E) st d
}.

Definition mtok (t: type) (q: val) : mpred :=
  if eq_dec q nullval then emp else malloc_token Ews t q.

(* The state at an iteration of the loop, with k its counter.  MLOC and MSEP take the parts
   that change separately, so that the loops inside a step can use them too. *)
Definition MLOC (E: menv) (molen mjlen depth: Z) : list localdef :=
  [temp _molen (Vlong (Int64.repr molen));
   temp _mjlen (Vlong (Int64.repr mjlen));
   temp _depth (Vlong (Int64.repr depth));
   temp _nslots (Vlong (Int64.repr (e_ns E)));
   temp _jcap (Vlong (Int64.repr (e_jcap E)));
   temp _ocap (Vlong (Int64.repr (e_ocap E)));
   temp _slots (e_sp E); temp _jour (e_jp E); temp _out (e_op E);
   lvar _st t_store (e_st E); lvar _marks (tarray t_mark 3) (e_marks E);
   lvar _mtag (tarray tulong 4) (e_mtag E); lvar _mbits (tarray tulong 4) (e_mbits E);
   lvar _mout (tarray tuchar 8) (e_mout E);
   lvar _ctag (tarray (tarray tulong 4) 3) (e_ctag E);
   lvar _cbits (tarray (tarray tulong 4) 3) (e_cbits E);
   lvar _cout (tarray (tarray tuchar 8) 3) (e_cout E);
   lvar _colen (tarray tulong 3) (e_colen E); lvar _cjlen (tarray tulong 3) (e_cjlen E);
   lvar _tg tulong (e_tg E); lvar _bt tulong (e_bt E); lvar _bs (tarray tuchar 2) (e_bs E);
   lvar _v t_val (e_v E); lvar _v__1 t_val (e_v1 E);
   gvars (e_gv E)].

Definition MSEP (E: menv) (vs: list V) (js: list J) (olen depth: Z) (os: list Z)
    (mk: list (reptype t_mark)) (mt mb mo: list val) (ct cb co: list (list val)) (cl cj: list val)
    (Rbs: mpred) : list mpred :=
  [mem_mgr (e_gv E); has_ext tt;
   mtok (tarray t_val (e_ns E)) (e_sp E); mtok (tarray t_undo (e_jcap E)) (e_jp E);
   mtok (tarray tuchar (e_ocap E)) (e_op E);
   store_rep Tsh Ews (e_st E) (e_sp E) (e_jp E) (e_op E) (e_jcap E) (e_ocap E) vs js olen depth;
   out_rep Ews (e_ocap E) os (e_op E);
   data_at Tsh (tarray t_mark 3) mk (e_marks E);
   data_at Tsh (tarray tulong 4) mt (e_mtag E);
   data_at Tsh (tarray tulong 4) mb (e_mbits E);
   data_at Tsh (tarray tuchar 8) mo (e_mout E);
   data_at Tsh (tarray (tarray tulong 4) 3) ct (e_ctag E);
   data_at Tsh (tarray (tarray tulong 4) 3) cb (e_cbits E);
   data_at Tsh (tarray (tarray tuchar 8) 3) co (e_cout E);
   data_at Tsh (tarray tulong 3) cl (e_colen E);
   data_at Tsh (tarray tulong 3) cj (e_cjlen E);
   data_at_ Tsh tulong (e_tg E); data_at_ Tsh tulong (e_bt E);
   Rbs;
   data_at_ Tsh t_val (e_v E); data_at_ Tsh t_val (e_v1 E)].

Definition MSTk (E: menv) (k: Z) (st: mstate) : environ -> mpred :=
  PROPx [inv_ok E st]
   (LOCALx (temp _k (Vlong (Int64.repr k)) :: MLOC E (Zlength (m_os st)) (Zlength (m_js st)) (Zlength (m_S st)))
    (SEPx (MSEP E (m_vs st) (m_js st) (Zlength (m_os st)) (Zlength (m_S st)) (m_os st)
             (m_mk st) (m_mt st) (m_mb st) (m_mo st) (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)
             (data_at_ Tsh (tarray tuchar 2) (e_bs E))))).

(* The assertion PROPx P (LOCALx L (SEPx S)) with MLOC and MSEP unfolded, for loop invariants. *)
Ltac loop_inv P L S :=
  let I := eval cbv delta [MLOC MSEP] beta in (PROPx P (LOCALx L (SEPx S))) in exact I.

(* The state's own locals and memory, with extra facts P. *)
Ltac st_inv E k st P :=
  loop_inv P (temp _k (Vlong (Int64.repr k)) :: MLOC E (Zlength (m_os st)) (Zlength (m_js st)) (Zlength (m_S st)))
    (MSEP E (m_vs st) (m_js st) (Zlength (m_os st)) (Zlength (m_S st)) (m_os st)
       (m_mk st) (m_mt st) (m_mb st) (m_mo st) (m_ct st) (m_cb st) (m_co st) (m_cl st) (m_cj st)
       (data_at_ Tsh (tarray tuchar 2) (e_bs E))).

(* ---------------------------------------------------------------------- *)
(* The pieces of main's body that the step lemmas prove.                   *)
(* ---------------------------------------------------------------------- *)

Definition main_body : statement := ltac:(let b := eval cbv [f_main fn_body] in (fn_body f_main) in exact b).

Ltac grab_then n :=
  let b := eval cbv [main_body] in main_body in
  match b with
  | context [Sifthenelse (Ebinop Oeq (Etempvar _op tuchar) (Econst_int (Int.repr n) tint) tint) ?A _] =>
      exact A
  end.

Definition op0_stmt : statement := ltac:(grab_then 0).
Definition op1_stmt : statement := ltac:(grab_then 1).
Definition op2_stmt : statement := ltac:(grab_then 2).
Definition op3_stmt : statement := ltac:(grab_then 3).
Definition op4_stmt : statement := ltac:(grab_then 4).
Definition checks_stmt : statement := ltac:(
  let b := eval cbv [main_body] in main_body in
  match b with
  | context [Ssequence (Sifthenelse (Ebinop Oeq (Etempvar _op tuchar) (Econst_int (Int.repr 0) tint) tint) _ _) ?C] =>
      exact C
  end).

Definition body_stmt : statement := ltac:(
  let b := eval cbv [main_body] in main_body in
  match b with
  | context [Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _k tulong) (Econst_int (Int.repr 32) tint) tint)
                                Sskip Sbreak) ?B) _] => exact B
  end).

(* A body proved with a normal postcondition serves any postcondition it implies. *)
Lemma semax_normal_weak {Espec: OracleKind} Delta P c Q (R: ret_assert):
  @semax CS Espec Delta P c (normal_ret_assert Q) ->
  ENTAIL Delta, Q |-- RA_normal R ->
  @semax CS Espec Delta P c R.
Proof.
  intros H1 H2. eapply semax_post_flipped; [ exact H1 | exact H2 | | | ].
  - simpl RA_break. apply andp_left2. intro rho. apply prop_left. intros [].
  - simpl RA_continue. apply andp_left2. intro rho. apply prop_left. intros [].
  - intros. simpl RA_return. apply andp_left2. intro rho. apply prop_left. intros [].
Qed.
