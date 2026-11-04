(* Bodies of load_all and vx_load. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
Require Import OpenverseLoader.proof.LoadLemmas.
#[local] Existing Instance Specs.CS.

Lemma shl_1_26: Int.shl (Int.repr 1) (Int.repr 26) = Int.repr 67108864.
Proof. reflexivity. Qed.

Lemma fns_rep_fold: forall fns n F, Zlength F = n ->
  (malloc_token Ews (tarray t_fn n) fns * farr n (map fn_val F) fns * iter_sepcon nodes_rep F
   |-- fns_rep fns F)%logic.
Proof. intros. subst n. unfold fns_rep, farr. cancel. Qed.

Lemma body_load_all: semax_body Vprog Gprog f_load_all load_all_spec.
Proof.
  start_function.
  forward.
  forward_if.
  { forward. Exists 19 (LD buf (Zlength bs) 0 0 0). rewrite if_false by lia.
    sep_apply (freeable_PRG0 p). entailer!. }
  rewrite ?shl_1_26 in *. simpl_ints.
  pose proof (Zlength_nonneg bs).
  assert (HL: Zlength bs <= MAXIN) by lia.
  forward_call (r, buf, shb, bs, 0, p, gv).
  all: try (solve [ repeat split; auto; rep_lia ]).
  Intros vret. destruct vret as [[[rc pos1] acap] bcap]. cbn [fst snd] in *.
  forward_if.
  { rewrite if_false by auto. forward. Exists rc (LD buf (Zlength bs) pos1 acap bcap).
    rewrite if_false by auto. entailer!. }
  subst rc. rewrite if_true by auto. Intros nfns entry fns args bytes.
  rewrite farr_fold.
  forward.
  forward_loop (EX f: Z, EX pos': Z, EX al: list Z, EX bl: list Z, EX Fd: list fnr,
    PROP (0 <= f <= nfns; Zlength Fd = f; Forall (fn_ok nfns al (Zlength bl)) Fd;
          Zlength al <= acap; Zlength bl <= bcap; u32_ok al; bytes_ok bl; 0 <= pos' <= Zlength bs)
    LOCAL (temp _f (Vint (Int.repr f)); temp _r r; temp _p p; gvars gv)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
         data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
         args_pool args acap al; bytes_pool bytes bcap bl;
         malloc_token Ews (tarray t_fn nfns) fns;
         farr nfns (map fn_val Fd ++ Zrepeat (fn_val zero_fn) (nfns - f)) fns;
         iter_sepcon nodes_rep Fd; mem_mgr gv))%assert
  continue: (EX f: Z, EX pos': Z, EX al: list Z, EX bl: list Z, EX Fd: list fnr,
    PROP (0 <= f < nfns; Zlength Fd = (f + 1)%Z; Forall (fn_ok nfns al (Zlength bl)) Fd;
          Zlength al <= acap; Zlength bl <= bcap; u32_ok al; bytes_ok bl; 0 <= pos' <= Zlength bs)
    LOCAL (temp _f (Vint (Int.repr f)); temp _r r; temp _p p; gvars gv)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
         data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
         args_pool args acap al; bytes_pool bytes bcap bl;
         malloc_token Ews (tarray t_fn nfns) fns;
         farr nfns (map fn_val Fd ++ Zrepeat (fn_val zero_fn) (nfns - (f + 1))%Z) fns;
         iter_sepcon nodes_rep Fd; mem_mgr gv))%assert
  break: (EX pos': Z, EX al: list Z, EX bl: list Z, EX Fd: list fnr,
    PROP (Zlength Fd = nfns; Forall (fn_ok nfns al (Zlength bl)) Fd;
          Zlength al <= acap; Zlength bl <= bcap; u32_ok al; bytes_ok bl; 0 <= pos' <= Zlength bs)
    LOCAL (temp _r r; temp _p p; gvars gv)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
         data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
         args_pool args acap al; bytes_pool bytes bcap bl;
         malloc_token Ews (tarray t_fn nfns) fns;
         farr nfns (map fn_val Fd) fns;
         iter_sepcon nodes_rep Fd; mem_mgr gv))%assert.
  - Exists 0 pos1 (@nil Z) (@nil Z) (@nil fnr).
    replace (map fn_val [] ++ Zrepeat (fn_val zero_fn) (nfns - 0)) with (Zrepeat (fn_val zero_fn) nfns)
      by (rewrite Z.sub_0_r; reflexivity).
    rewrite !Zlength_nil.
    entailer!.
    all: try (split; [ constructor | ]); try rep_lia; try constructor.
  - Intros f pos' al bl Fd.
    match goal with H: Zlength Fd = f |- _ => subst f end.
    forward.
    forward_if.
    2: { forward. Exists pos' al bl Fd. replace (nfns - Zlength Fd) with 0 by lia. rewrite Zrepeat_0, app_nil_r.
         entailer!. }
    assert_PROP (field_compatible (tarray t_fn nfns) [] fns) as FCf by entailer!.
    unfold farr.
    sep_apply (SingletonHole.array_with_hole_intro Ews t_fn (Zlength Fd) nfns
                 (map fn_val Fd ++ Zrepeat (fn_val zero_fn) (nfns - Zlength Fd)) fns ltac:(lia)).
    Intros.
    rewrite Znth_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map.
    replace (Zlength Fd - Zlength Fd) with 0 by lia. rewrite Znth_Zrepeat by lia.
    forward_call (r, buf, shb, bs, pos', acap, bcap, p, nfns, entry, fns, args, al, bytes, bl, Zlength Fd, gv).
    all: try (solve [ repeat split; auto; rep_lia ]).
    all: try (solve [ cancel ]).
    Intros vret. destruct vret as [[[[[[rc2 pos2] xs] bl2] x] fv] k]. cbn [fst snd] in *.
    sep_apply (SingletonHole.array_with_hole_elim Ews t_fn (Zlength Fd) nfns fv
                 (map fn_val Fd ++ Zrepeat (fn_val zero_fn) (nfns - Zlength Fd)) fns).
    rewrite farr_fold.
    forward_if.
    + rewrite if_false by auto. forward. Exists rc2 (LD buf (Zlength bs) pos2 acap bcap).
      rewrite if_false by auto.
      sep_apply (args_pool_blk args acap (al ++ xs)). sep_apply (bytes_pool_blk bytes bcap bl2).
      sep_apply (freeable_partial p nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl2) Fd (Zlength Fd) fv k
                   acap bcap ltac:(lia) ltac:(rep_lia) ltac:(lia)).
      entailer!.
    + subst rc2. rewrite if_true by auto.
      match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [-> Hok]; clear H end.
      try forward.
      Exists (Zlength Fd) pos2 (al ++ xs) bl2 (Fd ++ [x]).
      replace (upd_Znth (Zlength Fd) (map fn_val Fd ++ Zrepeat (fn_val zero_fn) (nfns - Zlength Fd)) (fn_val x))
        with (map fn_val (Fd ++ [x]) ++ Zrepeat (fn_val zero_fn) (nfns - (Zlength Fd + 1))).
      2: { rewrite upd_fill_map by lia. f_equal. f_equal. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      rewrite iter_sepcon_app. simpl iter_sepcon. rewrite sepcon_emp.
      entailer!.
      repeat match goal with |- _ /\ _ => split end.
      all: try (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil in *; rep_lia).
      all: try (solve [ apply Forall_app; split;
                  [ eapply Forall_impl; [ | eassumption ]; intros; eapply fn_ok_mono; eauto; lia
                  | constructor; auto ] ]).
      all: try (solve [ apply Forall_app; split; auto ]).
      all: auto.
  - Intros f pos' al bl Fd. forward. Exists (f + 1) pos' al bl Fd. entailer!.
  - Intros pos' al bl Fd. subst nfns.
    forward. forward.
    forward_if.
    { forward. Exists 18 (LD buf (Zlength bs) pos' acap bcap). rewrite if_false by lia.
      sep_apply (args_pool_blk args acap al). sep_apply (bytes_pool_blk bytes bcap bl).
      sep_apply (freeable_loaded p (Zlength Fd) entry fns args (Zlength al) bytes (Zlength bl) Fd acap bcap
                   ltac:(rep_lia) ltac:(auto)).
      entailer!. }
    sep_apply (fns_rep_fold fns (Zlength Fd) Fd ltac:(auto)).
    forward_call (p, (Zlength Fd), entry, fns, args, al, bytes, Zlength bl, Fd).
    all: try (solve [ repeat split; auto; rep_lia ]).
    Intros rc3.
    unfold fns_rep. rewrite farr_fold.
    forward_if.
    { forward. Exists rc3 (LD buf (Zlength bs) pos' acap bcap). rewrite if_false by lia.
      sep_apply (args_pool_blk args acap al). sep_apply (bytes_pool_blk bytes bcap bl).
      sep_apply (freeable_loaded p (Zlength Fd) entry fns args (Zlength al) bytes (Zlength bl) Fd acap bcap
                   ltac:(rep_lia) ltac:(auto)).
      entailer!. }
    match goal with H: rc3 = 0 \/ rc3 = 12 |- _ => destruct H as [ -> | -> ]; [ | exfalso; auto ] end.
    forward_call (p, (Zlength Fd), entry, fns, args, acap, al, bytes, Zlength bl, gv).
    all: try (solve [ repeat split; auto; rep_lia ]).
    Intros vret. destruct vret as [rc4 args']. cbn [fst snd] in *.
    forward_if.
    { rewrite if_false by auto. Intros. subst args'. forward.
      Exists rc4 (LD buf (Zlength bs) pos' acap bcap). rewrite if_false by auto.
      sep_apply (args_pool_blk args acap al). sep_apply (bytes_pool_blk bytes bcap bl).
      sep_apply (freeable_loaded p (Zlength Fd) entry fns args (Zlength al) bytes (Zlength bl) Fd acap bcap
                   ltac:(rep_lia) ltac:(auto)).
      entailer!. }
    subst rc4. rewrite if_true by auto.
    forward_call (p, (Zlength Fd), entry, fns, args', Zlength al, bytes, bcap, bl, gv).
    all: try (solve [ repeat split; auto; rep_lia ]).
    Intros vret. destruct vret as [rc5 bytes']. cbn [fst snd] in *.
    forward.
    Exists rc5 (LD buf (Zlength bs) pos' acap bcap).
    destruct (Z.eq_dec rc5 0) as [E5 | N5].
    + try (rewrite !if_true by auto). unfold prog_rep. Exists (Zlength Fd) entry fns args' bytes' al bl Fd.
      unfold fns_rep, farr.
      entailer!.
      unfold prog_ok. repeat split; auto; try rep_lia.
      all: try (match goal with H: 0 = 0 -> _ |- _ => apply H; auto end).
    + try (rewrite !if_false by auto). Intros. subst bytes'.
      sep_apply (args_final_blk args' al). sep_apply (bytes_pool_blk bytes bcap bl).
      sep_apply (freeable_loaded p (Zlength Fd) entry fns args' (Zlength al) bytes (Zlength bl) Fd (Zlength al) bcap
                   ltac:(rep_lia) ltac:(auto)).
      entailer!.
      all: try lia.
Qed.

Lemma body_vx_load: semax_body Vprog Gprog f_vx_load vx_load_spec.
Proof.
  start_function.
  forward. forward. forward. forward. forward.
  forward_call (out).
  forward_call (v_r, buf, shb, bs, out, gv).
  all: try (solve [ repeat split; auto; rep_lia ]).
  Intros vret. destruct vret as [rc rv]. cbn [fst snd] in *.
  forward_if (PROP () LOCAL (temp _rc (Vint (Int.repr rc)); lvar _r t_ld v_r; gvars gv; temp _out out)
     SEP (data_at Tsh t_ld rv v_r; buf_rep shb bs buf; mem_mgr gv;
          if Z.eq_dec rc 0 then prog_rep out else data_at Tsh t_prog PRG0 out))%assert.
  - rewrite if_false by auto. forward_call (out, gv). rewrite if_false by auto. entailer!.
  - forward. subst rc. rewrite !if_true by auto. entailer!.
  - forward. Exists rc. entailer!.
Qed.
