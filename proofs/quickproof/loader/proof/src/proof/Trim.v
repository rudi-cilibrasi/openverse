(* Bodies of trim_args and trim_bytes. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
#[local] Existing Instance Specs.CS.

Lemma token_data_test: forall t q v P,
  (malloc_token Ews t q * data_at Ews t v q * P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)))%logic.
Proof.
  intros. sep_apply (data_at_data_at_ Ews t v q). assert_PROP (isptr q) as Pq by entailer!.
  eapply derives_trans; [ | apply (malloc_test_null t q P) ].
  - rewrite if_false by (intro E; subst; contradiction). cancel.
  - pose proof (sizeof_pos t). lia.
Qed.

Lemma u32_ok_Znth: forall l i, u32_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l <= Int.max_unsigned.
Proof. intros. apply (proj1 (Forall_Znth _ _) H); auto. Qed.

Lemma upd_copy: forall (l: list Z) i, 0 <= i < Zlength l ->
  upd_Znth i (vints (sublist 0 i l) ++ Zrepeat Vundef (Zlength l - i)) (Vint (Int.repr (Znth i l))) =
  vints (sublist 0 (i + 1) l) ++ Zrepeat Vundef (Zlength l - (i + 1))%Z.
Proof. intros. unfold vints. list_solve. Qed.

Lemma body_trim_args: semax_body Vprog Gprog f_trim_args trim_args_spec.
Proof.
  start_function.
  unfold args_pool. Intros.
  assert_PROP (isptr args) as Pa by entailer!.
  forward.
  forward_if.
  - assert (al = []) by (apply Zlength_nil_inv; lia). subst al.
    forward.
    forward_if (PROP () LOCAL (temp _p p; gvars gv)
      SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength (@nil Z)) bytes nb) p; mem_mgr gv))%assert.
    + forward.
      sep_apply (data_at_data_at_ Ews (tarray tuint acap) (vints [] ++ Zrepeat Vundef (acap - Zlength (@nil Z))) args).
      forward_call (tarray tuint acap, args, gv).
      { rewrite if_false by (intro E; subst; contradiction). cancel. }
      entailer!.
    + exfalso; first [ discriminate | (subst; contradiction) | auto ].
    + forward. forward. Exists 0 nullval. rewrite if_true by reflexivity. unfold args_final. rewrite if_true by reflexivity. entailer!.
  - forward.
    forward_call (tarray tuint (Zlength al), gv).
    { entailer!. simpl. pose proof (Zlength_nonneg al). rewrite Z.max_r by lia. do 3 f_equal. lia. }
    { simpl. pose proof (Zlength_nonneg al). rewrite Z.max_r by lia. rep_lia. }
    Intros a.
    forward.
    forward_if.
    + apply derives_trans with ((if eq_dec a nullval then emp else
        malloc_token Ews (tarray tuint (Zlength al)) a * data_at_ Ews (tarray tuint (Zlength al)) a) * TT)%logic;
        [ cancel | apply malloc_test_null; simpl; rep_lia ].
    + forward. Exists 20 args. rewrite if_false by lia. unfold args_pool. entailer!.
    + rewrite if_false by auto. Intros.
      rewrite data_at__tarray.
      forward.
      forward_loop (EX i: Z,
        PROP (0 <= i <= Zlength al)
        LOCAL (temp _i (Vint (Int.repr i)); temp _a a; temp _p p; gvars gv)
        SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p;
             malloc_token Ews (tarray tuint acap) args;
             data_at Ews (tarray tuint acap) (vints al ++ Zrepeat Vundef (acap - Zlength al)) args;
             malloc_token Ews (tarray tuint (Zlength al)) a;
             data_at Ews (tarray tuint (Zlength al)) (vints (sublist 0 i al) ++ Zrepeat Vundef (Zlength al - i)) a;
             mem_mgr gv))%assert
      continue: (EX i: Z,
        PROP (0 <= i < Zlength al)
        LOCAL (temp _i (Vint (Int.repr i)); temp _a a; temp _p p; gvars gv)
        SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p;
             malloc_token Ews (tarray tuint acap) args;
             data_at Ews (tarray tuint acap) (vints al ++ Zrepeat Vundef (acap - Zlength al)) args;
             malloc_token Ews (tarray tuint (Zlength al)) a;
             data_at Ews (tarray tuint (Zlength al))
               (vints (sublist 0 (i + 1) al) ++ Zrepeat Vundef (Zlength al - (i + 1)))%Z a;
             mem_mgr gv))%assert
      break: (PROP ()
        LOCAL (temp _a a; temp _p p; gvars gv)
        SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p;
             malloc_token Ews (tarray tuint acap) args;
             data_at Ews (tarray tuint acap) (vints al ++ Zrepeat Vundef (acap - Zlength al)) args;
             malloc_token Ews (tarray tuint (Zlength al)) a;
             data_at Ews (tarray tuint (Zlength al)) (vints al) a;
             mem_mgr gv))%assert.
      * Exists 0.
        replace (vints (sublist 0 0 al) ++ Zrepeat Vundef (Zlength al - 0)) with (Zrepeat (default_val tuint) (Zlength al))
          by (rewrite sublist_nil; simpl; f_equal; lia).
        entailer!.
      * Intros i. forward. forward_if.
        -- assert (B := u32_ok_Znth al i H0 ltac:(lia)).
           forward. forward.
           { entailer!. rewrite Znth_app1 by (rewrite Zlength_vints; lia). rewrite Znth_vints by lia. auto. }
           rewrite Znth_app1 by (rewrite Zlength_vints; lia). rewrite Znth_vints by lia.
           forward.
           Exists i. rewrite upd_copy by lia. entailer!.
        -- forward. assert (i = Zlength al) by lia. subst i.
           rewrite sublist_same by lia. rewrite Z.sub_diag, Zrepeat_0, app_nil_r. entailer!.
      * Intros i. forward. Exists (i + 1). entailer!.
      * forward.
        forward_if (PROP () LOCAL (temp _a a; temp _p p; gvars gv)
          SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p;
               malloc_token Ews (tarray tuint (Zlength al)) a;
               data_at Ews (tarray tuint (Zlength al)) (vints al) a; mem_mgr gv))%assert.
        -- forward.
           sep_apply (data_at_data_at_ Ews (tarray tuint acap) (vints al ++ Zrepeat Vundef (acap - Zlength al)) args).
           forward_call (tarray tuint acap, args, gv).
           { rewrite if_false by (intro E; subst; contradiction). cancel. }
           entailer!.
        -- exfalso; first [ discriminate | (subst; contradiction) | auto ].
        -- forward. forward. Exists 0 a. rewrite if_true by reflexivity. unfold args_final. rewrite if_false by lia. entailer!.
Qed.

Lemma body_trim_bytes: semax_body Vprog Gprog f_trim_bytes trim_bytes_spec.
Proof.
  start_function.
  unfold bytes_pool. Intros.
  assert_PROP (isptr bytes) as Pa by entailer!.
  forward.
  forward_if.
  - assert (bl = []) by (apply Zlength_nil_inv; lia). subst bl.
    forward.
    forward_if (PROP () LOCAL (temp _p p; gvars gv)
      SEP (data_at Tsh t_prog (PRG nfns entry fns args na bytes (Zlength (@nil Z))) p; mem_mgr gv))%assert.
    + forward.
      sep_apply (data_at_data_at_ Ews (tarray tuchar bcap) (vints [] ++ Zrepeat Vundef (bcap - Zlength (@nil Z))) bytes).
      forward_call (tarray tuchar bcap, bytes, gv).
      { rewrite if_false by (intro E; subst; contradiction). cancel. }
      entailer!.
    + exfalso; first [ discriminate | (subst; contradiction) | auto ].
    + forward. forward. Exists 0 nullval. rewrite if_true by reflexivity. unfold bytes_final. rewrite if_true by reflexivity. entailer!.
  - forward.
    forward_call (tarray tuchar (Zlength bl), gv).
    { simpl. pose proof (Zlength_nonneg bl). rewrite Z.max_r by lia. rep_lia. }
    Intros b.
    forward.
    forward_if.
    + apply derives_trans with ((if eq_dec b nullval then emp else
        malloc_token Ews (tarray tuchar (Zlength bl)) b * data_at_ Ews (tarray tuchar (Zlength bl)) b) * TT)%logic;
        [ cancel | apply malloc_test_null; simpl; rep_lia ].
    + forward. Exists 20 bytes. rewrite if_false by lia. unfold bytes_pool. entailer!.
    + rewrite if_false by auto. Intros.
      rewrite data_at__tarray.
      forward.
      forward_loop (EX i: Z,
        PROP (0 <= i <= Zlength bl)
        LOCAL (temp _i (Vint (Int.repr i)); temp _b b; temp _p p; gvars gv)
        SEP (data_at Tsh t_prog (PRG nfns entry fns args na bytes (Zlength bl)) p;
             malloc_token Ews (tarray tuchar bcap) bytes;
             data_at Ews (tarray tuchar bcap) (vints bl ++ Zrepeat Vundef (bcap - Zlength bl)) bytes;
             malloc_token Ews (tarray tuchar (Zlength bl)) b;
             data_at Ews (tarray tuchar (Zlength bl)) (vints (sublist 0 i bl) ++ Zrepeat Vundef (Zlength bl - i)) b;
             mem_mgr gv))%assert
      continue: (EX i: Z,
        PROP (0 <= i < Zlength bl)
        LOCAL (temp _i (Vint (Int.repr i)); temp _b b; temp _p p; gvars gv)
        SEP (data_at Tsh t_prog (PRG nfns entry fns args na bytes (Zlength bl)) p;
             malloc_token Ews (tarray tuchar bcap) bytes;
             data_at Ews (tarray tuchar bcap) (vints bl ++ Zrepeat Vundef (bcap - Zlength bl)) bytes;
             malloc_token Ews (tarray tuchar (Zlength bl)) b;
             data_at Ews (tarray tuchar (Zlength bl))
               (vints (sublist 0 (i + 1) bl) ++ Zrepeat Vundef (Zlength bl - (i + 1)))%Z b;
             mem_mgr gv))%assert
      break: (PROP ()
        LOCAL (temp _b b; temp _p p; gvars gv)
        SEP (data_at Tsh t_prog (PRG nfns entry fns args na bytes (Zlength bl)) p;
             malloc_token Ews (tarray tuchar bcap) bytes;
             data_at Ews (tarray tuchar bcap) (vints bl ++ Zrepeat Vundef (bcap - Zlength bl)) bytes;
             malloc_token Ews (tarray tuchar (Zlength bl)) b;
             data_at Ews (tarray tuchar (Zlength bl)) (vints bl) b;
             mem_mgr gv))%assert.
      * Exists 0.
        replace (vints (sublist 0 0 bl) ++ Zrepeat Vundef (Zlength bl - 0)) with (Zrepeat (default_val tuchar) (Zlength bl))
          by (rewrite sublist_nil; simpl; f_equal; lia).
        entailer!.
      * Intros i. forward. forward_if.
        -- assert (B := bytes_ok_Znth bl i H0 ltac:(lia)).
           forward. forward.
           { entailer!. rewrite Znth_app1 by (rewrite Zlength_vints; lia). rewrite Znth_vints by lia.
             simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
           rewrite Znth_app1 by (rewrite Zlength_vints; lia). rewrite Znth_vints by lia.
           forward.
           Exists i.
           rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
           rewrite upd_copy by lia. entailer!.
        -- forward. assert (i = Zlength bl) by lia. subst i.
           rewrite sublist_same by lia. rewrite Z.sub_diag, Zrepeat_0, app_nil_r. entailer!.
      * Intros i. forward. Exists (i + 1). entailer!.
      * forward.
        forward_if (PROP () LOCAL (temp _b b; temp _p p; gvars gv)
          SEP (data_at Tsh t_prog (PRG nfns entry fns args na bytes (Zlength bl)) p;
               malloc_token Ews (tarray tuchar (Zlength bl)) b;
               data_at Ews (tarray tuchar (Zlength bl)) (vints bl) b; mem_mgr gv))%assert.
        -- forward.
           sep_apply (data_at_data_at_ Ews (tarray tuchar bcap) (vints bl ++ Zrepeat Vundef (bcap - Zlength bl)) bytes).
           forward_call (tarray tuchar bcap, bytes, gv).
           { rewrite if_false by (intro E; subst; contradiction). cancel. }
           entailer!.
        -- exfalso; first [ discriminate | (subst; contradiction) | auto ].
        -- forward. forward. Exists 0 b. rewrite if_true by reflexivity. unfold bytes_final. rewrite if_false by lia. entailer!.
Qed.
