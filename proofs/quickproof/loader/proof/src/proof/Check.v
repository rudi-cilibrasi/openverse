(* Body of check_calls. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
#[local] Existing Instance Specs.CS.

Lemma nodes_rep_ptr: forall x, isptr (f_q x) ->
  nodes_rep x = (malloc_token Ews (tarray t_node (Zlength (f_body x))) (f_q x) *
                 data_at Ews (tarray t_node (Zlength (f_body x))) (map node_val (f_body x)) (f_q x))%logic.
Proof. intros. unfold nodes_rep. rewrite if_false; auto. intro E; rewrite E in H; contradiction. Qed.


Lemma Znth_any: forall {A} (d d': Inhabitant A) i (l: list A), 0 <= i < Zlength l ->
  @Znth A d i l = @Znth A d' i l.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0); [ lia | ]. apply nth_indep.
  rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma body_check_calls: semax_body Vprog Gprog f_check_calls check_calls_spec.
Proof.
  start_function.
  unfold fns_rep. Intros.
  forward.
  forward_loop (EX f: Z,
    PROP (0 <= f <= nfns; forall f', 0 <= f' < f -> Forall (call_ok F) (f_body (Znth f' F)))
    LOCAL (temp _f (Vint (Int.repr f)); temp _p p)
    SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p;
         malloc_token Ews (tarray t_fn (Zlength F)) fns; data_at Ews (tarray t_fn (Zlength F)) (map fn_val F) fns;
         iter_sepcon nodes_rep F))%assert
  continue: (EX f: Z,
    PROP (0 <= f < nfns; forall f', 0 <= f' < f + 1 -> Forall (call_ok F) (f_body (Znth f' F)))
    LOCAL (temp _f (Vint (Int.repr f)); temp _p p)
    SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p;
         malloc_token Ews (tarray t_fn (Zlength F)) fns; data_at Ews (tarray t_fn (Zlength F)) (map fn_val F) fns;
         iter_sepcon nodes_rep F))%assert
  break: (PROP (forall f', 0 <= f' < nfns -> Forall (call_ok F) (f_body (Znth f' F)))
    LOCAL (temp _p p)
    SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p;
         malloc_token Ews (tarray t_fn (Zlength F)) fns; data_at Ews (tarray t_fn (Zlength F)) (map fn_val F) fns;
         iter_sepcon nodes_rep F))%assert.
  - Exists 0. entailer!; try (intros; lia).
  - Intros f. forward. forward_if.
    + forward.
      assert (OKf: fn_ok nfns al nb (Znth f F)) by (match goal with H: Forall (fn_ok _ _ _) F |- _ => apply (proj1 (Forall_Znth _ _) H); lia end).
      set (x := Znth f F) in *.
      destruct OKf as (Ok1 & Ok2 & Ok3 & Ok4 & Ok5 & Ok6 & Ok7 & Ok8 & Ok9 & Ok10).
      rewrite (iter_sepcon_Znth nodes_rep F f) by lia. fold x.
      rewrite (nodes_rep_ptr x) by auto. Intros.
      assert_PROP (field_compatible (tarray t_node (Zlength (f_body x))) [] (f_q x)) as FCq by entailer!.
      forward_loop (EX j: Z,
        PROP (0 <= j <= Zlength (f_body x); forall j', 0 <= j' < j -> call_ok F (Znth j' (f_body x)))
        LOCAL (temp _j (Vint (Int.repr j)); temp _f (Vint (Int.repr f)); temp _p p)
        SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p;
             malloc_token Ews (tarray t_fn (Zlength F)) fns; data_at Ews (tarray t_fn (Zlength F)) (map fn_val F) fns;
             iter_sepcon nodes_rep (remove_Znth f F);
             malloc_token Ews (tarray t_node (Zlength (f_body x))) (f_q x);
             data_at Ews (tarray t_node (Zlength (f_body x))) (map node_val (f_body x)) (f_q x)))%assert
      continue: (EX j: Z,
        PROP (0 <= j < Zlength (f_body x); forall j', 0 <= j' < j + 1 -> call_ok F (Znth j' (f_body x)))
        LOCAL (temp _j (Vint (Int.repr j)); temp _f (Vint (Int.repr f)); temp _p p)
        SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p;
             malloc_token Ews (tarray t_fn (Zlength F)) fns; data_at Ews (tarray t_fn (Zlength F)) (map fn_val F) fns;
             iter_sepcon nodes_rep (remove_Znth f F);
             malloc_token Ews (tarray t_node (Zlength (f_body x))) (f_q x);
             data_at Ews (tarray t_node (Zlength (f_body x))) (map node_val (f_body x)) (f_q x)))%assert
      break: (PROP (Forall (call_ok F) (f_body x))
        LOCAL (temp _f (Vint (Int.repr f)); temp _p p)
        SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p;
             malloc_token Ews (tarray t_fn (Zlength F)) fns; data_at Ews (tarray t_fn (Zlength F)) (map fn_val F) fns;
             iter_sepcon nodes_rep (remove_Znth f F);
             malloc_token Ews (tarray t_node (Zlength (f_body x))) (f_q x);
             data_at Ews (tarray t_node (Zlength (f_body x))) (map node_val (f_body x)) (f_q x)))%assert.
      * Exists 0. entailer!; try (intros; lia).
      * Intros j.
        assert (EF: forall d, @Znth _ d f (map fn_val F) = fn_val x).
        { intros d. rewrite Znth_map by lia. reflexivity. }
        forward. forward.
        { entailer!. rewrite EF. simpl. auto. }
        rewrite EF. unfold fn_val at 1. cbn [fst snd].
        forward_if.
        2: { forward. entailer!. apply Forall_forall. intros y Hy. apply In_Znth in Hy.
             destruct Hy as (i & Hi & <-).
             match goal with H: forall j', 0 <= j' < _ -> call_ok F _ |- _ => apply H; lia end. }
        forward. forward.
        { entailer!. rewrite EF. simpl. auto. }
        rewrite EF. unfold fn_val at 1. cbn [fst snd].
        forward.
        rewrite (add_ptr_uint_field t_node (Zlength (f_body x)) j (f_q x)) by (auto; rep_lia).
        set (ndp := field_address (tarray t_node (Zlength (f_body x))) [ArraySubsc j] (f_q x)).
        sep_apply (SingletonHole.array_with_hole_intro Ews t_node j (Zlength (f_body x))
                     (map node_val (f_body x)) (f_q x) ltac:(lia)).
        Intros. rewrite Znth_map by lia.
        set (y := Znth j (f_body x)).
        assert (Ey: node_val y = (Vint (Int.repr (n_tag y)), (Vint (Int.repr (n_op y)), (Vint (Int.repr (n_a y)),
          (Vint (Int.repr (n_b y)), (Vint (Int.repr (n_c y)), (Vint (Int.repr (n_d y)), Vlong (Int64.repr (n_lit y)))))))))
          by reflexivity.
        rewrite Ey.
        assert (NOK: node_ok nfns (f_nslots x) al nb j y) by (apply Ok10; lia).
        destruct NOK as (W & T & N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
        destruct W as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
        forward.
        forward_if (temp _t'1 (Vint (Int.repr (if Z.eq_dec (n_tag y) 5 then
                       (if Z.eq_dec (f_arity (Znth (n_a y) F)) (n_b y) then 0 else 1) else 0)))).
        { destruct (N5 ltac:(auto)) as [Na _].
          assert (OKa: fn_ok nfns al nb (Znth (n_a y) F)) by (match goal with H: Forall (fn_ok _ _ _) F |- _ => apply (proj1 (Forall_Znth _ _) H); lia end).
          destruct OKa as (A1 & A2 & _).
          assert (EA: forall d, @Znth _ d (n_a y) (map fn_val F) = fn_val (Znth (n_a y) F)).
          { intros d. rewrite Znth_map by lia. reflexivity. }
          forward. forward. forward.
          { entailer!. rewrite EA. simpl. auto. }
          rewrite EA. unfold fn_val at 1. cbn [fst snd].
          forward. forward.
          entailer!. rewrite if_true by auto.
          destruct (Z.eq_dec (f_arity (Znth (n_a y) F)) (n_b y)), (zeq (f_arity (Znth (n_a y) F)) (n_b y));
            simpl; try congruence; auto. }
        { forward. entailer!. rewrite if_false by auto. auto. }
        forward_if.
        { forward. Exists 12.
          sep_apply (SingletonHole.array_with_hole_elim Ews t_node j (Zlength (f_body x))
            (Vint (Int.repr (n_tag y)), (Vint (Int.repr (n_op y)), (Vint (Int.repr (n_a y)),
             (Vint (Int.repr (n_b y)), (Vint (Int.repr (n_c y)), (Vint (Int.repr (n_d y)), Vlong (Int64.repr (n_lit y))))))))
            (map node_val (f_body x)) (f_q x)).
          rewrite upd_Znth_triv by (rewrite ?Zlength_map; try lia; rewrite Znth_map by lia; reflexivity).
          unfold fns_rep. rewrite (iter_sepcon_Znth nodes_rep F f) by lia. fold x.
          rewrite (nodes_rep_ptr x) by auto. entailer!. }
        try forward.
        Exists j.
        sep_apply (SingletonHole.array_with_hole_elim Ews t_node j (Zlength (f_body x))
          (Vint (Int.repr (n_tag y)), (Vint (Int.repr (n_op y)), (Vint (Int.repr (n_a y)),
           (Vint (Int.repr (n_b y)), (Vint (Int.repr (n_c y)), (Vint (Int.repr (n_d y)), Vlong (Int64.repr (n_lit y))))))))
          (map node_val (f_body x)) (f_q x)).
        rewrite upd_Znth_triv by (rewrite ?Zlength_map; try lia; rewrite Znth_map by lia; reflexivity).
        entailer!.
        intros j' Hj'. destruct (zeq j' j).
        { subst j'. fold y. unfold call_ok. intros E5.
          destruct (Z.eq_dec (n_tag y) 5); [ | contradiction ].
          destruct (Z.eq_dec (f_arity (Znth (n_a y) F)) (n_b y)); auto.
          exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
        match goal with H: forall j', 0 <= j' < j -> call_ok F _ |- _ => apply H; lia end.
      * Intros j. forward. Exists (j + 1). entailer!.
      * Exists f. rewrite (iter_sepcon_Znth nodes_rep F f) by lia. fold x.
        rewrite (nodes_rep_ptr x) by auto. entailer!.
        intros f' Hf'. destruct (zeq f' f); [ subst f'; auto | ].
        match goal with H: forall f', 0 <= f' < f -> Forall _ _ |- _ => apply H; lia end.
    + forward. entailer!. intros f' Hf'.
      match goal with H: forall f', 0 <= f' < f -> Forall _ _ |- _ => apply H; lia end.
  - Intros f. forward. Exists (f + 1). entailer!.
  - forward. Exists 0. entailer!.
    all: repeat match goal with |- _ /\ _ => split end.
    all: try (left; reflexivity).
    all: try (intros _).
    all: try (apply Forall_forall; intros y Hy; apply In_Znth in Hy; destruct Hy as (i & Hi & <-);
              match goal with H: forall f', 0 <= f' < _ -> Forall _ _ |- _ => apply H; lia end).
    all: try (unfold fns_rep; cancel).
Qed.
