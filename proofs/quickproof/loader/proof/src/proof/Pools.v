(* Bodies of rd_bytes and rd_args, which append to the pools. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
#[local] Existing Instance Specs.CS.

Lemma body_rd_bytes: semax_body Vprog Gprog f_rd_bytes rd_bytes_spec.
Proof.
  start_function.
  forward_if.
  { forward. Exists 19 pos bl (default_val tuint). unfold data_at_. entailer!. }
  forward. forward.
  forward_if.
  { forward. Exists 1 pos bl (default_val tuint). unfold data_at_. entailer!. }
  forward. forward.
  forward_if.
  { forward. Exists 19 pos bl (default_val tuint). unfold data_at_. entailer!. }
  rewrite shl_1_24 in *. simpl_ints.
  forward. forward.
  unfold bytes_pool. Intros.
  forward_for_simple_bound n (EX i: Z,
    PROP ()
    LOCAL (temp _r r; temp _p p; temp _n (Vint (Int.repr n)); temp _off off)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
         data_at Tsh t_prog (PRG nfns entry fns args nargs bytes (Zlength bl)) p;
         malloc_token Ews (tarray tuchar bcap) bytes;
         data_at Ews (tarray tuchar bcap)
           (vints (bl ++ sublist pos (pos + i) bs) ++ Zrepeat Vundef (bcap - Zlength (bl ++ sublist pos (pos + i) bs))) bytes;
         data_at sho tuint (Vint (Int.repr (Zlength bl))) off))%assert.
  - entailer!. rewrite sublist_nil, app_nil_r. auto.
  - buf_nonnull.
    assert (Bk := bytes_ok_Znth bs (pos + i) H ltac:(lia)).
    forward. forward. forward. forward. forward.
    { entailer!. rewrite Znth_vints by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_vints by lia.
    forward.
    { entailer!. }
    assert (EL: Zlength (bl ++ sublist pos (pos + i) bs) = Zlength bl + i)
      by (rewrite Zlength_app, Zlength_sublist by lia; lia).
    rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
    rewrite <- EL, upd_fill by lia.
    replace ((bl ++ sublist pos (pos + i) bs) ++ [Znth (pos + i) bs]) with (bl ++ sublist pos (pos + (i + 1)) bs).
    2: { rewrite <- app_assoc. f_equal. rewrite (sublist_split pos (pos + i) (pos + (i + 1))) by lia.
         replace (pos + (i + 1)) with (pos + i + 1) by lia.
         rewrite sublist_len_1 by lia. reflexivity. }
    entailer!. rewrite buf_rep_nonnull by auto. cancel.
  - forward. forward. forward. forward. forward.
    Exists 0 (pos + n) (bl ++ sublist pos (pos + n) bs) (Vint (Int.repr (Zlength bl))).
    assert (EL: Zlength (bl ++ sublist pos (pos + n) bs) = Zlength bl + n)
      by (rewrite Zlength_app, Zlength_sublist by lia; lia).
    unfold bytes_pool. rewrite !EL.
    apply andp_right.
    + apply prop_right. split; [ lia | ]. split; [ lia | ]. split; [ lia | ]. split.
      { apply bytes_ok_app; auto. apply bytes_ok_sublist; auto. }
      split; [ auto | reflexivity ].
    + cancel.
Qed.

Lemma body_rd_args: semax_body Vprog Gprog f_rd_args rd_args_spec.
Proof.
  start_function.
  forward_if.
  { forward. Exists 19 pos (@nil Z) (default_val tuint). rewrite app_nil_r. unfold data_at_. entailer!. }
  rewrite shl_1_16 in *. simpl_ints.
  forward. forward.
  forward_for_simple_bound n (EX k: Z, EX pos': Z, EX xs: list Z,
    PROP (Zlength xs = k; 0 <= pos' <= Zlength bs; Zlength al + k <= acap; Forall (fun x => 0 <= x < j) xs)
    LOCAL (temp _r r; temp _p p; temp _j (Vint (Int.repr j)); temp _n (Vint (Int.repr n)); temp _off off;
           lvar _x tuint v_x)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
         data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes nbytes) p;
         args_pool args acap (al ++ xs); data_at sho tuint (Vint (Int.repr (Zlength al))) off;
         data_at_ Tsh tuint v_x))%assert.
  - Exists pos (@nil Z). rewrite app_nil_r. entailer!.
  - cbv beta. Intros pos' xs.
    forward_call (r, buf, shb, bs, pos', acap, bcap, j, v_x, Tsh).
    Intros vret. destruct vret as [[[rc pos''] x] v]. cbn [fst snd] in *.
    forward_if.
    + forward. Exists rc pos'' xs (Vint (Int.repr (Zlength al))). entailer!.
    + subst rc. match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [-> Hx] end.
      assert (EA: Zlength (al ++ xs) = Zlength al + i) by (rewrite Zlength_app; lia).
      forward. forward.
      forward_if.
      * forward. Exists 19 pos'' xs (Vint (Int.repr (Zlength al))). entailer!.
      * simpl_ints. rewrite EA in *.
        unfold args_pool. Intros.
        forward. forward. forward. forward.
        { entailer!. }
        forward. forward.
        Exists pos'' (xs ++ [x]).
        rewrite <- EA, upd_fill by lia. rewrite <- app_assoc.
        unfold args_pool.
        entailer!.
        { split; [ rewrite Zlength_app; reflexivity | apply Forall_app; split; auto ]. }
        { assert (E2: Zlength (al ++ xs ++ [x]) = Zlength (al ++ xs) + 1)
            by (rewrite !Zlength_app, Zlength_cons, Zlength_nil; lia).
          rewrite E2. cancel. }
  - Intros pos' xs. forward. Exists 0 pos' xs (Vint (Int.repr (Zlength al))). entailer!.
Qed.
