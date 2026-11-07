(* Body of load_lit. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import OpenverseLoader.load.code.
Require Import OpenverseLoader.proof.Specs.
Require Import OpenverseLoader.proof.Lemmas.
Require Import OpenverseLoader.proof.Fields.
Require Import OpenverseLoader.proof.NodeLemmas.
#[local] Existing Instance Specs.CS.

Lemma body_load_lit: semax_body Vprog Gprog f_load_lit load_lit_spec.
Proof.
  start_function. pre_props.
  unfold node_val; cbn [n_tag n_op n_a n_b n_c n_d n_lit].
  set (z := Vint (Int.repr 0)).
  set (l0 := Vlong (Int64.repr 0)).
  forward_call (r, buf, shb, bs, pos, acap, bcap, v_kind, Tsh).
  Intros vret. destruct vret as [[[rc1 p1] k] vk]. cbn [fst snd] in *.
  forward_if.
  { forward. Exists 1 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  use_rc0.
  forward.
  forward_if.
  { forward. Exists 16 p1 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
  forward. forward.
  forward.
  forward_if (EX lit: Z, EX pos': Z,
    PROP (0 <= pos' <= Zlength bs; Int64.min_signed <= lit <= Int64.max_signed; (k = 1 -> lit = 0 \/ lit = 1))
    LOCAL (lvar _i tlong v_i; lvar _x tuint v_x; lvar _kind tuint v_kind; temp _r r; temp _p p; temp _nd nd)
    SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
         data_at_ Tsh tuint v_kind; data_at_ Tsh tlong v_i; data_at_ Tsh tuint v_x;
         data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
         args_pool args acap al; bytes_pool bytes bcap bl;
         data_at Ews t_node (z, (Vint (Int.repr k), (z, (z, (z, (z, Vlong (Int64.repr lit))))))) nd))%assert.
  - (* INT *)
    forward_call (r, buf, shb, bs, p1, acap, bcap, v_i, Tsh).
    Intros vret. destruct vret as [[[rc2 p2] xi] vi]. cbn [fst snd] in *.
    forward_if.
    { forward. Exists 1 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
      rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
    use_rc0.
    forward. forward. Exists xi p2. entailer!.
  - forward.
    forward_if (EX lit: Z, EX pos': Z,
      PROP (0 <= pos' <= Zlength bs; Int64.min_signed <= lit <= Int64.max_signed; (k = 1 -> lit = 0 \/ lit = 1))
      LOCAL (lvar _i tlong v_i; lvar _x tuint v_x; lvar _kind tuint v_kind; temp _r r; temp _p p; temp _nd nd)
      SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
           data_at_ Tsh tuint v_kind; data_at_ Tsh tlong v_i; data_at_ Tsh tuint v_x;
           data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
           args_pool args acap al; bytes_pool bytes bcap bl;
           data_at Ews t_node (z, (Vint (Int.repr k), (z, (z, (z, (z, Vlong (Int64.repr lit))))))) nd))%assert.
    + (* LOGIC *)
      forward_call (r, buf, shb, bs, p1, acap, bcap, v_x, Tsh).
      Intros vret. destruct vret as [[[rc2 p2] xb] vb]. cbn [fst snd] in *.
      forward_if.
      { forward. Exists 1 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
        rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
      use_rc0.
      forward.
      forward_if.
      { forward. Exists 17 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
        rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
      forward. forward. Exists xb p2.
      rewrite Int.unsigned_repr by rep_lia. entailer!.
    + forward.
      forward_if (EX lit: Z, EX pos': Z,
        PROP (0 <= pos' <= Zlength bs; Int64.min_signed <= lit <= Int64.max_signed; (k = 1 -> lit = 0 \/ lit = 1))
        LOCAL (lvar _i tlong v_i; lvar _x tuint v_x; lvar _kind tuint v_kind; temp _r r; temp _p p; temp _nd nd)
        SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
             data_at_ Tsh tuint v_kind; data_at_ Tsh tlong v_i; data_at_ Tsh tuint v_x;
             data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
             args_pool args acap al; bytes_pool bytes bcap bl;
             data_at Ews t_node (z, (Vint (Int.repr k), (z, (z, (z, (z, Vlong (Int64.repr lit))))))) nd))%assert.
      * (* CHAR *)
        forward_call (r, buf, shb, bs, p1, acap, bcap, v_x, Tsh).
        Intros vret. destruct vret as [[[rc2 p2] xb] vb]. cbn [fst snd] in *.
        forward_if.
        { forward. Exists 1 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
          rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
        use_rc0.
        forward. forward. Exists xb p2.
        rewrite Int.unsigned_repr by rep_lia. entailer!.
      * forward.
        forward_if (EX lit: Z, EX pos': Z,
          PROP (0 <= pos' <= Zlength bs; Int64.min_signed <= lit <= Int64.max_signed; (k = 1 -> lit = 0 \/ lit = 1))
          LOCAL (lvar _i tlong v_i; lvar _x tuint v_x; lvar _kind tuint v_kind; temp _r r; temp _p p; temp _nd nd)
          SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
               data_at_ Tsh tuint v_kind; data_at_ Tsh tlong v_i; data_at_ Tsh tuint v_x;
               data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
               args_pool args acap al; bytes_pool bytes bcap bl;
               data_at Ews t_node (z, (Vint (Int.repr k), (z, (z, (z, (z, Vlong (Int64.repr lit))))))) nd))%assert.
        -- (* STR *)
           forward_call (r, buf, shb, bs, p1, acap, bcap, v_x, Tsh).
           Intros vret. destruct vret as [[[rc2 p2] xs] vs]. cbn [fst snd] in *.
           forward_if.
           { forward. Exists 1 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
             rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
           use_rc0.
           forward. forward. forward.
           match goal with H: k = 3 |- _ => subst k end.
           assert_PROP (field_compatible t_node [] nd) as FC by entailer!.
           assert (FCa: field_compatible t_node (DOT _a) nd) by auto with field_compatible.
           sep_apply (node_take_a Ews z (Vint (Int.repr 3)) z (Vint (Int.repr xs)) z z l0 nd).
           forward_call (r, buf, shb, bs, p2, acap, bcap, p, nfns, entry, fns, args, Zlength al, bytes, bl, xs,
                         field_address t_node [StructField _a] nd, Ews).
           { cancel. }
           Intros vret. destruct vret as [[[rc3 p3] bl'] va]. cbn [fst snd] in *.
           sep_apply (node_fold_a Ews z (Vint (Int.repr 3)) va (Vint (Int.repr xs)) z z l0 nd).
           forward.
           Exists rc3 p3 (@nil Z) bl' (mkN 0 3 (Zlength bl) xs 0 0 0). ex_node nd.
           rewrite app_nil_r. entailer!.
           unfold node_post_props. rewrite Zlength_nil, app_nil_r.
           split; [ lia | ]. split; [ lia | ]. split; [ lia | ]. split; [ constructor | ].
           split; [ lia | ]. split; [ auto | ].
           intros E. subst rc3.
           match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [Hlen' Hva]; clear H end.
           subst va. split; [ reflexivity | node_ok_tac ].
        -- forward.
           forward_if (EX lit: Z, EX pos': Z,
             PROP (0 <= pos' <= Zlength bs; Int64.min_signed <= lit <= Int64.max_signed; (k = 1 -> lit = 0 \/ lit = 1))
             LOCAL (lvar _i tlong v_i; lvar _x tuint v_x; lvar _kind tuint v_kind; temp _r r; temp _p p; temp _nd nd)
             SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
                  data_at_ Tsh tuint v_kind; data_at_ Tsh tlong v_i; data_at_ Tsh tuint v_x;
                  data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
                  args_pool args acap al; bytes_pool bytes bcap bl;
                  data_at Ews t_node (z, (Vint (Int.repr k), (z, (z, (z, (z, Vlong (Int64.repr lit))))))) nd))%assert.
           ++ (* REF *)
              forward_call (r, buf, shb, bs, p1, acap, bcap, v_x, Tsh).
              Intros vret. destruct vret as [[[rc2 p2] xr] vr]. cbn [fst snd] in *.
              forward_if.
              { forward. Exists 1 p2 (@nil Z) bl (mkN 0 0 0 0 0 0 0). ex_node nd.
                rewrite app_nil_r. entailer!. apply npp_err; auto; lia. }
              use_rc0.
              forward. forward. Exists xr p2.
              rewrite Int.unsigned_repr by rep_lia. entailer!.
           ++ forward. Exists 0 p1. entailer!.
  - Intros lit pos'. forward.
    Exists 0 pos' (@nil Z) bl (mkN 0 k 0 0 0 0 lit). ex_node nd.
    rewrite app_nil_r. entailer!. apply npp_ok; auto; try lia.
    intros _. split; [ reflexivity | node_ok_tac ].
Qed.
