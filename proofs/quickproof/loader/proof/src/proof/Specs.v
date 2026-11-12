(* Specifications of the functions of runtime/src/load.c (the OVBC loader), under the unit's compspecs.

   The specifications are about safety and the well-formedness that the law loader_wellscoped checks:
   the readers return "some value" with range facts only; the node and function loaders establish
   node_ok / fn_ok (the conditions of FORMAT.md that the forward pass checks); check_calls adds the
   arity half of condition 5 (call_ok); on an error every function leaves the program in a state that
   vx_free_program can release (freeable). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require OpenverseLoader.units.Load.
Require Import OpenverseLoader.load.code.

#[export] Instance CS : compspecs := OpenverseLoader.units.Load.CS.
Definition Vprog : varspecs. mk_varspecs OpenverseLoader.load.code.prog. Defined.

Notation t_ld := (Tstruct _vx_ld noattr).
Notation t_node := (Tstruct _vx_node noattr).
Notation t_fn := (Tstruct _vx_fn noattr).
Notation t_prog := (Tstruct _vx_program noattr).

Notation MAXIN := 67108864%Z.   (* VX_MAX_INPUT = 2^26 *)

Definition vints (l: list Z) : list val := map (fun x => Vint (Int.repr x)) l.
Definition bytes_ok (l: list Z) : Prop := Forall (fun b => 0 <= b <= Byte.max_unsigned) l.
Definition u32_ok (l: list Z) : Prop := Forall (fun b => 0 <= b <= Int.max_unsigned) l.

(* struct vx_ld and struct vx_program as values *)
Notation LD buf len pos acap bcap :=
  (buf, (Vlong (Int64.repr len), (Vlong (Int64.repr pos), (Vlong (Int64.repr acap), Vlong (Int64.repr bcap))))).
Notation PRG nfns entry fns args nargs bytes nbytes :=
  (Vint (Int.repr nfns), (Vint (Int.repr entry), (fns, (args, (Vint (Int.repr nargs), (bytes, Vint (Int.repr nbytes))))))).
Notation PRG0 := (PRG 0 0 nullval nullval 0 nullval 0).

(* The input buffer: NULL only when empty (malloc(0) may return NULL). *)
Definition buf_rep (sh: share) (bs: list Z) (buf: val) : mpred :=
  (if eq_dec buf nullval then !! (bs = nil) && emp
  else data_at sh (tarray tuchar (Zlength bs)) (vints bs) buf)%logic.

(* ------------------------------------------------------------------ nodes *)

Record node := mkN { n_tag: Z; n_op: Z; n_a: Z; n_b: Z; n_c: Z; n_d: Z; n_lit: Z }.

Definition node_val (x: node) : reptype t_node :=
  (Vint (Int.repr (n_tag x)), (Vint (Int.repr (n_op x)), (Vint (Int.repr (n_a x)), (Vint (Int.repr (n_b x)),
   (Vint (Int.repr (n_c x)), (Vint (Int.repr (n_d x)), Vlong (Int64.repr (n_lit x)))))))).

#[export] Instance Inhabitant_node : Inhabitant node := mkN 0 0 0 0 0 0 0.

Definition node_wf (x: node) : Prop :=
  0 <= n_tag x <= Int.max_unsigned /\ 0 <= n_op x <= Int.max_unsigned /\ 0 <= n_a x <= Int.max_unsigned /\
  0 <= n_b x <= Int.max_unsigned /\ 0 <= n_c x <= Int.max_unsigned /\ 0 <= n_d x <= Int.max_unsigned /\
  Int64.min_signed <= n_lit x <= Int64.max_signed.

(* The argument list of a PRIM, CALL or HEAP node j lies in the args pool and names nodes < j. *)
Definition args_ok (al: list Z) (j: Z) (x: node) : Prop :=
  n_b x <= Zlength al /\ n_c x <= Zlength al - n_b x /\
  forall k, 0 <= k < n_b x -> Znth (n_c x + k) al < j.

(* Node j of a function with nslots slots, in a program of nfns functions whose pools hold al and nb bytes:
   what the forward pass checks (conditions 3, 4, 6 and the first half of 5). *)
Definition node_ok (nfns nslots: Z) (al: list Z) (nb: Z) (j: Z) (x: node) : Prop :=
  node_wf x /\ n_tag x <= 12 /\
  (n_tag x = 0 -> n_op x <= 6 /\ (n_op x = 1 -> n_lit x = 0 \/ n_lit x = 1) /\
                  (n_op x = 3 -> n_b x <= nb /\ n_a x <= nb - n_b x)) /\
  (n_tag x = 1 -> n_a x < nslots) /\
  (n_tag x = 2 -> n_a x < nslots /\ n_b x < j) /\
  (n_tag x = 3 -> n_a x < j /\ n_b x < j) /\
  (n_tag x = 4 -> n_op x <= 69 /\ (n_a x = 0 \/ n_op x = 25) /\ args_ok al j x) /\
  (n_tag x = 5 -> n_a x < nfns /\ args_ok al j x) /\
  (n_tag x = 6 -> n_a x < j /\ n_b x < j /\ n_c x < j) /\
  (n_tag x = 7 -> n_a x < nslots /\ n_b x < j /\ n_c x < j /\ n_d x < j) /\
  (n_tag x = 8 \/ n_tag x = 10 \/ n_tag x = 11 -> n_a x < j) /\
  (n_tag x = 12 -> n_op x <= 4 /\ (n_a x = 0 \/ n_op x <> 3) /\ args_ok al j x /\
                   (n_op x = 4 -> n_d x <= 4194304 /\ 4 * n_d x <= nb /\ n_a x <= nb - 4 * n_d x)).

(* ------------------------------------------------------------- functions *)

Record fnr := mkF { f_arity: Z; f_nslots: Z; f_dec: Z; f_off: Z; f_len: Z; f_root: Z; f_q: val;
                    f_body: list node }.

Definition fn_val (x: fnr) : reptype t_fn :=
  (Vint (Int.repr (f_arity x)), (Vint (Int.repr (f_nslots x)), (Vint (Int.repr (f_dec x)),
   (Vint (Int.repr (f_off x)), (Vint (Int.repr (f_len x)), (Vint (Int.repr (Zlength (f_body x))),
   (Vint (Int.repr (f_root x)), f_q x))))))).

Definition zero_fn : fnr := mkF 0 0 0 0 0 0 nullval nil.
#[export] Instance Inhabitant_fnr : Inhabitant fnr := zero_fn.

Definition fn_ok (nfns: Z) (al: list Z) (nb: Z) (x: fnr) : Prop :=
  0 <= f_arity x <= f_nslots x /\ f_nslots x <= 65536 /\ 0 <= f_dec x <= Int.max_unsigned /\
  0 <= f_off x /\ 0 <= f_len x /\ f_off x + f_len x <= nb /\
  1 <= Zlength (f_body x) <= 4194304 /\ 0 <= f_root x < Zlength (f_body x) /\ isptr (f_q x) /\
  forall j, 0 <= j < Zlength (f_body x) -> node_ok nfns (f_nslots x) al nb j (Znth j (f_body x)).

(* The arity half of condition 5, established by check_calls. *)
Definition call_ok (F: list fnr) (x: node) : Prop :=
  n_tag x = 5 -> f_arity (Znth (n_a x) F) = n_b x.

(* The node table of a function. *)
Definition nodes_rep (x: fnr) : mpred :=
  (if eq_dec (f_q x) nullval then emp
  else malloc_token Ews (tarray t_node (Zlength (f_body x))) (f_q x) *
       data_at Ews (tarray t_node (Zlength (f_body x))) (map node_val (f_body x)) (f_q x))%logic.

(* The function table and the node tables. *)
Definition fns_rep (fns: val) (F: list fnr) : mpred :=
  (malloc_token Ews (tarray t_fn (Zlength F)) fns *
  data_at Ews (tarray t_fn (Zlength F)) (map fn_val F) fns *
  iter_sepcon nodes_rep F)%logic.

(* ----------------------------------------------------------------- pools *)

(* During the pass: the pools have their capacity; the first entries are filled. *)
Definition args_pool (args: val) (acap: Z) (al: list Z) : mpred :=
  (malloc_token Ews (tarray tuint acap) args *
  data_at Ews (tarray tuint acap) (vints al ++ Zrepeat Vundef (acap - Zlength al)) args)%logic.

Definition bytes_pool (bytes: val) (bcap: Z) (bl: list Z) : mpred :=
  (malloc_token Ews (tarray tuchar bcap) bytes *
  data_at Ews (tarray tuchar bcap) (vints bl ++ Zrepeat Vundef (bcap - Zlength bl)) bytes)%logic.

(* After the trims: exactly sized, NULL when empty. *)
Definition args_final (args: val) (al: list Z) : mpred :=
  (if Z.eq_dec (Zlength al) 0 then !! (args = nullval) && emp
  else malloc_token Ews (tarray tuint (Zlength al)) args *
       data_at Ews (tarray tuint (Zlength al)) (vints al) args)%logic.

Definition bytes_final (bytes: val) (bl: list Z) : mpred :=
  (if Z.eq_dec (Zlength bl) 0 then !! (bytes = nullval) && emp
  else malloc_token Ews (tarray tuchar (Zlength bl)) bytes *
       data_at Ews (tarray tuchar (Zlength bl)) (vints bl) bytes)%logic.

(* ------------------------------------------------------ program states *)

(* A program that vx_load accepted. *)
Definition prog_ok (nfns entry: Z) (F: list fnr) (al: list Z) (nb: Z) : Prop :=
  Zlength F = nfns /\ 1 <= nfns <= 65536 /\ 0 <= entry < nfns /\
  0 <= nb <= MAXIN /\ Zlength al <= MAXIN /\ u32_ok al /\
  Forall (fn_ok nfns al nb) F /\ Forall (fun x => Forall (call_ok F) (f_body x)) F.

Definition prog_rep (p: val) : mpred :=
  (EX nfns: Z, EX entry: Z, EX fns: val, EX args: val, EX bytes: val, EX al: list Z, EX bl: list Z,
  EX F: list fnr,
  !! (prog_ok nfns entry F al (Zlength bl) /\ bytes_ok bl) &&
  data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p *
  fns_rep fns F * args_final args al * bytes_final bytes bl)%logic.

(* A block that free can release, or NULL. *)
Definition blk (t: type) (q: val) : mpred :=
  (if eq_dec q nullval then emp else malloc_token Ews t q * data_at_ Ews t q)%logic.

Definition fn_nodes (v: reptype t_fn) : val := snd (snd (snd (snd (snd (snd (snd v)))))).

Definition fblk (x: reptype t_fn * Z) : mpred := blk (tarray t_node (snd x)) (fn_nodes (fst x)).

Definition fns_free (fns: val) (nfns: Z) (L: list (reptype t_fn * Z)) : mpred :=
  (if eq_dec fns nullval then emp
  else !! (Zlength L = nfns) && malloc_token Ews (tarray t_fn nfns) fns *
       data_at Ews (tarray t_fn nfns) (map fst L) fns * iter_sepcon fblk L)%logic.

(* What vx_free_program releases: a function table (with its node tables), the pools. *)
Definition freeable (p: val) : mpred :=
  (EX nfns: Z, EX ve: val, EX fns: val, EX args: val, EX vna: val, EX bytes: val, EX vnb: val,
  EX L: list (reptype t_fn * Z), EX ka: Z, EX kb: Z,
  !! (0 <= nfns <= Int.max_unsigned) &&
  data_at Tsh t_prog (Vint (Int.repr nfns), (ve, (fns, (args, (vna, (bytes, vnb)))))) p *
  fns_free fns nfns L * blk (tarray tuint ka) args * blk (tarray tuchar kb) bytes)%logic.

(* ------------------------------------------------------------- readers *)

Definition rd_u8_spec :=
 DECLARE _rd_u8
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z, out: val, sho: share
 PRE [ tptr t_ld, tptr tuint ]
   PROP (readable_share shb; writable_share sho; bytes_ok bs; 0 <= pos <= Zlength bs; Zlength bs <= MAXIN;
         0 <= acap <= MAXIN; 0 <= bcap <= MAXIN)
   PARAMS (r; out)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf; data_at_ sho tuint out)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX x: Z, EX v: val,
   PROP (rc = 0 \/ rc = 1; 0 <= pos' <= Zlength bs; rc = 0 -> v = Vint (Int.repr x) /\ 0 <= x <= 255)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf; data_at sho tuint v out).

Definition rd_u32_spec :=
 DECLARE _rd_u32
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z, out: val, sho: share
 PRE [ tptr t_ld, tptr tuint ]
   PROP (readable_share shb; writable_share sho; bytes_ok bs; 0 <= pos <= Zlength bs; Zlength bs <= MAXIN;
         0 <= acap <= MAXIN; 0 <= bcap <= MAXIN)
   PARAMS (r; out)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf; data_at_ sho tuint out)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX x: Z, EX v: val,
   PROP (rc = 0 \/ rc = 1; 0 <= pos' <= Zlength bs; rc = 0 -> v = Vint (Int.repr x) /\ 0 <= x <= Int.max_unsigned)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf; data_at sho tuint v out).

Definition rd_i64_spec :=
 DECLARE _rd_i64
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z, out: val, sho: share
 PRE [ tptr t_ld, tptr tlong ]
   PROP (readable_share shb; writable_share sho; bytes_ok bs; 0 <= pos <= Zlength bs; Zlength bs <= MAXIN;
         0 <= acap <= MAXIN; 0 <= bcap <= MAXIN)
   PARAMS (r; out)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf; data_at_ sho tlong out)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX x: Z, EX v: val,
   PROP (rc = 0 \/ rc = 1; 0 <= pos' <= Zlength bs;
         rc = 0 -> v = Vlong (Int64.repr x) /\ Int64.min_signed <= x <= Int64.max_signed)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf; data_at sho tlong v out).

Definition rd_bytes_spec :=
 DECLARE _rd_bytes
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z,
      p: val, nfns: Z, entry: Z, fns: val, args: val, nargs: Z, bytes: val, bl: list Z,
      n: Z, off: val, sho: share
 PRE [ tptr t_ld, tptr t_prog, tuint, tptr tuint ]
   PROP (readable_share shb; writable_share sho; bytes_ok bs; 0 <= pos <= Zlength bs; Zlength bs <= MAXIN;
         0 <= acap <= MAXIN; 0 <= bcap <= MAXIN; Zlength bl <= bcap; bytes_ok bl; 0 <= n <= Int.max_unsigned)
   PARAMS (r; p; Vint (Int.repr n); off)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args nargs bytes (Zlength bl)) p;
        bytes_pool bytes bcap bl; data_at_ sho tuint off)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX bl': list Z, EX v: val,
   PROP (rc = 0 \/ rc = 1 \/ rc = 19; 0 <= pos' <= Zlength bs; Zlength bl <= Zlength bl' <= bcap; bytes_ok bl';
         (rc = 0 -> Zlength bl' = Zlength bl + n /\ v = Vint (Int.repr (Zlength bl)))%Z)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args nargs bytes (Zlength bl')) p;
        bytes_pool bytes bcap bl'; data_at sho tuint v off).

Definition rd_child_spec :=
 DECLARE _rd_child
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z, j: Z, out: val, sho: share
 PRE [ tptr t_ld, tuint, tptr tuint ]
   PROP (readable_share shb; writable_share sho; bytes_ok bs; 0 <= pos <= Zlength bs; Zlength bs <= MAXIN;
         0 <= acap <= MAXIN; 0 <= bcap <= MAXIN; 0 <= j <= Int.max_unsigned)
   PARAMS (r; Vint (Int.repr j); out)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf; data_at_ sho tuint out)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX x: Z, EX v: val,
   PROP (rc = 0 \/ rc = 1 \/ rc = 9; 0 <= pos' <= Zlength bs; rc = 0 -> v = Vint (Int.repr x) /\ 0 <= x < j)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf; data_at sho tuint v out).

Definition rd_slot_spec :=
 DECLARE _rd_slot
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z, nslots: Z, out: val, sho: share
 PRE [ tptr t_ld, tuint, tptr tuint ]
   PROP (readable_share shb; writable_share sho; bytes_ok bs; 0 <= pos <= Zlength bs; Zlength bs <= MAXIN;
         0 <= acap <= MAXIN; 0 <= bcap <= MAXIN; 0 <= nslots <= Int.max_unsigned)
   PARAMS (r; Vint (Int.repr nslots); out)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf; data_at_ sho tuint out)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX x: Z, EX v: val,
   PROP (rc = 0 \/ rc = 1 \/ rc = 10; 0 <= pos' <= Zlength bs; rc = 0 -> v = Vint (Int.repr x) /\ 0 <= x < nslots)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf; data_at sho tuint v out).

Definition rd_args_spec :=
 DECLARE _rd_args
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z,
      p: val, nfns: Z, entry: Z, fns: val, args: val, al: list Z, bytes: val, nbytes: Z,
      j: Z, n: Z, off: val, sho: share
 PRE [ tptr t_ld, tptr t_prog, tuint, tuint, tptr tuint ]
   PROP (readable_share shb; writable_share sho; bytes_ok bs; 0 <= pos <= Zlength bs; Zlength bs <= MAXIN;
         0 <= acap <= MAXIN; 0 <= bcap <= MAXIN; Zlength al <= acap;
         0 <= j <= Int.max_unsigned; 0 <= n <= Int.max_unsigned)
   PARAMS (r; p; Vint (Int.repr j); Vint (Int.repr n); off)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nbytes) p;
        args_pool args acap al; data_at_ sho tuint off)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX xs: list Z, EX v: val,
   PROP (rc = 0 \/ rc = 1 \/ rc = 9 \/ rc = 19; 0 <= pos' <= Zlength bs; (Zlength al + Zlength xs <= acap)%Z;
         Forall (fun x => 0 <= x < j) xs;
         rc = 0 -> Zlength xs = n /\ v = Vint (Int.repr (Zlength al)))
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes nbytes) p;
        args_pool args acap (al ++ xs); data_at sho tuint v off).

(* --------------------------------------------------------- node loaders *)

Definition node_clear_spec :=
 DECLARE _node_clear
 WITH nd: val
 PRE [ tptr t_node ]
   PROP () PARAMS (nd) SEP (data_at_ Ews t_node nd)
 POST [ tvoid ]
   PROP () RETURN () SEP (data_at Ews t_node (node_val (mkN 0 0 0 0 0 0 0)) nd).

(* The common shape of the node loaders: node nd has its tag set and every other field 0. *)
Definition node_pre_props (shb: share) (bs: list Z) (pos acap bcap nfns entry: Z) (al bl: list Z)
    (nslots j: Z) : Prop :=
  readable_share shb /\ bytes_ok bs /\ 0 <= pos <= Zlength bs /\ Zlength bs <= MAXIN /\
  0 <= acap <= MAXIN /\ 0 <= bcap <= MAXIN /\ Zlength al <= acap /\ Zlength bl <= bcap /\
  bytes_ok bl /\ 0 <= nfns <= 65536 /\ 0 <= entry <= Int.max_unsigned /\
  0 <= nslots <= 65536 /\ 0 <= j < 4194304.

Definition node_post_props (bs: list Z) (acap bcap nfns: Z) (al bl: list Z) (nslots j: Z)
    (rc pos': Z) (xs bl': list Z) (x: node) (v: reptype t_node) : Prop :=
  0 <= rc <= 21 /\ 0 <= pos' <= Zlength bs /\ Zlength al + Zlength xs <= acap /\
  Forall (fun y => 0 <= y < j) xs /\ Zlength bl <= Zlength bl' <= bcap /\ bytes_ok bl' /\
  (rc = 0 -> v = node_val x /\ node_ok nfns nslots (al ++ xs) (Zlength bl') j x).

Definition load_lit_spec :=
 DECLARE _load_lit
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z,
      p: val, nfns: Z, entry: Z, fns: val, args: val, al: list Z, bytes: val, bl: list Z,
      nslots: Z, j: Z, nd: val
 PRE [ tptr t_ld, tptr t_prog, tptr t_node ]
   PROP (node_pre_props shb bs pos acap bcap nfns entry al bl nslots j)
   PARAMS (r; p; nd)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
        args_pool args acap al; bytes_pool bytes bcap bl;
        data_at Ews t_node (node_val (mkN 0 0 0 0 0 0 0)) nd)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX xs: list Z, EX bl': list Z, EX x: node, EX v: reptype t_node,
   PROP (node_post_props bs acap bcap nfns al bl nslots j rc pos' xs bl' x v)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl')) p;
        args_pool args acap (al ++ xs); bytes_pool bytes bcap bl';
        data_at Ews t_node v nd).

Definition load_prim_spec :=
 DECLARE _load_prim
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z,
      p: val, nfns: Z, entry: Z, fns: val, args: val, al: list Z, bytes: val, bl: list Z,
      nslots: Z, j: Z, nd: val
 PRE [ tptr t_ld, tptr t_prog, tuint, tptr t_node ]
   PROP (node_pre_props shb bs pos acap bcap nfns entry al bl nslots j)
   PARAMS (r; p; Vint (Int.repr j); nd)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
        args_pool args acap al; bytes_pool bytes bcap bl;
        data_at Ews t_node (node_val (mkN 4 0 0 0 0 0 0)) nd)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX xs: list Z, EX bl': list Z, EX x: node, EX v: reptype t_node,
   PROP (node_post_props bs acap bcap nfns al bl nslots j rc pos' xs bl' x v)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl')) p;
        args_pool args acap (al ++ xs); bytes_pool bytes bcap bl';
        data_at Ews t_node v nd).

Definition load_call_spec :=
 DECLARE _load_call
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z,
      p: val, nfns: Z, entry: Z, fns: val, args: val, al: list Z, bytes: val, bl: list Z,
      nslots: Z, j: Z, nd: val
 PRE [ tptr t_ld, tptr t_prog, tuint, tptr t_node ]
   PROP (node_pre_props shb bs pos acap bcap nfns entry al bl nslots j)
   PARAMS (r; p; Vint (Int.repr j); nd)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
        args_pool args acap al; bytes_pool bytes bcap bl;
        data_at Ews t_node (node_val (mkN 5 0 0 0 0 0 0)) nd)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX xs: list Z, EX bl': list Z, EX x: node, EX v: reptype t_node,
   PROP (node_post_props bs acap bcap nfns al bl nslots j rc pos' xs bl' x v)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl')) p;
        args_pool args acap (al ++ xs); bytes_pool bytes bcap bl';
        data_at Ews t_node v nd).

(* HEAP: the tags of an isTag go into the bytes pool, as a string literal's bytes do. *)
Definition load_heap_spec :=
 DECLARE _load_heap
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z,
      p: val, nfns: Z, entry: Z, fns: val, args: val, al: list Z, bytes: val, bl: list Z,
      nslots: Z, j: Z, nd: val
 PRE [ tptr t_ld, tptr t_prog, tuint, tptr t_node ]
   PROP (node_pre_props shb bs pos acap bcap nfns entry al bl nslots j)
   PARAMS (r; p; Vint (Int.repr j); nd)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
        args_pool args acap al; bytes_pool bytes bcap bl;
        data_at Ews t_node (node_val (mkN 12 0 0 0 0 0 0)) nd)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX xs: list Z, EX bl': list Z, EX x: node, EX v: reptype t_node,
   PROP (node_post_props bs acap bcap nfns al bl nslots j rc pos' xs bl' x v)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl')) p;
        args_pool args acap (al ++ xs); bytes_pool bytes bcap bl';
        data_at Ews t_node v nd).

Definition load_three_spec :=
 DECLARE _load_three
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z,
      p: val, nfns: Z, entry: Z, fns: val, args: val, al: list Z, bytes: val, bl: list Z,
      nslots: Z, j: Z, nd: val
 PRE [ tptr t_ld, tuint, tptr t_node ]
   PROP (node_pre_props shb bs pos acap bcap nfns entry al bl nslots j)
   PARAMS (r; Vint (Int.repr j); nd)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
        args_pool args acap al; bytes_pool bytes bcap bl;
        data_at Ews t_node (node_val (mkN 6 0 0 0 0 0 0)) nd)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX xs: list Z, EX bl': list Z, EX x: node, EX v: reptype t_node,
   PROP (node_post_props bs acap bcap nfns al bl nslots j rc pos' xs bl' x v)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl')) p;
        args_pool args acap (al ++ xs); bytes_pool bytes bcap bl';
        data_at Ews t_node v nd).

Definition load_for_spec :=
 DECLARE _load_for
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z,
      p: val, nfns: Z, entry: Z, fns: val, args: val, al: list Z, bytes: val, bl: list Z,
      nslots: Z, j: Z, nd: val
 PRE [ tptr t_ld, tuint, tuint, tptr t_node ]
   PROP (node_pre_props shb bs pos acap bcap nfns entry al bl nslots j)
   PARAMS (r; Vint (Int.repr nslots); Vint (Int.repr j); nd)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
        args_pool args acap al; bytes_pool bytes bcap bl;
        data_at Ews t_node (node_val (mkN 7 0 0 0 0 0 0)) nd)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX xs: list Z, EX bl': list Z, EX x: node, EX v: reptype t_node,
   PROP (node_post_props bs acap bcap nfns al bl nslots j rc pos' xs bl' x v)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl')) p;
        args_pool args acap (al ++ xs); bytes_pool bytes bcap bl';
        data_at Ews t_node v nd).

Definition load_node_spec :=
 DECLARE _load_node
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z,
      p: val, nfns: Z, entry: Z, fns: val, args: val, al: list Z, bytes: val, bl: list Z,
      nslots: Z, j: Z, nd: val
 PRE [ tptr t_ld, tptr t_prog, tuint, tuint, tptr t_node ]
   PROP (node_pre_props shb bs pos acap bcap nfns entry al bl nslots j)
   PARAMS (r; p; Vint (Int.repr nslots); Vint (Int.repr j); nd)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
        args_pool args acap al; bytes_pool bytes bcap bl;
        data_at_ Ews t_node nd)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX xs: list Z, EX bl': list Z, EX x: node, EX v: reptype t_node,
   PROP (node_post_props bs acap bcap nfns al bl nslots j rc pos' xs bl' x v)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl')) p;
        args_pool args acap (al ++ xs); bytes_pool bytes bcap bl';
        data_at Ews t_node v nd).

(* ------------------------------------------------------------ functions *)

Definition load_fn_spec :=
 DECLARE _load_fn
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, acap: Z, bcap: Z,
      p: val, nfns: Z, entry: Z, fns: val, args: val, al: list Z, bytes: val, bl: list Z,
      f: Z, gv: globals
 PRE [ tptr t_ld, tptr t_prog, tuint ]
   PROP (readable_share shb; bytes_ok bs; 0 <= pos <= Zlength bs; Zlength bs <= MAXIN;
         0 <= acap <= MAXIN; 0 <= bcap <= MAXIN; Zlength al <= acap; Zlength bl <= bcap; bytes_ok bl;
         0 <= f < nfns; nfns <= 65536; 0 <= entry <= Int.max_unsigned;
         field_compatible (tarray t_fn nfns) nil fns)
   PARAMS (r; p; Vint (Int.repr f)) GLOBALS (gv)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes (Zlength bl)) p;
        args_pool args acap al; bytes_pool bytes bcap bl;
        data_at Ews t_fn (fn_val zero_fn) (field_address (tarray t_fn nfns) [ArraySubsc f] fns);
        mem_mgr gv)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX xs: list Z, EX bl': list Z, EX x: fnr, EX fv: reptype t_fn, EX k: Z,
   PROP (0 <= rc <= 21; 0 <= pos' <= Zlength bs; (Zlength al + Zlength xs <= acap)%Z; u32_ok xs;
         Zlength bl <= Zlength bl' <= bcap; bytes_ok bl';
         rc = 0 -> fv = fn_val x /\ fn_ok nfns (al ++ xs) (Zlength bl') x)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf;
        data_at Tsh t_prog (PRG nfns entry fns args (Zlength (al ++ xs)) bytes (Zlength bl')) p;
        args_pool args acap (al ++ xs); bytes_pool bytes bcap bl';
        data_at Ews t_fn fv (field_address (tarray t_fn nfns) [ArraySubsc f] fns);
        if Z.eq_dec rc 0 then nodes_rep x else blk (tarray t_node k) (fn_nodes fv);
        mem_mgr gv).

Definition check_calls_spec :=
 DECLARE _check_calls
 WITH p: val, nfns: Z, entry: Z, fns: val, args: val, al: list Z, bytes: val, nb: Z, F: list fnr
 PRE [ tptr t_prog ]
   PROP (Zlength F = nfns; 0 <= nfns <= 65536; Forall (fn_ok nfns al nb) F;
         0 <= Zlength al <= Int.max_unsigned; 0 <= nb <= Int.max_unsigned; 0 <= entry <= Int.max_unsigned)
   PARAMS (p)
   SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p; fns_rep fns F)
 POST [ tint ]
   EX rc: Z,
   PROP (rc = 0 \/ rc = 12; rc = 0 -> Forall (fun x => Forall (call_ok F) (f_body x)) F)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p; fns_rep fns F).

Definition load_header_spec :=
 DECLARE _load_header
 WITH r: val, buf: val, shb: share, bs: list Z, pos: Z, p: val, gv: globals
 PRE [ tptr t_ld, tptr t_prog ]
   PROP (readable_share shb; bytes_ok bs; 0 <= pos <= Zlength bs; Zlength bs <= MAXIN)
   PARAMS (r; p) GLOBALS (gv)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos 0 0) r; buf_rep shb bs buf;
        data_at Tsh t_prog PRG0 p; mem_mgr gv)
 POST [ tint ]
   EX rc: Z, EX pos': Z, EX acap: Z, EX bcap: Z,
   PROP (0 <= rc <= 20; 0 <= pos' <= Zlength bs; 0 <= acap <= MAXIN; 0 <= bcap <= MAXIN)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) pos' acap bcap) r; buf_rep shb bs buf; mem_mgr gv;
        if Z.eq_dec rc 0 then
          EX nfns: Z, EX entry: Z, EX fns: val, EX args: val, EX bytes: val,
          !! (1 <= nfns <= 65536 /\ 0 <= entry < nfns) &&
          data_at Tsh t_prog (PRG nfns entry fns args 0 bytes 0) p *
          malloc_token Ews (tarray t_fn nfns) fns *
          data_at Ews (tarray t_fn nfns) (Zrepeat (fn_val zero_fn) nfns) fns *
          args_pool args acap nil * bytes_pool bytes bcap nil
        else freeable p).

Definition trim_args_spec :=
 DECLARE _trim_args
 WITH p: val, nfns: Z, entry: Z, fns: val, args: val, acap: Z, al: list Z, bytes: val, nb: Z, gv: globals
 PRE [ tptr t_prog ]
   PROP (Zlength al <= acap <= MAXIN; u32_ok al)
   PARAMS (p) GLOBALS (gv)
   SEP (data_at Tsh t_prog (PRG nfns entry fns args (Zlength al) bytes nb) p; args_pool args acap al; mem_mgr gv)
 POST [ tint ]
   EX rc: Z, EX args': val,
   PROP (rc = 0 \/ rc = 20)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_prog (PRG nfns entry fns args' (Zlength al) bytes nb) p; mem_mgr gv;
        if Z.eq_dec rc 0 then args_final args' al else !! (args' = args) && args_pool args acap al).

Definition trim_bytes_spec :=
 DECLARE _trim_bytes
 WITH p: val, nfns: Z, entry: Z, fns: val, args: val, na: Z, bytes: val, bcap: Z, bl: list Z, gv: globals
 PRE [ tptr t_prog ]
   PROP (Zlength bl <= bcap <= MAXIN; bytes_ok bl)
   PARAMS (p) GLOBALS (gv)
   SEP (data_at Tsh t_prog (PRG nfns entry fns args na bytes (Zlength bl)) p; bytes_pool bytes bcap bl;
        mem_mgr gv)
 POST [ tint ]
   EX rc: Z, EX bytes': val,
   PROP (rc = 0 \/ rc = 20)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_prog (PRG nfns entry fns args na bytes' (Zlength bl)) p; mem_mgr gv;
        if Z.eq_dec rc 0 then bytes_final bytes' bl else !! (bytes' = bytes) && bytes_pool bytes bcap bl).

Definition prog_clear_spec :=
 DECLARE _prog_clear
 WITH p: val
 PRE [ tptr t_prog ]
   PROP () PARAMS (p) SEP (data_at_ Tsh t_prog p)
 POST [ tvoid ]
   PROP () RETURN () SEP (data_at Tsh t_prog PRG0 p).

Definition load_all_spec :=
 DECLARE _load_all
 WITH r: val, buf: val, shb: share, bs: list Z, p: val, gv: globals
 PRE [ tptr t_ld, tptr t_prog ]
   PROP (readable_share shb; bytes_ok bs; Zlength bs <= Int64.max_unsigned)
   PARAMS (r; p) GLOBALS (gv)
   SEP (data_at Tsh t_ld (LD buf (Zlength bs) 0 0 0) r; buf_rep shb bs buf; data_at Tsh t_prog PRG0 p;
        mem_mgr gv)
 POST [ tint ]
   EX rc: Z, EX rv: reptype t_ld,
   PROP (0 <= rc <= 21)
   RETURN (Vint (Int.repr rc))
   SEP (data_at Tsh t_ld rv r; buf_rep shb bs buf; mem_mgr gv;
        if Z.eq_dec rc 0 then prog_rep p else freeable p).

Definition vx_free_program_spec :=
 DECLARE _vx_free_program
 WITH p: val, gv: globals
 PRE [ tptr t_prog ]
   PROP () PARAMS (p) GLOBALS (gv) SEP (freeable p; mem_mgr gv)
 POST [ tvoid ]
   PROP () RETURN () SEP (data_at Tsh t_prog PRG0 p; mem_mgr gv).

Definition vx_load_spec :=
 DECLARE _vx_load
 WITH buf: val, shb: share, bs: list Z, out: val, gv: globals
 PRE [ tptr tuchar, tulong, tptr t_prog ]
   PROP (readable_share shb; bytes_ok bs; Zlength bs <= Int64.max_unsigned)
   PARAMS (buf; Vlong (Int64.repr (Zlength bs)); out) GLOBALS (gv)
   SEP (buf_rep shb bs buf; data_at_ Tsh t_prog out; mem_mgr gv)
 POST [ tint ]
   EX rc: Z,
   PROP (0 <= rc <= 21)
   RETURN (Vint (Int.repr rc))
   SEP (buf_rep shb bs buf; mem_mgr gv;
        if Z.eq_dec rc 0 then prog_rep out else data_at Tsh t_prog PRG0 out).

Definition Gprog : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   rd_u8_spec; rd_u32_spec; rd_i64_spec; rd_bytes_spec; rd_child_spec; rd_slot_spec; rd_args_spec;
   node_clear_spec; load_lit_spec; load_prim_spec; load_call_spec; load_heap_spec; load_three_spec;
   load_for_spec; load_node_spec; load_fn_spec; check_calls_spec; load_header_spec; trim_args_spec;
   trim_bytes_spec; prog_clear_spec; load_all_spec; vx_free_program_spec; vx_load_spec].
