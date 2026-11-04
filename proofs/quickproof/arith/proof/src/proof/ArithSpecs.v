(* ArithSpecs: the specifications of the nine functions of runtime/src/arith.c (bodies: ArithBasic.v,
   ArithDiv.v).

   Each specification states the exact result in Z.  The value v that *out holds before the call is
   arbitrary; it is left unchanged whenever the result is not VX_OK. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require OpenverseArith.units.Arith.
Require Import OpenverseArith.arith.code.
Require Import OpenverseArith.proof.ArithZ OpenverseArith.proof.ArithTac.

#[export] Instance CS : compspecs := OpenverseArith.units.Arith.CS.
Definition Vprog : varspecs. mk_varspecs OpenverseArith.arith.code.prog. Defined.

Definition vx_add_spec :=
  DECLARE _vx_add
  WITH a: Z, b: Z, out: val, sh: share, v: val
  PRE [ tlong, tlong, tptr tlong ]
    PROP (writable_share sh; MIN <= a <= MAX; MIN <= b <= MAX)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b); out)
    SEP (data_at sh tlong v out)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (st_of (a + b))))
    SEP (data_at sh tlong (out_of (a + b) v) out).

Definition vx_sub_spec :=
  DECLARE _vx_sub
  WITH a: Z, b: Z, out: val, sh: share, v: val
  PRE [ tlong, tlong, tptr tlong ]
    PROP (writable_share sh; MIN <= a <= MAX; MIN <= b <= MAX)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b); out)
    SEP (data_at sh tlong v out)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (st_of (a - b))))
    SEP (data_at sh tlong (out_of (a - b) v) out).

Definition vx_mul_spec :=
  DECLARE _vx_mul
  WITH a: Z, b: Z, out: val, sh: share, v: val
  PRE [ tlong, tlong, tptr tlong ]
    PROP (writable_share sh; MIN <= a <= MAX; MIN <= b <= MAX)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b); out)
    SEP (data_at sh tlong v out)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (st_of (a * b))))
    SEP (data_at sh tlong (out_of (a * b) v) out).

Definition vx_neg_spec :=
  DECLARE _vx_neg
  WITH a: Z, out: val, sh: share, v: val
  PRE [ tlong, tptr tlong ]
    PROP (writable_share sh; MIN <= a <= MAX)
    PARAMS (Vlong (Int64.repr a); out)
    SEP (data_at sh tlong v out)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (st_of (- a))))
    SEP (data_at sh tlong (out_of (- a) v) out).

Definition vx_abs_spec :=
  DECLARE _vx_abs
  WITH a: Z, out: val, sh: share, v: val
  PRE [ tlong, tptr tlong ]
    PROP (writable_share sh; MIN <= a <= MAX)
    PARAMS (Vlong (Int64.repr a); out)
    SEP (data_at sh tlong v out)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (st_of (Z.abs a))))
    SEP (data_at sh tlong (out_of (Z.abs a) v) out).

Definition vx_floordiv_spec :=
  DECLARE _vx_floordiv
  WITH a: Z, b: Z, out: val, sh: share, v: val
  PRE [ tlong, tlong, tptr tlong ]
    PROP (writable_share sh; MIN <= a <= MAX; MIN <= b <= MAX)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b); out)
    SEP (data_at sh tlong v out)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (div_st b (a / b))))
    SEP (data_at sh tlong (div_out b (a / b) v) out).

Definition vx_ceildiv_spec :=
  DECLARE _vx_ceildiv
  WITH a: Z, b: Z, out: val, sh: share, v: val
  PRE [ tlong, tlong, tptr tlong ]
    PROP (writable_share sh; MIN <= a <= MAX; MIN <= b <= MAX)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b); out)
    SEP (data_at sh tlong v out)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (div_st b (ceildiv a b))))
    SEP (data_at sh tlong (div_out b (ceildiv a b) v) out).

Definition vx_quotient_spec :=
  DECLARE _vx_quotient
  WITH a: Z, b: Z, out: val, sh: share, v: val
  PRE [ tlong, tlong, tptr tlong ]
    PROP (writable_share sh; MIN <= a <= MAX; MIN <= b <= MAX)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b); out)
    SEP (data_at sh tlong v out)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (div_st b (ediv a b))))
    SEP (data_at sh tlong (div_out b (ediv a b) v) out).

(* The Euclidean remainder always fits: VX_OK unless b = 0. *)
Definition vx_modulo_spec :=
  DECLARE _vx_modulo
  WITH a: Z, b: Z, out: val, sh: share, v: val
  PRE [ tlong, tlong, tptr tlong ]
    PROP (writable_share sh; MIN <= a <= MAX; MIN <= b <= MAX)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b); out)
    SEP (data_at sh tlong v out)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if b =? 0 then VX_FAIL else VX_OK)))
    SEP (data_at sh tlong (if b =? 0 then v else Vlong (Int64.repr (emod a b))) out).


(* The context of a body: vx_abs and the divisions call vx_neg. *)
Definition Gprog : funspecs := [vx_neg_spec].
