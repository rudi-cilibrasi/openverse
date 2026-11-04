/-
  OpenVerse — the OVBC binary format (`docs/FORMAT.md`).

  `Prog.encode` serialises a Verse Core program for the C runtime. Each
  function's expression tree becomes a post-order node table, so every child
  reference points to an earlier node; compound literals are emitted as the
  primitive that builds them.
-/
import OpenVerse.Core.Syntax
import OpenVerse.Core.Prims

namespace OpenVerse.Encode

def u8 (n : Nat) : ByteArray := ByteArray.mk #[n.toUInt8]

def u32 (n : Nat) : ByteArray :=
  ByteArray.mk #[(n % 256).toUInt8, (n / 256 % 256).toUInt8,
    (n / 65536 % 256).toUInt8, (n / 16777216 % 256).toUInt8]

/-- Two's-complement little-endian 64-bit encoding. -/
def i64 (i : Int) : ByteArray :=
  let u : Nat := (i % (2 ^ 64 : Int)).toNat
  ByteArray.mk ((List.range 8).map (fun k => (u / 2 ^ (8 * k) % 256).toUInt8)).toArray

def bytes (bs : List Nat) : ByteArray := ByteArray.mk (bs.map (·.toUInt8)).toArray

/-- The code of each primitive (FORMAT.md) and its `k` field. -/
def primCode : Prim → Nat × Nat
  | .add => (0, 0) | .sub => (1, 0) | .mul => (2, 0) | .neg => (3, 0) | .abs => (4, 0)
  | .floorDiv => (5, 0) | .ceilDiv => (6, 0) | .quotient => (7, 0) | .modulo => (8, 0)
  | .lt => (9, 0) | .le => (10, 0) | .gt => (11, 0) | .ge => (12, 0)
  | .eq => (13, 0) | .ne => (14, 0) | .query => (15, 0)
  | .mkArr => (16, 0) | .mkTup => (17, 0) | .mkSome => (18, 0)
  | .concat => (19, 0) | .index => (20, 0) | .len => (21, 0) | .arrSet => (22, 0)
  | .flatten => (23, 0) | .range => (24, 0) | .tupGet k => (25, k) | .toStr => (26, 0)
  | .fail => (27, 0) | .userErr => (28, 0)

/-- The node table under construction. -/
abbrev EncM := StateM (Array ByteArray)

def emit (b : ByteArray) : EncM Nat := modifyGet fun ns => (ns.size, ns.push b)

def emitPrim (op : Prim) (args : List Nat) : EncM Nat :=
  let (c, k) := primCode op
  emit (u8 4 ++ u8 c ++ u32 k ++ u32 args.length ++ args.foldl (fun b a => b ++ u32 a) .empty)

mutual
def encLit : Value → EncM Nat
  | .int i => emit (u8 0 ++ u8 0 ++ i64 i)
  | .logic b => emit (u8 0 ++ u8 1 ++ u8 (if b then 1 else 0))
  | .char c => emit (u8 0 ++ u8 2 ++ u8 c)
  | .none => emit (u8 0 ++ u8 4)
  | .arr vs => match asBytes vs with
    | some bs => emit (u8 0 ++ u8 3 ++ u32 bs.length ++ bytes bs)
    | none => do let ids ← encLits vs; emitPrim .mkArr ids
  | .tup [] => emit (u8 0 ++ u8 5)
  | .tup (v :: vs) => do let ids ← encLits (v :: vs); emitPrim .mkTup ids
  | .some v => do let i ← encLit v; emitPrim .mkSome [i]
def encLits : List Value → EncM (List Nat)
  | [] => pure []
  | v :: vs => do let i ← encLit v; let is ← encLits vs; pure (i :: is)
end

mutual
def encExpr : Expr → EncM Nat
  | .lit v => encLit v
  | .local i => emit (u8 1 ++ u32 i)
  | .assign i e => do let a ← encExpr e; emit (u8 2 ++ u32 i ++ u32 a)
  | .seq a b => do let x ← encExpr a; let y ← encExpr b; emit (u8 3 ++ u32 x ++ u32 y)
  | .prim op es => do let ids ← encExprs es; emitPrim op ids
  | .call f es => do
    let ids ← encExprs es
    emit (u8 5 ++ u32 f ++ u32 ids.length ++ ids.foldl (fun b a => b ++ u32 a) .empty)
  | .ite c t e => do
    let x ← encExpr c; let y ← encExpr t; let z ← encExpr e
    emit (u8 6 ++ u32 x ++ u32 y ++ u32 z)
  | .forE i it filt body => do
    let x ← encExpr it; let y ← encExpr filt; let z ← encExpr body
    emit (u8 7 ++ u32 i ++ u32 x ++ u32 y ++ u32 z)
  | .loop b => do let x ← encExpr b; emit (u8 8 ++ u32 x)
  | .brk => emit (u8 9)
  | .ret e => do let x ← encExpr e; emit (u8 10 ++ u32 x)
  | .print e => do let x ← encExpr e; emit (u8 11 ++ u32 x)
def encExprs : List Expr → EncM (List Nat)
  | [] => pure []
  | e :: es => do let i ← encExpr e; let is ← encExprs es; pure (i :: is)
end

def encFn (fn : Fn) : ByteArray :=
  let (root, nodes) := (encExpr fn.body).run #[]
  let name := fn.name.toUTF8
  u32 fn.arity ++ u32 fn.nslots ++ u8 (if fn.decides then 1 else 0) ++ u32 name.size ++ name ++
    u32 nodes.size ++ nodes.foldl (· ++ ·) .empty ++ u32 root

end Encode

/-- Serialise a program in the OVBC format. -/
def Prog.encode (P : Prog) : ByteArray :=
  "OVBC".toUTF8 ++ Encode.u32 1 ++ Encode.u32 P.fns.length ++ Encode.u32 P.main ++
    P.fns.foldl (fun b fn => b ++ Encode.encFn fn) .empty

end OpenVerse
