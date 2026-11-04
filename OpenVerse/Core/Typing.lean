/-
  OpenVerse — types of Verse Core and the typing relation.

  `VTy` are the types of Verse Core values (Verse's `int`, `logic`, `char`,
  `[]t`, `tuple(…)` with `void = tuple()`, `?t`). `hasTy v t` types values;
  `Typed S Γ ρ e τ` types expressions: `S` gives each function's parameter
  and result types, `Γ` the type of each slot of the current frame, `ρ` the
  result type of the current function (for `return`).

  A function is typed when its body starts by initialising every
  non-parameter slot with the default value of its type (`initPrefix`), and
  the rest of the body has the function's result type. The elaborator emits
  that prefix, so the invariant "every slot holds a value of its type" holds
  throughout the rest of the body: `OpenVerse.Core.TypeSafety`.
-/
import OpenVerse.Core.Semantics

namespace OpenVerse

inductive VTy where
  | int | logic | char
  | arr : VTy → VTy
  | tup : List VTy → VTy
  | opt : VTy → VTy
  deriving Repr, Inhabited

namespace VTy

/-- `void` is the empty tuple. -/
def void : VTy := .tup []
def str : VTy := .arr .char

mutual
def decEq : (a b : VTy) → Decidable (a = b)
  | .int, .int => isTrue rfl
  | .logic, .logic => isTrue rfl
  | .char, .char => isTrue rfl
  | .arr a, .arr b => match decEq a b with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .opt a, .opt b => match decEq a b with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .tup as, .tup bs => match decEqList as bs with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .int, .logic | .int, .char | .int, .arr _ | .int, .tup _ | .int, .opt _
  | .logic, .int | .logic, .char | .logic, .arr _ | .logic, .tup _ | .logic, .opt _
  | .char, .int | .char, .logic | .char, .arr _ | .char, .tup _ | .char, .opt _
  | .arr _, .int | .arr _, .logic | .arr _, .char | .arr _, .tup _ | .arr _, .opt _
  | .tup _, .int | .tup _, .logic | .tup _, .char | .tup _, .arr _ | .tup _, .opt _
  | .opt _, .int | .opt _, .logic | .opt _, .char | .opt _, .arr _ | .opt _, .tup _ =>
    isFalse (by intro h; cases h)
def decEqList : (as bs : List VTy) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | a :: as, b :: bs => match decEq a b, decEqList as bs with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h1, _ => isFalse (by intro h; cases h; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro h; cases h; exact h2 rfl)
end

instance : DecidableEq VTy := decEq

mutual
/-- The value a slot of this type starts with (after the initialisation prefix). -/
def default : VTy → Value
  | .int => .int 0
  | .logic => .logic false
  | .char => .char 0
  | .arr _ => .arr []
  | .opt _ => .none
  | .tup ts => .tup (defaults ts)
def defaults : List VTy → List Value
  | [] => []
  | t :: ts => default t :: defaults ts
end

end VTy

mutual
/-- `v` has type `t`. -/
def hasTy : Value → VTy → Bool
  | .int _, .int => true
  | .logic _, .logic => true
  | .char c, .char => decide (c < 256)
  | .arr vs, .arr t => allTy vs t
  | .tup vs, .tup ts => allTys vs ts
  | .none, .opt _ => true
  | .some v, .opt t => hasTy v t
  | _, _ => false
/-- Every element of `vs` has type `t`. -/
def allTy : List Value → VTy → Bool
  | [], _ => true
  | v :: vs, t => hasTy v t && allTy vs t
/-- The elements of `vs` have the types `ts`, pointwise. -/
def allTys : List Value → List VTy → Bool
  | [], [] => true
  | v :: vs, t :: ts => hasTy v t && allTys vs ts
  | [], _ :: _ => false
  | _ :: _, [] => false
end

/-- Function signatures: parameter types and result type, by function index. -/
abbrev Sigs := List (List VTy × VTy)

/-- The typing of primitives: `PrimTy op ts τ` when `op` applied to values
    of types `ts` gives a value of type `τ`. -/
inductive PrimTy : Prim → List VTy → VTy → Prop
  | arith {op} : op ∈ [Prim.add, .sub, .mul, .floorDiv, .ceilDiv, .quotient, .modulo] →
      PrimTy op [.int, .int] .int
  | unary {op} : op ∈ [Prim.neg, .abs] → PrimTy op [.int] .int
  | cmpInt {op} : op ∈ [Prim.lt, .le, .gt, .ge] → PrimTy op [.int, .int] .int
  | cmpChar {op} : op ∈ [Prim.lt, .le, .gt, .ge] → PrimTy op [.char, .char] .char
  | eq {a b} : PrimTy .eq [a, b] a
  | ne {a b} : PrimTy .ne [a, b] a
  | queryLogic : PrimTy .query [.logic] .logic
  | queryOpt {t} : PrimTy .query [.opt t] t
  | mkArr {t ts} : (∀ u ∈ ts, u = t) → PrimTy .mkArr ts (.arr t)
  | mkTup {ts} : PrimTy .mkTup ts (.tup ts)
  | mkSome {t} : PrimTy .mkSome [t] (.opt t)
  | concat {t} : PrimTy .concat [.arr t, .arr t] (.arr t)
  | index {t} : PrimTy .index [.arr t, .int] t
  | len {t} : PrimTy .len [.arr t] .int
  | arrSet {t} : PrimTy .arrSet [.arr t, .int, t] (.arr t)
  | flatten {t} : PrimTy .flatten [.arr (.arr t)] (.arr t)
  | range : PrimTy .range [.int, .int] (.arr .int)
  | tupGet {k ts t} : ts[k]? = some t → PrimTy (.tupGet k) [.tup ts] t
  | toStrInt : PrimTy .toStr [.int] VTy.str
  | toStrChar : PrimTy .toStr [.char] VTy.str
  | toStrStr : PrimTy .toStr [VTy.str] VTy.str
  | fail {t} : PrimTy .fail [] t
  | userErr {t} : PrimTy .userErr [] t

mutual
/-- `Typed S Γ ρ e τ`: in a function whose slots have types `Γ` and whose
    result type is `ρ`, `e` has type `τ`. `break`, `return`, `false?` and
    `Err()` have every type. -/
inductive Typed (S : Sigs) (Γ : List VTy) (ρ : VTy) : Expr → VTy → Prop
  | lit {v τ} : hasTy v τ = true → Typed S Γ ρ (.lit v) τ
  | local {i τ} : Γ[i]? = some τ → Typed S Γ ρ (.local i) τ
  | assign {i e τ} : Γ[i]? = some τ → Typed S Γ ρ e τ → Typed S Γ ρ (.assign i e) τ
  | seq {a b σ τ} : Typed S Γ ρ a σ → Typed S Γ ρ b τ → Typed S Γ ρ (.seq a b) τ
  | prim {op es ts τ} : TypedL S Γ ρ es ts → PrimTy op ts τ → Typed S Γ ρ (.prim op es) τ
  | call {f es ps τ} : S[f]? = some (ps, τ) → TypedL S Γ ρ es ps → Typed S Γ ρ (.call f es) τ
  | ite {c t e σ τ} : Typed S Γ ρ c σ → Typed S Γ ρ t τ → Typed S Γ ρ e τ →
      Typed S Γ ρ (.ite c t e) τ
  | forE {i it filt body τe σ τb} : Γ[i]? = some τe → Typed S Γ ρ it (.arr τe) →
      Typed S Γ ρ filt σ → Typed S Γ ρ body τb → Typed S Γ ρ (.forE i it filt body) (.arr τb)
  | loop {b σ} : Typed S Γ ρ b σ → Typed S Γ ρ (.loop b) VTy.void
  | brk {τ} : Typed S Γ ρ .brk τ
  | ret {e τ} : Typed S Γ ρ e ρ → Typed S Γ ρ (.ret e) τ
  | print {e} : Typed S Γ ρ e VTy.str → Typed S Γ ρ (.print e) VTy.void
inductive TypedL (S : Sigs) (Γ : List VTy) (ρ : VTy) : List Expr → List VTy → Prop
  | nil : TypedL S Γ ρ [] []
  | cons {e es τ ts} : Typed S Γ ρ e τ → TypedL S Γ ρ es ts → TypedL S Γ ρ (e :: es) (τ :: ts)
end

/-- The initialisation of slots `k, k+1, …` with the defaults of `ts`, before `e`. -/
def initPrefix (k : Nat) : List VTy → Expr → Expr
  | [], e => e
  | t :: ts, e => .seq (.assign k (.lit t.default)) (initPrefix (k + 1) ts e)

/-- A function of signature `(ps, ρ)` is typed with slot types `Γ`. -/
structure FnTyped (S : Sigs) (fn : Fn) (ps : List VTy) (ρ : VTy) (Γ : List VTy) : Prop where
  arity : fn.arity = ps.length
  slots : Γ.length = fn.nslots
  params : Γ.take fn.arity = ps
  body : ∃ b, fn.body = initPrefix fn.arity (Γ.drop fn.arity) b ∧ Typed S Γ ρ b ρ

/-- Every function of `P` is typed with its signature in `S`. -/
def ProgTyped (P : Prog) (S : Sigs) : Prop :=
  P.fns.length = S.length ∧
  ∀ (f : Nat) (fn : Fn) (ps : List VTy) (τ : VTy), P.fns[f]? = some fn → S[f]? = some (ps, τ) →
    ∃ Γ, FnTyped S fn ps τ Γ

/-- A frame agrees with slot types `Γ`. -/
def FrameOK (Γ : List VTy) (fr : List Value) : Prop := allTys fr Γ = true

/-- What a typed expression's outcome can be: a value of its type, a
    `return` of a value of the result type, anything else but a type error. -/
def ResOK (τ ρ : VTy) : Res → Prop
  | .ok v => hasTy v τ = true
  | .ret v => hasTy v ρ = true
  | .err k => k ≠ .type
  | .fail => True
  | .brk => True

def LResOK (ts : List VTy) (ρ : VTy) : LRes → Prop
  | .ok vs => allTys vs ts = true
  | .stop r => ResOK VTy.void ρ r ∧ r.isOk = false

end OpenVerse
