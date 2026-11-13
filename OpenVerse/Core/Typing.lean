/-
  OpenVerse — types of Verse Core and the typing relation.

  `VTy` are the types of Verse Core values (Verse's `int`, `logic`, `char`,
  `[]t`, `tuple(…)` with `void = tuple()`, `?t`). `hasTy v t` types values;
  `Typed S Γ ρ e τ` types expressions: `S` gives each function's parameter
  and result types, `Γ` the type of each slot of the current frame, `ρ` the
  result type of the current function (for `return`).

  Types may mention type variables (`var j`, the j-th type parameter of a
  generic function). No value has a type variable as its type; a call
  instantiates its callee's signature with any substitution `θ`.

  A function is typed when its body starts by initialising every
  non-parameter slot with a value of its type (`initPrefixE`), and the rest
  of the body has the function's result type. For a slot of a closed type
  that value is the type's default literal; a slot whose type mentions a type
  variable is initialised from the parameters (`DefaultE`): a generic
  function receives a value of each of its type parameters as a hidden
  argument. The elaborator emits that prefix, so the invariant "every slot
  holds a value of its type" holds throughout the rest of the body:
  `OpenVerse.Core.TypeSafety`.
-/
import OpenVerse.Core.Semantics

namespace OpenVerse

inductive VTy where
  | int | logic | char
  /-- `float` (#127): an IEEE 64-bit float. -/
  | float
  | arr : VTy → VTy
  | tup : List VTy → VTy
  | opt : VTy → VTy
  /-- The `j`-th type parameter of the current (generic) function. -/
  | var : Nat → VTy
  /-- A reference to an object whose class tag is one of `ts` (#29), whose
      type arguments start with `args` (#39): a subclass may have more
      parameters than its parent, after the parent's. -/
  | ref : List Nat → List VTy → VTy
  /-- A reference through *views* (#351): to an object whose class tag is
      one of the entries' `t`, whose entry `(t, φ)` gives the view's type
      arguments as types over the object's (`var j` is its argument `j`),
      of which `args` is a prefix. An interface a class gives arguments that
      are not a prefix of its own (`both(t, u) := class(container(t),
      sink(u))` at `sink`: `φ = [var 1]`) is referred to so. The views are
      the classes' own: substitution leaves them. -/
  | vref : List (Nat × List VTy) → List VTy → VTy
  /-- `comparable` (Book of Verse ch. 11): the type of every value, above
      every type. The front end boxes a comparable value before it becomes
      one (`OpenVerse.Core.Comparable`), so that `veq` on boxes is Verse's
      equality; Verse Core needs only that every value has it. -/
  | dyn
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
  | .float, .float => isTrue rfl
  | .arr a, .arr b => match decEq a b with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .opt a, .opt b => match decEq a b with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .tup as, .tup bs => match decEqList as bs with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .var a, .var b => if h : a = b then isTrue (by subst h; rfl)
    else isFalse (by intro h'; cases h'; exact h rfl)
  | .ref a as, .ref b bs => if h : a = b then
      match decEqList as bs with
      | isTrue h2 => isTrue (by subst h; subst h2; rfl)
      | isFalse h2 => isFalse (by intro h'; cases h'; exact h2 rfl)
    else isFalse (by intro h'; cases h'; exact h rfl)
  | .vref a as, .vref b bs => match decEqEnts a b with
    | isTrue h => match decEqList as bs with
      | isTrue h2 => isTrue (by subst h; subst h2; rfl)
      | isFalse h2 => isFalse (by intro h'; cases h'; exact h2 rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .vref _ _, .int | .vref _ _, .logic | .vref _ _, .char | .vref _ _, .float | .vref _ _, .arr _
  | .vref _ _, .tup _ | .vref _ _, .opt _ | .vref _ _, .var _ | .vref _ _, .ref _ _
  | .int, .vref _ _ | .logic, .vref _ _ | .char, .vref _ _ | .float, .vref _ _ | .arr _, .vref _ _
  | .tup _, .vref _ _ | .opt _, .vref _ _ | .var _, .vref _ _ | .ref _ _, .vref _ _ =>
    isFalse (by intro h; cases h)
  | .int, .ref _ _ | .logic, .ref _ _ | .char, .ref _ _ | .arr _, .ref _ _ | .tup _, .ref _ _
  | .opt _, .ref _ _ | .var _, .ref _ _
  | .ref _ _, .int | .ref _ _, .logic | .ref _ _, .char | .ref _ _, .arr _ | .ref _ _, .tup _
  | .ref _ _, .opt _ | .ref _ _, .var _ => isFalse (by intro h; cases h)
  | .int, .var _ | .logic, .var _ | .char, .var _ | .arr _, .var _ | .tup _, .var _ | .opt _, .var _
  | .var _, .int | .var _, .logic | .var _, .char | .var _, .arr _ | .var _, .tup _ | .var _, .opt _
  | .int, .logic | .int, .char | .int, .arr _ | .int, .tup _ | .int, .opt _
  | .logic, .int | .logic, .char | .logic, .arr _ | .logic, .tup _ | .logic, .opt _
  | .char, .int | .char, .logic | .char, .arr _ | .char, .tup _ | .char, .opt _
  | .arr _, .int | .arr _, .logic | .arr _, .char | .arr _, .tup _ | .arr _, .opt _
  | .tup _, .int | .tup _, .logic | .tup _, .char | .tup _, .arr _ | .tup _, .opt _
  | .opt _, .int | .opt _, .logic | .opt _, .char | .opt _, .arr _ | .opt _, .tup _
  | .float, .int | .float, .logic | .float, .char | .float, .arr _ | .float, .tup _ | .float, .opt _
  | .float, .var _ | .float, .ref _ _
  | .int, .float | .logic, .float | .char, .float | .arr _, .float | .tup _, .float | .opt _, .float
  | .var _, .float | .ref _ _, .float =>
    isFalse (by intro h; cases h)
  | .dyn, .dyn => isTrue rfl
  | .dyn, .int | .dyn, .logic | .dyn, .char | .dyn, .float | .dyn, .arr _ | .dyn, .tup _ | .dyn, .opt _
  | .dyn, .var _ | .dyn, .ref _ _ | .dyn, .vref _ _
  | .int, .dyn | .logic, .dyn | .char, .dyn | .float, .dyn | .arr _, .dyn | .tup _, .dyn | .opt _, .dyn
  | .var _, .dyn | .ref _ _, .dyn | .vref _ _, .dyn => isFalse (by intro h; cases h)
def decEqList : (as bs : List VTy) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | a :: as, b :: bs => match decEq a b, decEqList as bs with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h1, _ => isFalse (by intro h; cases h; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro h; cases h; exact h2 rfl)
def decEqEnts : (as bs : List (Nat × List VTy)) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | (t, φ) :: as, (u, ψ) :: bs =>
    if h0 : t = u then
      match decEqList φ ψ, decEqEnts as bs with
      | isTrue h1, isTrue h2 => isTrue (by subst h0; subst h1; subst h2; rfl)
      | isFalse h1, _ => isFalse (by intro h; cases h; exact h1 rfl)
      | _, isFalse h2 => isFalse (by intro h; cases h; exact h2 rfl)
    else isFalse (by intro h; cases h; exact h0 rfl)
end

instance : DecidableEq VTy := decEq

mutual
/-- The value a slot of this type starts with (after the initialisation prefix). -/
def default : VTy → Value
  | .int => .int 0
  | .logic => .logic false
  | .char => .char 0
  | .float => .float 0
  | .arr _ => Value.emptyArray
  | .opt _ => .none
  | .tup ts => Value.ofTuple (defaults ts)
  -- no value has a type variable as its type; slots of such types are
  -- initialised from parameters instead (`DefaultE`)
  | .var _ => .void
  -- a reference has no default of its own: slots of such types start as a
  -- prototype, a new object or a parameter instead (`DefaultE`, #37)
  | .ref _ _ => .void
  | .vref _ _ => .void
  -- (a `dyn` slot starts as `()`, which every type's values include)
  | .dyn => .void
def defaults : List VTy → List Value
  | [] => []
  | t :: ts => default t :: defaults ts
end

mutual
/-- Substitute `θ j` for each type variable `var j`. -/
def subst (θ : Nat → VTy) : VTy → VTy
  | .int => .int
  | .logic => .logic
  | .char => .char
  | .float => .float
  | .arr t => .arr (subst θ t)
  | .opt t => .opt (subst θ t)
  | .tup ts => .tup (substL θ ts)
  | .var j => θ j
  | .ref ts args => .ref ts (substL θ args)
  | .vref es args => .vref es (substL θ args)
  | .dyn => .dyn
def substL (θ : Nat → VTy) : List VTy → List VTy
  | [] => []
  | t :: ts => subst θ t :: substL θ ts
end

theorem substL_eq_map (θ : Nat → VTy) : ∀ ts : List VTy, substL θ ts = ts.map (subst θ)
  | [] => rfl
  | t :: ts => by simp [substL, substL_eq_map θ ts]

@[simp] theorem subst_tup (θ : Nat → VTy) (ts : List VTy) : subst θ (.tup ts) = .tup (ts.map (subst θ)) := by
  simp [subst, substL_eq_map]
@[simp] theorem subst_arr (θ : Nat → VTy) (t : VTy) : subst θ (.arr t) = .arr (subst θ t) := by simp [subst]
@[simp] theorem subst_opt (θ : Nat → VTy) (t : VTy) : subst θ (.opt t) = .opt (subst θ t) := by simp [subst]
@[simp] theorem subst_int (θ : Nat → VTy) : subst θ .int = .int := by simp [subst]
@[simp] theorem subst_logic (θ : Nat → VTy) : subst θ .logic = .logic := by simp [subst]
@[simp] theorem subst_char (θ : Nat → VTy) : subst θ .char = .char := by simp [subst]
@[simp] theorem subst_float (θ : Nat → VTy) : subst θ .float = .float := by simp [subst]
@[simp] theorem subst_var (θ : Nat → VTy) (j : Nat) : subst θ (.var j) = θ j := by simp [subst]
@[simp] theorem subst_ref (θ : Nat → VTy) (ts : List Nat) (args : List VTy) :
    subst θ (.ref ts args) = .ref ts (args.map (subst θ)) := by simp [subst, substL_eq_map]
@[simp] theorem subst_vref (θ : Nat → VTy) (es : List (Nat × List VTy)) (args : List VTy) :
    subst θ (.vref es args) = .vref es (args.map (subst θ)) := by simp [subst, substL_eq_map]
@[simp] theorem subst_void (θ : Nat → VTy) : subst θ void = void := by simp [void]
@[simp] theorem subst_str (θ : Nat → VTy) : subst θ str = str := by simp [str]
@[simp] theorem subst_dyn (θ : Nat → VTy) : subst θ .dyn = .dyn := by simp [subst]

mutual
/-- A type without type variables. -/
def closed : VTy → Bool
  | .var _ => false
  | .arr t | .opt t => closed t
  | .tup ts => closedL ts
  | .ref _ args | .vref _ args => closedL args
  | _ => true
def closedL : List VTy → Bool
  | [] => true
  | t :: ts => closed t && closedL ts
end

/-- A class's field type at the type arguments `args`: its `j`-th type
    parameter is `args[j]`, and `void` past them (so that instantiating
    commutes with substitution, `VTy.inst_subst`; a field read only uses
    field types whose variables are below `args.length`, `FieldTy`). -/
def inst (args : List VTy) (t : VTy) : VTy := t.subst fun j => args.getD j void

mutual
/-- `t` mentions only the type variables below `n`. -/
def varsBelow (n : Nat) : VTy → Bool
  | .var j => decide (j < n)
  | .arr t | .opt t => varsBelow n t
  | .tup ts => varsBelowL n ts
  | .ref _ args | .vref _ args => varsBelowL n args
  | _ => true
def varsBelowL (n : Nat) : List VTy → Bool
  | [] => true
  | t :: ts => varsBelow n t && varsBelowL n ts
end

mutual
/-- Subtyping, `t ≤ u` (#32): every value of `t` is a value of `u`. A
    reference type with fewer classes is below one with more, and with more
    type arguments below one with a prefix of them (#39: a `sub(t, u)` is a
    `base(t)`); arrays, options and tuples are covariant (they are immutable
    values); otherwise the types are equal. -/
def sub : VTy → VTy → Bool
  -- (every value is a `dyn`)
  | _, .dyn => true
  | .ref ts as, .ref us bs => ts.all us.contains && bs.isPrefixOf as
  -- (#351) a class's reference fits a view of it whose arguments are among
  -- the reference's; a reference through views fits one with, for each
  -- entry, the same one or one with a prefix of its view that the target's
  -- arguments fit in (an interface's parent sees the classes through a
  -- prefix of what it does)
  | .ref ts as, .vref es bs => ts.all fun t => es.any fun e =>
      e.1 == t && e.2.all (fun v => varsBelow as.length v) && bs.isPrefixOf (e.2.map (inst as))
  | .vref es as, .vref fs bs => es.all (fun e => fs.any fun e' =>
      e'.1 == e.1 && e'.2.isPrefixOf e.2 && (e' == e || decide (bs.length ≤ e'.2.length))) && bs.isPrefixOf as
  | .arr t, .arr u => sub t u
  | .opt t, .opt u => sub t u
  | .tup ts, .tup us => subL ts us
  | t, u => decide (t = u)
def subL : List VTy → List VTy → Bool
  | [], [] => true
  | t :: ts, u :: us => sub t u && subL ts us
  | _, _ => false
end

/-- Every type is below `dyn`. -/
@[simp] theorem sub_dyn (t : VTy) : t.sub .dyn = true := by cases t <;> rfl

/-- Only `dyn` is above `dyn`. -/
theorem dyn_sub_iff (w : VTy) : VTy.dyn.sub w = true ↔ w = .dyn := by cases w <;> simp [sub]

end VTy

/-- The typing of a heap (#39): each object's class tag and type arguments.
    It is a ghost: objects do not record their type arguments. -/
abbrev HeapTy := List (Nat × List VTy)

mutual
/-- `v` has type `t`, in a heap whose objects have the classes and type
    arguments `Ξ`. -/
def hasTy (Ξ : HeapTy) : Value → VTy → Bool
  | _, .dyn => true
  | .int _, .int => true
  | .logic _, .logic => true
  | .char c, .char => decide (c < 256)
  | .float _, .float => true
  | .arr vs, .arr t => allTy Ξ vs.toList t
  | .tup vs, .tup ts => allTys Ξ vs ts
  | .none, .opt _ => true
  | .some v, .opt t => hasTy Ξ v t
  | .ref a, .ref ts args => match Ξ[a]? with
    | some (t, args') => ts.contains t && args.isPrefixOf args'
    | none => false
  | .ref a, .vref es args => match Ξ[a]? with
    | some (t, args') => es.any fun e => e.1 == t && args.isPrefixOf (e.2.map (VTy.inst args'))
    | none => false
  | _, _ => false
/-- Every element of `vs` has type `t`. -/
def allTy (Ξ : HeapTy) : List Value → VTy → Bool
  | [], _ => true
  | v :: vs, t => hasTy Ξ v t && allTy Ξ vs t
/-- The elements of `vs` have the types `ts`, pointwise. -/
def allTys (Ξ : HeapTy) : List Value → List VTy → Bool
  | [], [] => true
  | v :: vs, t :: ts => hasTy Ξ v t && allTys Ξ vs ts
  | [], _ :: _ => false
  | _ :: _, [] => false
end

/-- Every value is a `dyn`. -/
@[simp] theorem hasTy_dyn (Ξ : HeapTy) (v : Value) : hasTy Ξ v .dyn = true := by cases v <;> rfl

/-- The certificate of a program's types: each function's parameter types and
    result type, by function index, each class's field types, by tag, and the
    classes and type arguments of the prototype objects that `Main`'s
    prelude allocates first (#37): a literal may refer to them, as every
    heap starts with them. -/
structure Sigs where
  fns : List (List VTy × VTy)
  /-- Each class's field types, in terms of its type parameters (#39). -/
  classes : List (List VTy) := []
  /-- The prototypes: each one's class and (closed) type arguments. -/
  protos : HeapTy := []
  /-- Each class's pins (#142, #209): for each of its Verse Core type
      arguments, `some c` when the class fixes it to `c`, a type over the
      class's type arguments (`var i` is argument `i`), else `none`. A pin
      fixes an argument to a closed type (`int_box := class(box(int))` has
      `[some int]`) or relates it to others (`dup(t) := class(pair(t, t))`
      has `[none, some (var 0)]`). -/
  pins : List (List (Option VTy)) := []

/-- The pins of class `t`. -/
def Sigs.pinsOf (S : Sigs) (t : Nat) : List (Option VTy) := (S.pins[t]?).getD []

mutual
/-- Whether type variable `j` occurs in a type. -/
def VTy.hasVar (j : Nat) : VTy → Bool
  | .var i => i == j
  | .arr t | .opt t => VTy.hasVar j t
  | .tup ts => VTy.hasVarL j ts
  | .ref _ args | .vref _ args => VTy.hasVarL j args
  | _ => false
def VTy.hasVarL (j : Nat) : List VTy → Bool
  | [] => false
  | t :: ts => VTy.hasVar j t || VTy.hasVarL j ts
end

/-- The type arguments among `args` that a class's pins `ps` fix (#142),
    each with its pin (over the arguments: see `VTy.pinsOK`). -/
def VTy.pinPairs : List (Option VTy) → List VTy → List (VTy × VTy)
  | some c :: ps, a :: as => (a, c) :: VTy.pinPairs ps as
  | none :: ps, _ :: as => VTy.pinPairs ps as
  | _, _ => []

/-- Pins `ps` mention only the first `n` type arguments, so type arguments
    `a` of length `n` agree with them whenever an extension of `a` agrees
    with pins that start with `ps`. -/
def VTy.pinsBelow (ps : List (Option VTy)) (n : Nat) : Bool :=
  ps.all fun o => o.all (VTy.varsBelow n)

/-- Type arguments `args` agree with pins `ps` (#142, #209): there are at
    least as many as pins, and each pinned argument is its pin at `args`.
    (So an object of a class with pins has all of its type arguments:
    those a dispatch opens, `Typed.dispatch`.) -/
def VTy.pinsOK (ps : List (Option VTy)) (args : List VTy) : Bool :=
  decide (ps.length ≤ args.length) && (VTy.pinPairs ps args).all fun p => decide (p.1 = p.2.inst args)

/-- `k` fresh type variables, from `N` on: the type arguments a dispatch
    opens beyond the receiver's (#209). -/
def VTy.ext (N k : Nat) : List VTy := (List.range k).map fun i => .var (N + i)

/-- When `k > 0`, the pins `P` on `n + k` type arguments are pins on all of
    them: an object that agrees with them has at least `n + k`. -/
def VTy.extOK (P : List (Option VTy)) (n k : Nat) : Bool :=
  k == 0 || P.length == n + k

/-- `μ` refines type arguments `args` by pins `ps` (#142, #209): it is a most
    general substitution that makes them agree with the pins. Every other
    one factors through it (`Core/Unify.lean` finds one when there is any). -/
def PinRefines (ps : List (Option VTy)) (args : List VTy) (μ : Nat → VTy) : Prop :=
  VTy.pinsOK ps (args.map (VTy.subst μ)) = true ∧
  ∀ R, VTy.pinsOK ps (args.map (VTy.subst R)) = true → ∀ j, (μ j).subst R = R j

/-- `μ` refines the type arguments `X` that an object behind a reference
    through a view `φ` has (#351): a most general substitution that makes
    them agree with the pins `ps` and the reference's arguments `a` a prefix
    of the view at them. Every other one factors through it. -/
def ViewRefines (ps : List (Option VTy)) (φ a X : List VTy) (μ : Nat → VTy) : Prop :=
  (VTy.pinsOK ps (X.map (VTy.subst μ)) = true ∧
    a.map (VTy.subst μ) <+: (φ.map (VTy.inst X)).map (VTy.subst μ)) ∧
  ∀ R, VTy.pinsOK ps (X.map (VTy.subst R)) = true →
    a.map (VTy.subst R) <+: (φ.map (VTy.inst X)).map (VTy.subst R) → ∀ j, (μ j).subst R = R j

/-- The typing of primitives: `PrimTy op ts τ` when `op` applied to values
    of types `ts` gives a value of type `τ`. -/
inductive PrimTy : Prim → List VTy → VTy → Prop
  | rational {op} : op ∈ [Prim.add, .sub, .mul, .quotient] →
      PrimTy op [.int, .int, .int, .int] (.tup [.int, .int])
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
  | farith {op} : op ∈ [Prim.fadd, .fsub, .fmul, .fdiv, .fmin, .fmax, .fpow, .fatan2] →
      PrimTy op [.float, .float] .float
  | funary {op} : op ∈ [Prim.fneg, .fabs, .fsqrt, .fexp, .fln, .fsin, .fcos, .ftan, .fasin, .facos,
      .fatan, .fisFinite, .fsinh, .fcosh, .ftanh, .fasinh, .facosh, .fatanh] → PrimTy op [.float] .float
  | fcmp {op} : op ∈ [Prim.flt, .fle, .fgt, .fge] → PrimTy op [.float, .float] .float
  | fofInt : PrimTy .fofInt [.int] .float
  | fofBits : PrimTy .fofBits [.int] .float
  | ftoInt {op} : op ∈ [Prim.ffloor, .fceil, .fround, .ftrunc] → PrimTy op [.float] .int
  | toStrFloat : PrimTy .toStr [.float] VTy.str
  | fail {t} : PrimTy .fail [] t
  | userErr {t} : PrimTy .userErr [] t

/-- Field `k` has type `τ` in every class of `ts`, at the type arguments
    `args`, mentioning no type parameter past them (so that it has that type
    in every object whose arguments extend `args`). -/
def FieldTy (S : Sigs) (ts : List Nat) (args : List VTy) (k : Nat) (τ : VTy) : Prop :=
  ∀ t ∈ ts, ∃ fs f, S.classes[t]? = some fs ∧ fs[k]? = some f ∧ f.varsBelow args.length = true ∧
    f.inst args = τ

mutual
/-- `Typed S Γ ρ e τ`: in a function whose slots have types `Γ` and whose
    result type is `ρ`, `e` has type `τ`. `break`, `return`, `false?` and
    `Err()` have every type. -/
inductive Typed (S : Sigs) (Γ : List VTy) (ρ : VTy) : Expr → VTy → Prop
  /-- A literal may refer only to the prototypes, which every heap starts with. -/
  | lit {v τ} : hasTy S.protos v τ = true → Typed S Γ ρ (.lit v) τ
  | local {i τ} : Γ[i]? = some τ → Typed S Γ ρ (.local i) τ
  /-- Subsumption: an expression of a type has every type above it (#32). -/
  | sub {e t u} : Typed S Γ ρ e t → t.sub u = true → Typed S Γ ρ e u
  | assign {i e τ} : Γ[i]? = some τ → Typed S Γ ρ e τ → Typed S Γ ρ (.assign i e) τ
  | seq {a b σ τ} : Typed S Γ ρ a σ → Typed S Γ ρ b τ → Typed S Γ ρ (.seq a b) τ
  | prim {op es ts τ} : TypedL S Γ ρ es ts → PrimTy op ts τ → Typed S Γ ρ (.prim op es) τ
  /-- A call instantiates the callee's type variables with any `θ`. -/
  | call {f es ps τ} (θ : Nat → VTy) : S.fns[f]? = some (ps, τ) → TypedL S Γ ρ es (ps.map (VTy.subst θ)) →
      Typed S Γ ρ (.call f es) (τ.subst θ)
  | ite {c t e σ τ} : Typed S Γ ρ c σ → Typed S Γ ρ t τ → Typed S Γ ρ e τ →
      Typed S Γ ρ (.ite c t e) τ
  | forE {i it filt body τe σ τb} : Γ[i]? = some τe → Typed S Γ ρ it (.arr τe) →
      Typed S Γ ρ filt σ → Typed S Γ ρ body τb → Typed S Γ ρ (.forE i it filt body) (.arr τb)
  | loop {b σ} : Typed S Γ ρ b σ → Typed S Γ ρ (.loop b) VTy.void
  | brk {τ} : Typed S Γ ρ .brk τ
  | ret {e τ} : Typed S Γ ρ e ρ → Typed S Γ ρ (.ret e) τ
  | print {e} : Typed S Γ ρ e VTy.str → Typed S Γ ρ (.print e) VTy.void
  /-- A new object of class `t`, its fields given in order, at type
      arguments that agree with its class's pins. -/
  | heap_new {t es fs ts args} : S.classes[t]? = some fs → t ∈ ts → VTy.pinsOK (S.pinsOf t) args = true →
      TypedL S Γ ρ es (fs.map (VTy.inst args)) → Typed S Γ ρ (.heap (.new t) es) (.ref ts args)
  | heap_get {k e ts args τ} : Typed S Γ ρ e (.ref ts args) → FieldTy S ts args k τ →
      Typed S Γ ρ (.heap (.get k) [e]) τ
  | heap_set {k e v ts args τ} : Typed S Γ ρ e (.ref ts args) → FieldTy S ts args k τ →
      Typed S Γ ρ v τ → Typed S Γ ρ (.heap (.set k) [e, v]) τ
  | heap_tag {e ts args} : Typed S Γ ρ e (.ref ts args) → Typed S Γ ρ (.heap .tag [e]) .int
  /-- A cast: it fails unless the object's class is one of `us`. -/
  | heap_isTag {e ts args us} : Typed S Γ ρ e (.ref ts args) →
      Typed S Γ ρ (.heap (.isTag us) [e]) (.ref us args)
  /-- A cast of a reference through views (#351): an object of a class of
      `us`, at type arguments that the view does not tell. -/
  | heap_isTag_v {e es args us} : Typed S Γ ρ e (.vref es args) →
      Typed S Γ ρ (.heap (.isTag us) [e]) (.ref us [])
  /-- **Dispatch through a view** (#351): a call of `f` on the object in
      slot `y`, of type `vref ents a`, when its class is one of `us`, else
      `e`. Every entry for a class of `us` has the same view `φ`, which
      mentions only its first `k` type arguments, on all of which its pins
      are `P`. The call is typed with the receiver at `k` fresh type
      variables `ext` (from `N` on), refined by `μ`, which makes them agree
      with the pins and `a` a prefix of `φ` at them. When the branch runs,
      the object's first `k` arguments for `ext` do so, so that substitution
      factors through `μ`. -/
  | dispatch_view {y us f es e ents a ps τ σs τ' P φ} (k N : Nat) (θ μ : Nat → VTy) :
      Γ[y]? = some (.vref ents a) → (∀ e ∈ ents, e.1 ∈ us → e.2 = φ) → (∀ v ∈ φ, v.varsBelow k = true) →
      (∀ t ∈ us, (S.pinsOf t).take k = P) → VTy.pinsBelow P k = true → VTy.extOK P 0 k = true →
      VTy.varsBelowL N a = true → VTy.varsBelowL N σs = true → τ'.varsBelow N = true →
      ViewRefines P φ a (VTy.ext N k) μ →
      S.fns[f]? = some (ps, τ) → TypedL S Γ ρ es σs →
      VTy.subL ((VTy.ref us (VTy.ext N k) :: σs).map (VTy.subst μ)) (ps.map (VTy.subst θ)) = true →
      (τ.subst θ).sub (τ'.subst μ) = true → Typed S Γ ρ e τ' →
      Typed S Γ ρ (.ite (.heap (.isTag us) [.local y]) (.call f (.local y :: es)) e) τ'
  /-- When no substitution makes the `k` fresh arguments agree with the
      pins and `a` a prefix of the view at them, the call through the view
      cannot run (#351). -/
  | dispatch_view_none {y us f es e ents a τ' P φ} (k N : Nat) :
      Γ[y]? = some (.vref ents a) → (∀ e ∈ ents, e.1 ∈ us → e.2 = φ) → (∀ v ∈ φ, v.varsBelow k = true) →
      (∀ t ∈ us, (S.pinsOf t).take k = P) → VTy.pinsBelow P k = true → VTy.extOK P 0 k = true →
      VTy.varsBelowL N a = true →
      (∀ μ, VTy.pinsOK P ((VTy.ext N k).map (VTy.subst μ)) = true →
        ¬ a.map (VTy.subst μ) <+: (φ.map (VTy.inst (VTy.ext N k))).map (VTy.subst μ)) → Typed S Γ ρ e τ' →
      Typed S Γ ρ (.ite (.heap (.isTag us) [.local y]) (.call f (.local y :: es)) e) τ'
  /-- **Dispatch to classes that fix type arguments** (#142, #209): a call
      of `f` on the object in slot `y` when its class is one of `us`, else
      `e`. `y`'s type arguments `a` are extended by `k` fresh type
      variables `ext` (from `N` on, above every variable of `a`, of the
      other arguments' types `σs` and of `τ'`): the arguments an object of
      `us` has beyond `a`, which the code has no names for (existentials;
      the classes have pins on all of them, so an object has them). Every
      class of `us` pins the same arguments among those, in terms of them
      alone, and `μ` refines `a ++ ext` by the pins; the call is typed with
      `μ` applied to both sides. When the branch runs, the object's
      arguments agree with its pins and are `a ++ rest`: the substitution
      of `rest` for `ext` makes them agree, so it factors through `μ`, and
      the call is typed at it. -/
  | dispatch {y us f es e ts a ps τ σs τ' P} (k N : Nat) (θ μ : Nat → VTy) :
      Γ[y]? = some (.ref ts a) → (∀ t ∈ us, (S.pinsOf t).take (a.length + k) = P) →
      VTy.pinsBelow P (a.length + k) = true → VTy.extOK P a.length k = true →
      VTy.varsBelowL N a = true → VTy.varsBelowL N σs = true → τ'.varsBelow N = true →
      PinRefines P (a ++ VTy.ext N k) μ →
      S.fns[f]? = some (ps, τ) → TypedL S Γ ρ es σs →
      VTy.subL ((VTy.ref us (a ++ VTy.ext N k) :: σs).map (VTy.subst μ)) (ps.map (VTy.subst θ)) = true →
      (τ.subst θ).sub (τ'.subst μ) = true → Typed S Γ ρ e τ' →
      Typed S Γ ρ (.ite (.heap (.isTag us) [.local y]) (.call f (.local y :: es)) e) τ'
  /-- When no substitution makes `a ++ ext` agree with the pins, the call
      cannot run: no object of a class of `us` has type arguments starting
      with `a`. -/
  | dispatch_none {y us f es e ts a τ' P} (k N : Nat) :
      Γ[y]? = some (.ref ts a) → (∀ t ∈ us, (S.pinsOf t).take (a.length + k) = P) →
      VTy.pinsBelow P (a.length + k) = true → VTy.extOK P a.length k = true →
      VTy.varsBelowL N a = true →
      (∀ μ, VTy.pinsOK P ((a ++ VTy.ext N k).map (VTy.subst μ)) = false) → Typed S Γ ρ e τ' →
      Typed S Γ ρ (.ite (.heap (.isTag us) [.local y]) (.call f (.local y :: es)) e) τ'
inductive TypedL (S : Sigs) (Γ : List VTy) (ρ : VTy) : List Expr → List VTy → Prop
  | nil : TypedL S Γ ρ [] []
  | cons {e es τ ts} : Typed S Γ ρ e τ → TypedL S Γ ρ es ts → TypedL S Γ ρ (e :: es) (τ :: ts)
end

/-- The initialisation of slots `k, k+1, …` with the values of `ds`, before `e`. -/
def initPrefixE (k : Nat) : List Expr → Expr → Expr
  | [], e => e
  | d :: ds, e => .seq (.assign k d) (initPrefixE (k + 1) ds e)

/-- The initialisation of slots `k, k+1, …` with the default literals of `ts`. -/
def initPrefix (k : Nat) (ts : List VTy) (e : Expr) : Expr :=
  initPrefixE k (ts.map fun t => .lit t.default) e

mutual
/-- `DefaultE S a Γ d t`: `d` initialises a slot of type `t` in a function
    whose first `a` slots are its parameters: a literal of type `t`, a
    parameter of type `t`, a tuple of such, or (for a reference type) a new
    object of one of its classes, with defaults as fields. It reads only
    parameters, may allocate, and evaluates without failing to a value of
    type `t.subst θ` whenever the parameters hold values of their types
    under `θ`. -/
inductive DefaultE (S : Sigs) (a : Nat) (Γ : List VTy) : Expr → VTy → Prop
  | lit {v t} : hasTy S.protos v t = true → DefaultE S a Γ (.lit v) t
  | param {i t} : i < a → Γ[i]? = some t → DefaultE S a Γ (.local i) t
  | tup {ds ts} : DefaultEL S a Γ ds ts → DefaultE S a Γ (.prim .mkTup ds) (.tup ts)
  | new {t ds fs ts args} : S.classes[t]? = some fs → t ∈ ts → VTy.pinsOK (S.pinsOf t) args = true →
      DefaultEL S a Γ ds (fs.map (VTy.inst args)) → DefaultE S a Γ (.heap (.new t) ds) (.ref ts args)
  /-- A field of a parameter's object (#209): the value of a type argument
      that an object of a class with type parameters of its own holds, as
      code that opens them has none of its own. -/
  | field {i k ts args τ} : i < a → Γ[i]? = some (.ref ts args) → FieldTy S ts args k τ →
      DefaultE S a Γ (.heap (.get k) [.local i]) τ
  /-- A default is also one of every type above its own. -/
  | sub {d t u} : DefaultE S a Γ d t → t.sub u = true → DefaultE S a Γ d u
inductive DefaultEL (S : Sigs) (a : Nat) (Γ : List VTy) : List Expr → List VTy → Prop
  | nil : DefaultEL S a Γ [] []
  | cons {d ds t ts} : DefaultE S a Γ d t → DefaultEL S a Γ ds ts →
      DefaultEL S a Γ (d :: ds) (t :: ts)
end

/-- A function of signature `(ps, ρ)` is typed with slot types `Γ`. -/
structure FnTyped (S : Sigs) (fn : Fn) (ps : List VTy) (ρ : VTy) (Γ : List VTy) : Prop where
  arity : fn.arity = ps.length
  slots : Γ.length = fn.nslots
  params : Γ.take fn.arity = ps
  body : ∃ b ds, fn.body = initPrefixE fn.arity ds b ∧ DefaultEL S fn.arity Γ ds (Γ.drop fn.arity) ∧
    Typed S Γ ρ b ρ

/-- The prototypes' type arguments are closed (so a literal's typing holds
    at every instance, `Typed.subst`). -/
def Sigs.ClosedProtos (S : Sigs) : Prop := ∀ p ∈ S.protos, VTy.closedL p.2 = true

/-- What `Typed.subst` needs of the certificate. (A `new` agrees with its
    class's pins at every instance, whatever they are: `VTy.pinsOK_subst`.) -/
def Sigs.Closed (S : Sigs) : Prop := S.ClosedProtos

/-- The heap typing `Ξ` is the heap's: one entry per object, its class and
    type arguments, and every object has its class's field types at them. -/
def HeapOK (S : Sigs) (Ξ : HeapTy) (h : Array Obj) : Prop :=
  Ξ.length = h.size ∧
  (∀ (a : Nat) (o : Obj), h.toList[a]? = some o →
    ∃ args fs, Ξ[a]? = some (o.tag, args) ∧ S.classes[o.tag]? = some fs ∧
      allTys Ξ o.fields (fs.map (VTy.inst args)) = true ∧ VTy.pinsOK (S.pinsOf o.tag) args = true) ∧
  -- the heap starts with the prototypes (#37)
  S.protos <+: Ξ

/-- `Main`'s prelude (#37): allocate the prototype objects, in order, each
    with its fields as literals, then run `e`. A field may refer to any
    prototype, also one allocated after it (evaluating a literal does not
    look at the heap): prototypes may form cycles. They are shared and can
    be written; the front end only ever reads a slot after assigning it. -/
def protoPrelude : List (Nat × List Value) → Expr → Expr
  | [], e => e
  | (t, vs) :: rest, e => .seq (.heap (.new t) (vs.map .lit)) (protoPrelude rest e)

/-- The objects a prelude allocates. -/
def protoObjs (objs : List (Nat × List Value)) : Array Obj := (objs.map fun (t, vs) => ⟨t, vs⟩).toArray

/-- `P`'s `Main` is a prelude that allocates the prototypes (well typed),
    then calls a function `m` of `Main`'s signature (#37). -/
def PreludeOK (P : Prog) (S : Sigs) : Prop :=
  ∃ fn objs m, P.fns[P.main]? = some fn ∧ fn.arity = 0 ∧ fn.nslots = 0 ∧
    fn.body = protoPrelude objs (.call m []) ∧
    HeapOK S S.protos (protoObjs objs) ∧ S.fns[m]? = S.fns[P.main]?

/-- Every function of `P` is typed with its signature in `S`. -/
def ProgTyped (P : Prog) (S : Sigs) : Prop :=
  S.Closed ∧ P.fns.length = S.fns.length ∧
  (∀ (f : Nat) (fn : Fn) (ps : List VTy) (τ : VTy), P.fns[f]? = some fn → S.fns[f]? = some (ps, τ) →
    ∃ Γ, FnTyped S fn ps τ Γ) ∧
  -- the heap starts with the prototypes when the program starts (#37)
  (S.protos = [] ∨ PreludeOK P S)


/-- A frame agrees with slot types `Γ`. -/
def FrameOK (Ξ : HeapTy) (Γ : List VTy) (fr : List Value) : Prop := allTys Ξ fr Γ = true

/-- What a typed expression's outcome can be: a value of its type, a
    `return` of a value of the result type, anything else but a type error. -/
def ResOK (Ξ : HeapTy) (τ ρ : VTy) : Res → Prop
  | .ok v => hasTy Ξ v τ = true
  | .ret v => hasTy Ξ v ρ = true
  | .err k => k ≠ .type
  | .fail => True
  | .brk => True

def LResOK (Ξ : HeapTy) (ts : List VTy) (ρ : VTy) : LRes → Prop
  | .ok vs => allTys Ξ vs ts = true
  | .stop r => ResOK Ξ VTy.void ρ r ∧ r.isOk = false

/-! ### `veq` on values of one type -/

mutual
/-- `t` holds each of its values one way: it has no `dyn` in it, but under
    a reference (whose values are addresses). `dyn` holds every value, so
    the empty value there four ways. Every type but those with `dyn` is. -/
def VTy.dynFree : VTy → Bool
  | .dyn => false
  | .arr t | .opt t => VTy.dynFree t
  | .tup ts => VTy.dynFreeL ts
  | _ => true
def VTy.dynFreeL : List VTy → Bool
  | [] => true
  | t :: ts => VTy.dynFree t && VTy.dynFreeL ts
end

open Value in
/-- Two values of one type without `dyn` have one constructor, but for an
    empty option and a full one. -/
theorem hasTy_kind (Ξ : HeapTy) (a b : Value) (τ : VTy) (hτ : τ.dynFree = true)
    (ha : hasTy Ξ a τ = true) (hb : hasTy Ξ b τ = true) :
    kind a = kind b ∨ (kind a = 6 ∧ kind b = 7) ∨ (kind a = 7 ∧ kind b = 6) := by
  cases τ <;> simp [VTy.dynFree] at hτ <;> cases a <;> simp_all [hasTy, Value.kind] <;> cases b <;>
    simp_all [hasTy]

open Value in
mutual
/-- On values of one type, `veq` is equality: each type without `dyn` holds
    the empty value one way, so only a comparison of values of different
    types (in generic code, across types, or boxed as `dyn`s) can tell `veq`
    from `=`. -/
theorem veq_iff_eq_of_hasTy (Ξ : HeapTy) : ∀ (a b : Value) (τ : VTy), τ.dynFree = true →
    hasTy Ξ a τ = true → hasTy Ξ b τ = true → (veq a b = true ↔ a = b)
  | .int x, .int y, _, _, _, _ => by simp [veq]
  | .logic x, .logic y, _, _, _, _ => by cases x <;> cases y <;> simp [veq]
  | .char x, .char y, _, _, _, _ => by simp [veq]
  | .float x, .float y, _, _, _, _ => by simp [veq]
  | .arr a, .arr b, .arr t, hτ, ha, hb => by
    have ih := veqList_iff_eq_of_allTy Ξ a.toList b.toList t (by simpa [VTy.dynFree] using hτ)
      (by simpa [hasTy] using ha) (by simpa [hasTy] using hb)
    simp only [veq, Bool.and_eq_true, beq_iff_eq, Value.arr.injEq]
    rw [ih]
    constructor
    · rintro ⟨-, h⟩; exact Array.toList_inj.mp h
    · rintro rfl; exact ⟨rfl, rfl⟩
  | .tup xs, .tup ys, .tup ts, hτ, ha, hb => by
    have ih := veqList_iff_eq_of_allTys Ξ xs ys ts (by simpa [VTy.dynFree] using hτ)
      (by simpa [hasTy] using ha) (by simpa [hasTy] using hb)
    simp only [veq, Value.tup.injEq]; exact ih
  | .none, .none, _, _, _, _ => by simp [veq]
  | .none, .some _, _, _, _, _ => by simp [veq, isEmpty]
  | .some _, .none, _, _, _, _ => by simp [veq, isEmpty]
  | .some x, .some y, .opt t, hτ, ha, hb => by
    have ih := veq_iff_eq_of_hasTy Ξ x y t (by simpa [VTy.dynFree] using hτ)
      (by simpa [hasTy] using ha) (by simpa [hasTy] using hb)
    simp only [veq, Value.some.injEq]; exact ih
  | .ref x, .ref y, _, _, _, _ => by simp [veq]
  | .arr _, .arr _, .dyn, hτ, _, _ | .tup _, .tup _, .dyn, hτ, _, _
  | .some _, .some _, .dyn, hτ, _, _ => by simp [VTy.dynFree] at hτ
  | .int _, .logic _, τ, hτ, ha, hb | .int _, .char _, τ, hτ, ha, hb | .int _, .float _, τ, hτ, ha, hb
  | .int _, .arr _, τ, hτ, ha, hb
  | .int _, .tup _, τ, hτ, ha, hb | .int _, .none, τ, hτ, ha, hb | .int _, .some _, τ, hτ, ha, hb
  | .int _, .ref _, τ, hτ, ha, hb
  | .logic _, .int _, τ, hτ, ha, hb | .logic _, .char _, τ, hτ, ha, hb | .logic _, .float _, τ, hτ, ha, hb
  | .logic _, .arr _, τ, hτ, ha, hb
  | .logic _, .tup _, τ, hτ, ha, hb | .logic _, .none, τ, hτ, ha, hb | .logic _, .some _, τ, hτ, ha, hb
  | .logic _, .ref _, τ, hτ, ha, hb
  | .char _, .int _, τ, hτ, ha, hb | .char _, .logic _, τ, hτ, ha, hb | .char _, .float _, τ, hτ, ha, hb
  | .char _, .arr _, τ, hτ, ha, hb
  | .char _, .tup _, τ, hτ, ha, hb | .char _, .none, τ, hτ, ha, hb | .char _, .some _, τ, hτ, ha, hb
  | .char _, .ref _, τ, hτ, ha, hb
  | .float _, .int _, τ, hτ, ha, hb | .float _, .logic _, τ, hτ, ha, hb | .float _, .char _, τ, hτ, ha, hb
  | .float _, .arr _, τ, hτ, ha, hb
  | .float _, .tup _, τ, hτ, ha, hb | .float _, .none, τ, hτ, ha, hb | .float _, .some _, τ, hτ, ha, hb
  | .float _, .ref _, τ, hτ, ha, hb
  | .arr _, .int _, τ, hτ, ha, hb | .arr _, .logic _, τ, hτ, ha, hb | .arr _, .char _, τ, hτ, ha, hb
  | .arr _, .float _, τ, hτ, ha, hb
  | .arr _, .tup _, τ, hτ, ha, hb | .arr _, .none, τ, hτ, ha, hb | .arr _, .some _, τ, hτ, ha, hb
  | .arr _, .ref _, τ, hτ, ha, hb
  | .tup _, .int _, τ, hτ, ha, hb | .tup _, .logic _, τ, hτ, ha, hb | .tup _, .char _, τ, hτ, ha, hb
  | .tup _, .float _, τ, hτ, ha, hb
  | .tup _, .arr _, τ, hτ, ha, hb | .tup _, .none, τ, hτ, ha, hb | .tup _, .some _, τ, hτ, ha, hb
  | .tup _, .ref _, τ, hτ, ha, hb
  | .none, .int _, τ, hτ, ha, hb | .none, .logic _, τ, hτ, ha, hb | .none, .char _, τ, hτ, ha, hb
  | .none, .float _, τ, hτ, ha, hb
  | .none, .arr _, τ, hτ, ha, hb | .none, .tup _, τ, hτ, ha, hb | .none, .ref _, τ, hτ, ha, hb
  | .some _, .int _, τ, hτ, ha, hb
  | .some _, .logic _, τ, hτ, ha, hb | .some _, .char _, τ, hτ, ha, hb | .some _, .float _, τ, hτ, ha, hb
  | .some _, .arr _, τ, hτ, ha, hb
  | .some _, .tup _, τ, hτ, ha, hb | .some _, .ref _, τ, hτ, ha, hb | .ref _, .int _, τ, hτ, ha, hb
  | .ref _, .logic _, τ, hτ, ha, hb
  | .ref _, .char _, τ, hτ, ha, hb | .ref _, .float _, τ, hτ, ha, hb | .ref _, .arr _, τ, hτ, ha, hb
  | .ref _, .tup _, τ, hτ, ha, hb
  | .ref _, .none, τ, hτ, ha, hb | .ref _, .some _, τ, hτ, ha, hb =>
    absurd (hasTy_kind Ξ _ _ τ hτ ha hb) (by simp [kind])
theorem veqList_iff_eq_of_allTy (Ξ : HeapTy) : ∀ (xs ys : List Value) (t : VTy), t.dynFree = true →
    allTy Ξ xs t = true → allTy Ξ ys t = true → (veqList xs ys = true ↔ xs = ys)
  | [], [], _, _, _, _ => by simp [veqList]
  | [], _ :: _, _, _, _, _ => by simp [veqList]
  | _ :: _, [], _, _, _, _ => by simp [veqList]
  | x :: xs, y :: ys, t, hτ, ha, hb => by
    simp only [allTy, Bool.and_eq_true] at ha hb
    simp only [veqList, Bool.and_eq_true, List.cons.injEq]
    rw [veq_iff_eq_of_hasTy Ξ x y t hτ ha.1 hb.1, veqList_iff_eq_of_allTy Ξ xs ys t hτ ha.2 hb.2]
theorem veqList_iff_eq_of_allTys (Ξ : HeapTy) : ∀ (xs ys : List Value) (ts : List VTy),
    VTy.dynFreeL ts = true →
    allTys Ξ xs ts = true → allTys Ξ ys ts = true → (veqList xs ys = true ↔ xs = ys)
  | [], [], _, _, _, _ => by simp [veqList]
  | [], _ :: _, _, _, _, hb => by cases ‹List VTy› <;> simp_all [allTys]
  | _ :: _, [], _, _, ha, _ => by cases ‹List VTy› <;> simp_all [allTys]
  | x :: xs, y :: ys, t :: ts, hτ, ha, hb => by
    simp only [allTys, Bool.and_eq_true] at ha hb
    simp only [VTy.dynFreeL, Bool.and_eq_true] at hτ
    simp only [veqList, Bool.and_eq_true, List.cons.injEq]
    rw [veq_iff_eq_of_hasTy Ξ x y t hτ.1 ha.1 hb.1, veqList_iff_eq_of_allTys Ξ xs ys ts hτ.2 ha.2 hb.2]
  | _ :: _, _ :: _, [], _, ha, _ => by simp [allTys] at ha
end

end OpenVerse
