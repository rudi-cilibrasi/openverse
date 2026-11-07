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
  | .float => .float 0
  | .arr _ => .arr #[]
  | .opt _ => .none
  | .tup ts => .tup (defaults ts)
  -- no value has a type variable as its type; slots of such types are
  -- initialised from parameters instead (`DefaultE`)
  | .var _ => .void
  -- a reference has no default of its own: slots of such types start as a
  -- prototype, a new object or a parameter instead (`DefaultE`, #37)
  | .ref _ _ => .void
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
@[simp] theorem subst_void (θ : Nat → VTy) : subst θ void = void := by simp [void]
@[simp] theorem subst_str (θ : Nat → VTy) : subst θ str = str := by simp [str]

mutual
/-- A type without type variables. -/
def closed : VTy → Bool
  | .var _ => false
  | .arr t | .opt t => closed t
  | .tup ts => closedL ts
  | .ref _ args => closedL args
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
  | .ref _ args => varsBelowL n args
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
  | .ref ts as, .ref us bs => ts.all us.contains && bs.isPrefixOf as
  | .arr t, .arr u => sub t u
  | .opt t, .opt u => sub t u
  | .tup ts, .tup us => subL ts us
  | t, u => decide (t = u)
def subL : List VTy → List VTy → Bool
  | [], [] => true
  | t :: ts, u :: us => sub t u && subL ts us
  | _, _ => false
end

end VTy

/-- The typing of a heap (#39): each object's class tag and type arguments.
    It is a ghost: objects do not record their type arguments. -/
abbrev HeapTy := List (Nat × List VTy)

mutual
/-- `v` has type `t`, in a heap whose objects have the classes and type
    arguments `Ξ`. -/
def hasTy (Ξ : HeapTy) : Value → VTy → Bool
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
  | farith {op} : op ∈ [Prim.fadd, .fsub, .fmul, .fdiv, .fmin, .fmax] → PrimTy op [.float, .float] .float
  | funary {op} : op ∈ [Prim.fneg, .fabs] → PrimTy op [.float] .float
  | fcmp {op} : op ∈ [Prim.flt, .fle, .fgt, .fge] → PrimTy op [.float, .float] .float
  | fofInt : PrimTy .fofInt [.int] .float
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
  /-- A new object of class `t`, its fields given in order. -/
  | heap_new {t es fs ts args} : S.classes[t]? = some fs → t ∈ ts →
      TypedL S Γ ρ es (fs.map (VTy.inst args)) → Typed S Γ ρ (.heap (.new t) es) (.ref ts args)
  | heap_get {k e ts args τ} : Typed S Γ ρ e (.ref ts args) → FieldTy S ts args k τ →
      Typed S Γ ρ (.heap (.get k) [e]) τ
  | heap_set {k e v ts args τ} : Typed S Γ ρ e (.ref ts args) → FieldTy S ts args k τ →
      Typed S Γ ρ v τ → Typed S Γ ρ (.heap (.set k) [e, v]) τ
  | heap_tag {e ts args} : Typed S Γ ρ e (.ref ts args) → Typed S Γ ρ (.heap .tag [e]) .int
  /-- A cast: it fails unless the object's class is one of `us`. -/
  | heap_isTag {e ts args us} : Typed S Γ ρ e (.ref ts args) →
      Typed S Γ ρ (.heap (.isTag us) [e]) (.ref us args)
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
  | new {t ds fs ts args} : S.classes[t]? = some fs → t ∈ ts →
      DefaultEL S a Γ ds (fs.map (VTy.inst args)) → DefaultE S a Γ (.heap (.new t) ds) (.ref ts args)
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

/-- The heap typing `Ξ` is the heap's: one entry per object, its class and
    type arguments, and every object has its class's field types at them. -/
def HeapOK (S : Sigs) (Ξ : HeapTy) (h : Array Obj) : Prop :=
  Ξ.length = h.size ∧
  (∀ (a : Nat) (o : Obj), h.toList[a]? = some o →
    ∃ args fs, Ξ[a]? = some (o.tag, args) ∧ S.classes[o.tag]? = some fs ∧
      allTys Ξ o.fields (fs.map (VTy.inst args)) = true) ∧
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
  S.ClosedProtos ∧ P.fns.length = S.fns.length ∧
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

end OpenVerse
