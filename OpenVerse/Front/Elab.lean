/-
  OpenVerse front end — elaboration of surface Verse into Verse Core.

  * Names are resolved: locals to slots of the function's frame, functions
    and constants to program indices. Verse forbids shadowing; so does this.
  * Types are checked (int, logic, char, string = []char, []t, ?t, tuples,
    void), bidirectionally so that `false` and `array{}` take their type
    from context.
  * Failure discipline (Book of Verse ch. 8): an expression that can fail
    must be in a failure context — an `if` condition, a `for` clause,
    `option{}`, `logic{}`, `not`, the left of `or`, or a `<decides>`
    function body. "Can fail" is computed by `Expr.mayFail`, the very
    analysis the `<decides>` soundness theorem (`Eval.no_fail`) is about.
  * Derived forms use `OpenVerse.Core.Derived` (`not`, `or`, `option{}`,
    `logic{}`), whose rollback laws are proved.
  * The result is checked with `Prog.check` (proved to imply the hypotheses of
    the core theorems) before anyone runs it.
-/
import OpenVerse.Core.Check
import OpenVerse.Core.Derived
import OpenVerse.Core.TypeCheck
import OpenVerse.Core.Control
import OpenVerse.Front.Parser

namespace OpenVerse.Front
open OpenVerse

inductive Ty where
  | int | logic | char | void
  /-- A Unicode scalar value (spec: Char32); an `int` in Verse Core. -/
  | char32
  /-- The bottom type, of `break`, `return` and `Err()`. -/
  | never
  | arr : Ty → Ty
  | opt : Ty → Ty
  | tup : List Ty → Ty
  /-- A struct type (nominal), with the type arguments of a parametric
      struct: its value is the tuple of its fields. -/
  | struct : String → List Ty → Ty
  /-- An enum type (nominal): its value is the index of the enumerator. -/
  | enum : String → Ty
  /-- `[k]v`: in Verse Core, the array of its (key, value) pairs in insertion order. -/
  | map : Ty → Ty → Ty
  /-- A type parameter of the generic function (or parametric struct) being
      elaborated, opaque there (`comparable` when declared
      `t:subtype(comparable)`). In Verse Core it is a type variable `VTy.var`. -/
  | param : String → (comparable : Bool) → Ty
  deriving Repr, Inhabited

partial def Ty.eqv : Ty → Ty → Bool
  | .int, .int | .logic, .logic | .char, .char | .char32, .char32 | .void, .void | .never, .never => true
  | .arr a, .arr b => a.eqv b
  | .opt a, .opt b => a.eqv b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).all fun (a, b) => a.eqv b
  | .struct a as, .struct b bs =>
    a == b && as.length == bs.length && (as.zip bs).all fun (x, y) => x.eqv y
  | .enum a, .enum b => a == b
  | .map a b, .map c d => a.eqv c && b.eqv d
  | .param a _, .param b _ => a == b
  | _, _ => false

instance : BEq Ty := ⟨Ty.eqv⟩

partial def Ty.show : Ty → String
  | .int => "int" | .logic => "logic" | .char => "char" | .char32 => "char32" | .void => "void"
  | .never => "false"
  | .arr .char => "string"
  | .arr t => "[]" ++ t.show
  | .opt t => "?" ++ t.show
  | .tup ts => "tuple(" ++ ", ".intercalate (ts.map Ty.show) ++ ")"
  | .struct n [] => n
  | .struct n ts => n ++ "(" ++ ", ".intercalate (ts.map Ty.show) ++ ")"
  | .enum n => n
  | .map k v => "[" ++ k.show ++ "]" ++ v.show
  | .param n _ => n

def Ty.string : Ty := .arr .char

/-- Substitute type arguments for type parameters. -/
partial def Ty.subst (σ : List (String × Ty)) : Ty → Ty
  | .param n c => (σ.lookup n).getD (.param n c)
  | .arr t => .arr (t.subst σ)
  | .opt t => .opt (t.subst σ)
  | .tup ts => .tup (ts.map (Ty.subst σ))
  | .map k v => .map (k.subst σ) (v.subst σ)
  | .struct n ts => .struct n (ts.map (Ty.subst σ))
  | t => t

/-- `a` and `b` are equal up to a one-to-one renaming of type parameters,
    extending `m` (from `a`'s to `b`'s). -/
partial def Ty.alpha (m : List (String × String)) : Ty → Ty → Option (List (String × String))
  | .param x _, .param y _ => match m.lookup x with
    | some y' => if y' == y then some m else none
    | none => if m.any (·.2 == y) then none else some ((x, y) :: m)
  | .arr a, .arr b | .opt a, .opt b => Ty.alpha m a b
  | .tup as, .tup bs | .struct _ as, .struct _ bs =>
    if as.length != bs.length then none else (as.zip bs).foldlM (fun m (a, b) => Ty.alpha m a b) m
  | .map k v, .map k' v' => do Ty.alpha (← Ty.alpha m k k') v v'
  | a, b => if a.eqv b then some m else none

/-- Where a class or interface sits in the hierarchy (#18). -/
structure ClassInfo where
  /-- The superclass of a class (single inheritance). -/
  parent : Option String := none
  /-- The interfaces a class implements, or an interface extends. -/
  ifaces : List String := []
  isIface : Bool := false
  isAbstract : Bool := false
  isFinal : Bool := false
  deriving Inhabited

/-- The user-defined types of a program. -/
structure TyEnv where
  /-- Each struct: its fields in order (name, type, default value). The
      field types of a parametric struct mention its parameters as `Ty.param`. -/
  structs : List (String × List (String × Ty × Option SExpr)) := []
  /-- The structs that are classes or interfaces (Book of Verse ch. 10), in
      definition order: not comparable. -/
  classes : List String := []
  /-- The hierarchy of each class and interface. -/
  cinfo : List (String × ClassInfo) := []
  /-- The abstract methods (class or interface, method): their functions are
      never called. -/
  abstracts : List (String × String) := []
  /-- The type parameters of each parametric struct (name, declared comparable). -/
  sparams : List (String × List (String × Bool)) := []
  /-- Each enum: its enumerators in order. -/
  enums : List (String × List String) := []
  /-- The `var` fields of each class, inherited ones included (#34). -/
  varFields : List (String × String) := []
  /-- The `<unique>` classes: compared by identity (#34). -/
  uniques : List String := []
  /-- The prototype objects `Main`'s prelude allocates, in order (#37): the
      class each one is of, with its tag and fields. A slot of class type
      starts as a reference to one. -/
  protos : List (String × Nat × List Value) := []
  /-- The type arguments of each class's parametric superclass (#39), in
      terms of the class's own type parameters: `sub(t) := class(base(t))`
      gives `base ↦ [t]`. -/
  pargs : List (String × List Ty) := []
  /-- The class whose code each field default is, by (class, field): its
      type parameters are those the default mentions (#39). -/
  defaultHome : List ((String × String) × String) := []
  /-- The type parameters in scope, in order (the j-th is `VTy.var j` in
      Verse Core), and what they stand for: themselves (`Ty.param`) in a
      generic function or struct definition, the type arguments of a struct
      construction when its field defaults are elaborated. -/
  tvars : List (String × Ty) := []
  deriving Inhabited

/-- The fields of struct `n` applied to the type arguments `args`. -/
def TyEnv.fields (env : TyEnv) (n : String) (args : List Ty := []) : List (String × Ty × Option SExpr) :=
  let fs := (env.structs.lookup n).getD []
  match env.sparams.lookup n with
  | some ps =>
    let σ := (ps.map (·.1)).zip args
    fs.map fun (f, t, d) => (f, t.subst σ, d)
  | none => fs

def TyEnv.info (env : TyEnv) (c : String) : ClassInfo := (env.cinfo.lookup c).getD {}

/-- The type arguments of the superclass `T` of `d(args)` (along the class
    chain), or `[]` when `T` is not a parametric class above `d`. -/
partial def TyEnv.upArgs (env : TyEnv) (d : String) (args : List Ty) (T : String) : List Ty :=
  if d == T then args
  else match (env.info d).parent, env.pargs.lookup d with
    | some q, some qargs =>
      let σ := (((env.sparams.lookup d).getD []).map (·.1)).zip args
      env.upArgs q (qargs.map (·.subst σ)) T
    | some q, none => env.upArgs q [] T
    | none, _ => []

/-- The root of `d`'s class chain. -/
partial def TyEnv.rootOf (env : TyEnv) (d : String) : String :=
  match (env.info d).parent with
  | some q => env.rootOf q
  | none => d

/-- The type parameters of class `d` that are not among its parent's type
    arguments (#39): `u`, for `pair(t, u) := class(base(t))`. -/
def TyEnv.extraParams (env : TyEnv) (d : String) : List String :=
  let ps := ((env.sparams.lookup d).getD []).map (·.1)
  let qargs := (env.pargs.lookup d).getD []
  ps.filter fun p => !qargs.any fun | .param v _ => v == p | _ => false

/-- The type arguments of `d(args)` in Verse Core (#39): its parent's, then
    its own type parameters that are not among them. So a class's are an
    extension of every class's above it, and objects of `pair(int, string)
    := class(base(int))` are also `base(int)`s (Core's prefix subtyping). -/
partial def TyEnv.coreArgs (env : TyEnv) (d : String) (args : List Ty) : List Ty :=
  let ps := ((env.sparams.lookup d).getD []).map (·.1)
  let σ := ps.zip args
  let extras := (env.extraParams d).map fun p => (σ.lookup p).getD Ty.void
  match (env.info d).parent with
  | some q => env.coreArgs q (((env.pargs.lookup d).getD []).map (·.subst σ)) ++ extras
  | none => args

/-- Where each type parameter of class `d` sits among its Verse Core type
    arguments (`coreArgs`): the type variables of its class table entry. -/
def TyEnv.coreVars (env : TyEnv) (d : String) : List (String × Ty) :=
  let ps := (env.sparams.lookup d).getD []
  (env.coreArgs d (ps.map fun (v, c) => Ty.param v c)).zipIdx.map fun
    | (.param v c, _) => (v, Ty.param v c)
    | (_, j) => (s!"$arg{j}", Ty.void)

/-- The type arguments of `d` below `T`, for an instance of `T(targs)`: its
    type parameters at their places among the Verse Core type arguments. -/
def TyEnv.argsBelow (env : TyEnv) (T : String) (targs : List Ty) (d : String) : List Ty :=
  if d == T then targs else
  let cs := env.coreArgs T targs
  let vars := env.coreVars d
  ((env.sparams.lookup d).getD []).map fun (v, _) =>
    match vars.findIdx? (·.1 == v) with
    | some j => cs.getD j Ty.void
    | none => Ty.void



/-- A class or interface and everything above it: its class chain first,
    nearest first, then the interfaces of the chain, breadth first. This is
    also the order in which a method's implementation is looked up. -/
def TyEnv.supers (env : TyEnv) (c : String) : List String := Id.run do
  let mut chain := [c]
  let mut cur := c
  for _ in [0:env.cinfo.length] do
    match (env.info cur).parent with
    | some q => if chain.contains q then break else chain := chain ++ [q]; cur := q
    | none => break
  let mut out := chain
  let mut frontier := chain.flatMap fun k => (env.info k).ifaces
  for _ in [0:env.cinfo.length + 1] do
    let new := (frontier.filter (!out.contains ·)).eraseDups
    if new.isEmpty then break
    out := out ++ new
    frontier := new.flatMap fun k => (env.info k).ifaces
  return out

/-- `d` is `T` or below it. -/
def TyEnv.isSub (env : TyEnv) (d T : String) : Bool := (env.supers d).contains T

/-- The type arguments of class `D`, above or below `T`, for an instance of
    `T(targs)` (#39). -/
def TyEnv.argsAt (env : TyEnv) (T : String) (targs : List Ty) (D : String) : List Ty :=
  if env.isSub T D then env.upArgs T targs D else env.argsBelow T targs D

/-- The fields of class `d`, below `T`, with the types they have in an
    object that is a `T(targs)`: each as the topmost class that has it gives
    it, at that class's type arguments there. They are the types of the
    class table at the Verse Core type arguments of `T(targs)`, also for a
    `d` whose own type arguments differ (a placeholder, never read). -/
def TyEnv.fieldsSeen (env : TyEnv) (T : String) (targs : List Ty) (d : String) :
    List (String × Ty × Option SExpr) :=
  let chain := ((env.supers d).filter fun x => !(env.info x).isIface).reverse
  (env.fields d).map fun (f, t, dflt) =>
    match chain.find? fun D => (env.fields D).any (·.1 == f) with
    | some D =>
      let tD := (((env.fields D).find? (·.1 == f)).map (·.2.1)).getD t
      let σ := (((env.sparams.lookup D).getD []).map (·.1)).zip (env.argsAt T targs D)
      (f, tD.subst σ, dflt)
    | none => (f, t, dflt)

/-- The concrete classes at or below `T`, in definition order: a value of
    static type `T` holds an instance of one of them. In Verse Core it is the
    tuple of one option per such class, holding that class's fields (#18). -/
def TyEnv.concreteBelow (env : TyEnv) (T : String) : List String :=
  env.classes.filter fun d =>
    let i := env.info d
    !i.isIface && !i.isAbstract && env.isSub d T

/-- A class represented by references to heap objects (#34): every class
    and interface, parametric ones too (#39), with a concrete class below. -/
def TyEnv.isRefClass (env : TyEnv) (n : String) : Bool :=
  env.classes.contains n &&
    -- with no concrete class below, `n` has no instance: it stays the (empty)
    -- value of #18, so a variable of its type needs no placeholder
    env.classes.any fun d => let i := env.info d; !i.isIface && !i.isAbstract && (env.supers d).contains n

/-- The class tag of class `d` in Verse Core: its index in definition order. -/
def TyEnv.tagOf (env : TyEnv) (d : String) : Nat := (env.classes.idxOf? d).getD 0

/-- The tags of the concrete classes at or below `T`: a reference of static
    type `T` refers to an object of one of them. -/
def TyEnv.refTags (env : TyEnv) (T : String) : List Nat := (env.concreteBelow T).map env.tagOf

/-- A class or interface with no concrete class below it: no value of its
    type can exist, so code that uses one is unreachable. -/
def TyEnv.isEmptyClass (env : TyEnv) (n : String) : Bool :=
  env.classes.contains n && !env.isRefClass n

/-- Whether field `f` of class `c` is a `var`. -/
def TyEnv.isVarField (env : TyEnv) (c f : String) : Bool := env.varFields.contains (c, f)

/-- Whether a value of type `t` can hold an object that can change or has
    an identity: one of a class below a reference class with a `var` field,
    or `<unique>`. -/
partial def Ty.holdsMutable (env : TyEnv) (t : Ty) (seen : List String := []) : Bool :=
  match t with
  | .arr t | .opt t => t.holdsMutable env seen
  | .tup ts => ts.any (·.holdsMutable env seen)
  | .map k v => k.holdsMutable env seen || v.holdsMutable env seen
  | .struct n ts =>
    if env.classes.contains n then
      -- an object below `n`, or one its fields reach (by instantiation, #39;
      -- one that grows without end is taken to)
      let key := (Ty.struct n ts).show
      if seen.length > 16 || key.length > 400 then true
      else (env.concreteBelow n).any fun d =>
        (env.supers d).any env.uniques.contains ||
        (env.fieldsSeen n ts d).any fun (f, ft, _) =>
          env.varFields.contains (d, f) || (!seen.contains key && ft.holdsMutable env (key :: seen))
    else (env.fields n ts).any fun (_, t, _) => t.holdsMutable env seen
  | _ => false

/-- Whether `c` or a class or interface above it is `<unique>`. -/
def TyEnv.isUnique (env : TyEnv) (c : String) : Bool := (env.supers c).any env.uniques.contains

/-- The field types a value of struct or class type `n` holds in Verse Core:
    a struct's, or those of every concrete class below a (parametric) class.
    A reference holds none: the fields are in the heap. -/
def TyEnv.repFieldTys (env : TyEnv) (n : String) (args : List Ty) : List Ty :=
  if env.isRefClass n then []
  else if env.classes.contains n then
    (env.concreteBelow n).flatMap fun d => (env.fields d (if d == n then args else [])).map (·.2.1)
  else (env.fields n args).map (·.2.1)

/-- The struct names a type mentions (not looking inside those structs). -/
partial def Ty.structNames : Ty → List String
  | .struct n ts => n :: ts.flatMap Ty.structNames
  | .arr t | .opt t => t.structNames
  | .tup ts => ts.flatMap Ty.structNames
  | .map k v => k.structNames ++ v.structNames
  | _ => []

/-- A struct that contains itself, through any chain of fields (Verse Core
    types are finite trees, so such a struct has no representation). -/
def TyEnv.recursiveStruct? (env : TyEnv) : Option String :=
  let deps (n : String) : List String :=
    (env.repFieldTys n []).flatMap Ty.structNames
  -- the structs reachable from `n` in at most `env.structs.length` steps
  let reach (n : String) : List String := Id.run do
    let mut seen : List String := []
    let mut frontier := deps n
    for _ in [0:env.structs.length + 1] do
      let new := frontier.filter (!seen.contains ·)
      seen := seen ++ new
      frontier := new.flatMap deps
    return seen
  (env.structs.map (·.1)).find? fun n => (reach n).contains n

/-- The Verse Core type of a front-end type (`false`, the bottom type, has
    no values; slots and signatures never have it). -/
partial def Ty.toVTy (env : TyEnv) : Ty → VTy
  | .int | .char32 => .int
  | .logic => .logic
  | .char => .char
  | .void => VTy.void
  | .never => VTy.void
  | .arr t => .arr (t.toVTy env)
  | .opt t => .opt (t.toVTy env)
  | .tup ts => .tup (ts.map (Ty.toVTy env))
  | .struct n ts =>
    if env.isRefClass n then .ref (env.refTags n) ((env.coreArgs n ts).map (Ty.toVTy env))
    else if env.classes.contains n then
      -- one option per concrete class at or below `n`
      .tup ((env.concreteBelow n).map fun d =>
        .opt (.tup ((env.fields d (if d == n then ts else [])).map fun (_, t, _) => t.toVTy env)))
    else .tup ((env.fields n ts).map fun (_, t, _) => t.toVTy env)
  | .enum _ => .int
  | .map k v => .arr (.tup [k.toVTy env, v.toVTy env])
  -- the j-th type parameter of the generic function being elaborated
  | .param n _ => match env.tvars.findIdx? (·.1 == n) with
    | some j => .var j
    | none => VTy.void

/-- The type parameters a type mentions. -/
partial def Ty.params : Ty → List String
  | .param n _ => [n]
  | .arr t | .opt t => t.params
  | .tup ts | .struct _ ts => ts.flatMap Ty.params
  | .map k v => k.params ++ v.params
  | _ => []

/-- Whether `false` (the bottom type) occurs in a type. -/
partial def Ty.hasNever : Ty → Bool
  | .never => true
  | .arr t | .opt t => t.hasNever
  | .tup ts => ts.any Ty.hasNever
  | .map k v => k.hasNever || v.hasNever
  | _ => false

/-- First-order matching of a generic signature's type `pat` against the type
    `act` of an argument, extending the binding `σ` of the callee's type
    parameters. `false` (the bottom type) matches anything and binds nothing. -/
partial def Ty.matchArg (env : TyEnv) (σ : List (String × Ty)) : Ty → Ty → Option (List (String × Ty))
  | _, .never => some σ
  | .param v _, a =>
    match σ.lookup v with
    | some b => if b.eqv a then some σ else none
    -- a type with `false` inside, like that of `array{Err()}`, binds nothing either
    | none => if a.hasNever then some σ else some ((v, a) :: σ)
  | .arr p, .arr a | .opt p, .opt a => Ty.matchArg env σ p a
  | .tup ps, .tup as =>
    if ps.length != as.length then none
    else (ps.zip as).foldlM (fun σ (p, a) => Ty.matchArg env σ p a) σ
  | .map pk pv, .map ak av => do Ty.matchArg env (← Ty.matchArg env σ pk ak) pv av
  | .struct n ps, .struct m as =>
    -- an instance of a class below `n` is one of `n`, at its type arguments there (#39)
    let as := if n != m && env.classes.contains m && env.isSub m n then env.upArgs m as n else as
    if (n != m && !(env.classes.contains m && env.isSub m n)) || ps.length != as.length then none
    else (ps.zip as).foldlM (fun σ (p, a) => Ty.matchArg env σ p a) σ
  | p, a => if p.eqv a then some σ else none

/-- At most `cap` nodes of the Verse Core tree of `t` (to bound the size of
    a type without walking one that doubles at each level). -/
def Ty.sizeUpTo (env : TyEnv) (cap : Nat) (t : Ty) : Nat := go cap [t]
where
  go : Nat → List Ty → Nat
    | 0, _ | _, [] => 0
    | b + 1, t :: rest =>
      let kids := match t with
        | .arr u | .opt u => [u]
        | .tup us => us
        -- a struct is the tuple of its fields in Verse Core, a class the
        -- options of the classes below it
        | .struct n us => env.repFieldTys n us
        | .map k v => [k, v]
        | _ => []
      1 + go b (kids ++ rest)

/-- The largest Verse Core representation of a type that openverse accepts:
    a parametric struct with two fields of its parameter doubles at each
    level of nesting. -/
def maxTySize : Nat := 100000

/-- Whether `=` and `<>` are defined on values of type `t`: every openverse
    type is comparable except a type parameter not declared
    `subtype(comparable)`, and the containers of one (Book of Verse §4.9). -/
partial def Ty.comparable (env : TyEnv) : Ty → Bool
  | .param _ c => c
  | .arr t | .opt t => t.comparable env
  | .tup ts => ts.all (Ty.comparable env)
  | .map k v => k.comparable env && v.comparable env
  -- a class is not comparable unless it is `<unique>` (compared by
  -- identity), nor a struct with a field that is not (one holding such a
  -- class, or a type argument)
  | .struct n ts =>
    if env.isRefClass n then env.isUnique n
    else !env.classes.contains n && ts.all (Ty.comparable env) &&
      (env.fields n ts).all fun (_, t, _) => t.comparable env
  | _ => true

def isComparable (env : TyEnv) : Ty → Bool
  | .never => false
  | t => t.comparable env

structure Local where
  name    : String
  slot    : Nat
  ty      : Ty
  mutable : Bool

/-- The heap effects (the spec draft's TransactFx). -/
def heapFx : List String := ["allocates", "reads", "writes"]

structure Sig where
  idx     : Nat
  name    : String
  params  : List Ty
  ret     : Ty
  decides : Bool
  isConst : Bool
  /-- The named parameters (the last ones of `params`): name and default. -/
  named   : List (String × Option SExpr) := []
  /-- A generic function's type parameters (name, declared comparable). Its
      `params` and `ret` mention them as `Ty.param`. Its Verse Core function
      takes one more hidden parameter per type parameter, after these: a
      value of that type (`witness`), from which its slots of that type are
      initialised (`slotDefault`). -/
  tparams : List (String × Bool) := []
  /-- The heap effects its specifiers allow (#35). -/
  fx : List String := heapFx
  deriving Inhabited

structure Ctx where
  sigs    : List Sig
  /-- The functions' `<decides>` flags, as a program, for `Expr.mayFail`. -/
  sigProg : Prog
  locals  : List Local := []
  canFail : Bool := false
  inLoop  : Bool := false
  /-- In a class's `block:` clauses (one method, `$block`), where a `return`
      would skip the clauses after it. -/
  inBlock : Bool := false
  retTy   : Ty := .void
  types   : TyEnv := {}
  /-- The field defaults being elaborated (struct, field), to reject a default
      that depends on itself. -/
  defaults : List (String × String) := []
  /-- In a generic function, the slot of the hidden parameter that holds a
      value of its first type parameter (the others follow), and the names of
      its type parameters, in order. A field default is elaborated with its
      struct's type parameters in `types.tvars`, but its hidden arguments
      still come from the enclosing function's. -/
  dictBase : Nat := 0
  dictVars : List String := []
  /-- In a method of class `c` (the function `c.M`): `c`. A bare name that is
      not a local is then looked up among the fields and methods of `Self`. -/
  selfClass : Option String := none

structure ESt where
  /-- The program's types, for conversions between class types (`coerce`). -/
  env : TyEnv := {}
  nslots : Nat := 0
  /-- The type of each slot allocated so far (the certificate for `Prog.checkTypes`). -/
  slotTys : Array Ty := #[]
  /-- The heap effects of the function so far (#35): `allocates`, `reads`,
      `writes`, each with where it first occurs and the function called
      there, if it comes from a call. -/
  fx : List (String × Pos × Option String) := []
  deriving Inhabited

abbrev EM := StateT ESt (Except String)

/-- The heap effects a function's specifiers allow: all of them by default
    and with `<transacts>`, none with `<computes>`, those named by
    `<allocates>`, `<reads>`, `<writes>`. -/
def allowedFx (effs : List String) : List String :=
  if effs.contains "transacts" then heapFx
  else
    let named := heapFx.filter effs.contains
    if !named.isEmpty then named
    else if effs.contains "computes" then []
    else heapFx

/-- Run `m`, attributing the heap effects it records first to `p` (a field
    or argument default: the effect is the construction's or the call's). -/
def fxAt (p : Pos) (m : EM α) : EM α := do
  let before := (← get).fx.length
  let r ← m
  modify fun st => { st with fx := st.fx.take before ++ (st.fx.drop before).map fun (k, _, v) => (k, p, v) }
  return r

/-- Record heap effects at `p` (of a call of `via`). -/
def noteFx (p : Pos) (ks : List String) (via : Option String := none) : EM Unit :=
  modify fun st => { st with fx := ks.foldl (fun acc k =>
    if acc.any (·.1 == k) then acc else acc ++ [(k, p, via)]) st.fx }

/-- An elaborated expression and its type. -/
structure R where
  e  : Expr
  ty : Ty


/-- A new slot of the current frame, holding values of type `t`. -/
def fresh (t : Ty) : EM Nat :=
  modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push t })

def eerr (p : Pos) (msg : String) : EM α := throw s!"{p.show}: {msg}"

/-- A class's fields cannot be set: they are immutable until `var` fields,
    which need reference semantics, are supported. Setting one would make
    the tuple representation observable. -/
def classSetMsg (c f : String) : String :=
  s!"field '{f}' of class {c} is not a var: declare it with var {f}:t = …"

/-- Whether every map key type inside `t` is comparable. -/
partial def Ty.mapKeysOK (env : TyEnv) : Ty → Bool
  | .map k v => k.comparable env && k.mapKeysOK env && v.mapKeysOK env
  | .arr t | .opt t => t.mapKeysOK env
  | .tup ts | .struct _ ts => ts.all (Ty.mapKeysOK env)
  | _ => true

/-- Why values of type `t` cannot be used where equality is needed. -/
def notComparable (env : TyEnv) (t : Ty) (what : String) : String :=
  match t with
  | .struct n _ =>
    if env.classes.contains n then
      s!"{what} must be comparable, and {t.show} is a class (only <unique> classes are comparable, by identity)"
    else notComparable.params t what
  | _ => notComparable.params t what
where
  params (t : Ty) (what : String) : String :=
  match t.params with
  | v :: _ => s!"{what} must be comparable, and {t.show} is not: declare {v}:subtype(comparable)"
  | [] => s!"{what} must be comparable, and {t.show} is not"

def builtins : List String :=
  ["Print", "ToString", "Floor", "Ceil", "Abs", "Min", "Max", "Quotient", "Mod", "Err"]

partial def resolveTy (env : TyEnv) (p : Pos) : STy → EM Ty
  | .name "int" => pure .int
  | .name "logic" => pure .logic
  | .name "char" => pure .char
  | .name "char32" => pure .char32
  | .name "string" => pure Ty.string
  | .name "void" => pure .void
  | .name "float" => eerr p "float is not supported by openverse v1"
  | .name n =>
    if let some t := env.tvars.lookup n then pure t
    else if (env.structs.lookup n).isSome then
      match env.sparams.lookup n with
      | some ps => eerr p s!"{n} is parametric: write {n}(…) with {ps.length} type argument(s)"
      | none => pure (.struct n [])
    else if (env.enums.lookup n).isSome then pure (.enum n)
    else eerr p s!"unknown type '{n}' (supported: int, logic, char, string, void, []t, ?t, tuple(…), and structs and enums)"
  | .arr t => return .arr (← resolveTy env p t)
  | .opt t => return .opt (← resolveTy env p t)
  | .tup [] => pure .void
  | .tup ts => return .tup (← ts.mapM (resolveTy env p))
  | .map k v => do
    let kt ← resolveTy env p k
    if !kt.comparable env then eerr p (notComparable env kt "a map key")
    return .map kt (← resolveTy env p v)
  | .app n args => do
    let ts ← args.mapM (resolveTy env p)
    match env.sparams.lookup n with
    | some ps =>
      if ps.length != ts.length then eerr p s!"{n} takes {ps.length} type argument(s), found {ts.length}"
      for ((v, c), t) in ps.zip ts do
        if c && !t.comparable env then eerr p (notComparable env t s!"type argument {v} of {n}")
      let t := Ty.struct n ts
      if t.sizeUpTo env (maxTySize + 1) > maxTySize then
        eerr p s!"the type {n}(…) is too large: its Verse Core representation has more than {maxTySize} nodes"
      return t
    | none =>
      if (env.structs.lookup n).isSome then eerr p s!"struct {n} takes no type arguments"
      else eerr p s!"unknown parametric type '{n}' (only structs can be parametric)"

def Ctx.lookup (ctx : Ctx) (n : String) : Option Local := ctx.locals.find? (·.name == n)
def Ctx.sig? (ctx : Ctx) (n : String) : Option Sig := ctx.sigs.find? (·.name == n)

/-- Class or interface `c` has method `m`, its own or inherited. -/
def Ctx.hasMethod (ctx : Ctx) (c m : String) : Bool :=
  (ctx.types.supers c).any fun e => (ctx.sig? s!"{e}.{m}").isSome

/-- Where the method `m` of `c` is declared, for the signature of a call: the
    most specific of the declarations at or above `c` and, among several,
    one whose result is below the others' (overrides may narrow it). -/
def Ctx.methodDecl? (ctx : Ctx) (c m : String) : Option String :=
  let env := ctx.types
  let cands := (env.supers c).filter fun e => (ctx.sig? s!"{e}.{m}").isSome
  let best := cands.filter fun e => !cands.any fun e' => e' != e && env.isSub e' e
  let retOf (e : String) : Ty := ((ctx.sig? s!"{e}.{m}").map (·.ret)).getD .void
  let below (a b : Ty) : Bool := a == b || match a, b with
    | .struct S [], .struct T [] => env.isSub S T
    | _, _ => false
  match best.find? (fun e => best.all fun e' => below (retOf e) (retOf e')) with
  | some e => some e
  | none => best.head?

/-- The most specific of the non-abstract definitions of method `m` among
    `ups`: one that no other is below (the class chain comes first in
    `supers`, and no interface is below a class, so a definition in the class
    chain wins over interface defaults; the order in which parents are listed
    does not matter). -/
def Ctx.mostSpecific? (ctx : Ctx) (ups : List String) (m : String) : Option String :=
  let cands := ups.filter fun e => (ctx.sig? s!"{e}.{m}").isSome && !ctx.types.abstracts.contains (e, m)
  cands.find? fun e => !cands.any fun e' => e' != e && ctx.types.isSub e' e

/-- The implementation of method `m` for an instance of class `d`. -/
def Ctx.implOf? (ctx : Ctx) (d m : String) : Option String :=
  ctx.mostSpecific? (ctx.types.supers d) m

def p2 (op : Prim) (a b : Expr) : Expr := .prim op [a, b]

/-- The slot of the hidden parameter for type parameter `n`. -/
def TyEnv.dictSlot? (env : TyEnv) (dictBase : Nat) (n : String) : Option Nat :=
  (env.tvars.findIdx? (·.1 == n)).map (dictBase + ·)

/-- A value of type `t`, built by an expression whose Verse Core type the
    checker infers exactly (`tc e none`): the hidden argument a call of a
    generic function passes for a type argument `t`. It is only ever used to
    initialise slots, so which value it is does not matter. A class
    reference is a fresh slot of exactly its type (`new` would infer only
    the class constructed), which starts as a placeholder. -/
partial def witness (env : TyEnv) (dictBase : Nat) (dictVars : List String) : Ty → EM Expr
  | .int | .char32 | .enum _ => pure (.lit (.int 0))
  | .logic => pure (.lit (.logic false))
  | .char => pure (.lit (.char 0))
  | .void | .never => pure (.lit .void)
  | .arr t => return .prim .mkArr [← witness env dictBase dictVars t]
  | .opt t => return .prim .mkSome [← witness env dictBase dictVars t]
  | .tup ts => return .prim .mkTup (← ts.mapM (witness env dictBase dictVars))
  | .map k v => return .prim .mkArr [.prim .mkTup [← witness env dictBase dictVars k, ← witness env dictBase dictVars v]]
  | .struct n ts => do
    if env.isRefClass n then return .local (← fresh (.struct n ts))
    if env.classes.contains n then
      -- every option set, so that the checker infers the type (the value is
      -- never observed)
      return .prim .mkTup (← (env.concreteBelow n).mapM fun d => do
        return .prim .mkSome [.prim .mkTup (← (env.fields d (if d == n then ts else [])).mapM fun (_, t, _) =>
          witness env dictBase dictVars t)])
    return .prim .mkTup (← (env.fields n ts).mapM fun (_, t, _) => witness env dictBase dictVars t)
  -- a type parameter of the enclosing function: its hidden parameter (an
  -- unknown one cannot occur; the checker would reject the program)
  | .param n _ => pure <| match dictVars.idxOf? n with
    | some j => .local (dictBase + j)
    | none => .lit .void

/-- Whether a Verse Core type mentions a type variable. -/
partial def _root_.OpenVerse.VTy.hasVar : VTy → Bool
  | .var _ => true
  | .arr t | .opt t => t.hasVar
  | .tup ts => ts.any VTy.hasVar
  | _ => false

/-- The value of a prototype's field of type `t`: its type's default, or a
    reference to a prototype already allocated (`done`: class, address). -/
partial def protoValue (env : TyEnv) (done : List (String × Nat)) : Ty → Option Value
  | .int | .char32 | .enum _ => some (.int 0)
  | .logic => some (.logic false)
  | .char => some (.char 0)
  | .void | .never => some .void
  | .arr _ | .map _ _ => some (.arr [])
  | .opt _ => some .none
  | .tup ts => (ts.mapM (protoValue env done)).map .tup
  | t@(.struct n ts) =>
    if env.isRefClass n then
      ((env.concreteBelow n).findSome? fun d =>
        if env.coreArgs d [] == env.coreArgs n ts then (done.lookup d).map Value.ref else none)
    else if env.classes.contains n then some (t.toVTy env).default
    else ((env.fields n ts).mapM fun (f : String × Ty × Option SExpr) => protoValue env done f.2.1).map .tup
  | .param .. => none

/-- One prototype per concrete class (#37), in definition order: its class,
    tag and fields. A field of a class type refers to a prototype of a class
    below it, wherever that is (prototypes may form cycles, so classes that
    require each other have them too). -/
def TyEnv.makeProtos (env : TyEnv) : List (String × Nat × List Value) :=
  -- (a parametric class has none: a prototype has fixed type arguments)
  let concrete := env.classes.filter fun d =>
    let i := env.info d
    env.isRefClass d && !i.isIface && !i.isAbstract && (env.sparams.lookup d).isNone
  let addrs := concrete.zipIdx
  concrete.filterMap fun d =>
    ((env.fields d).mapM fun (f : String × Ty × Option SExpr) => protoValue env addrs f.2.1).map
      fun vs => (d, env.tagOf d, vs)

/-- Whether a Verse Core type mentions a reference. -/
partial def _root_.OpenVerse.VTy.hasRef : VTy → Bool
  | .ref _ _ => true
  | .arr t | .opt t => t.hasRef
  | .tup ts => ts.any VTy.hasRef
  | _ => false

/-- The value a slot of type `t` starts with (`DefaultE`), in a function
    whose parameters (hidden ones included) have types `params`: the default
    literal of its Verse Core type (also when only `[]` or the empty option
    mentions a type variable or a reference), the hidden parameter of a type
    parameter, a parameter of a subtype, a placeholder object of the first
    concrete class below a class (#34), or a tuple of such. `visiting` are
    the class types (with their type arguments, #39) whose placeholders are
    being built. -/
partial def slotDefault (env : TyEnv) (dictBase : Nat) (params : List Ty) (visiting : List String)
    (t : Ty) : Except String Expr := do
  let vt := t.toVTy env
  if !vt.hasVar && !vt.hasRef then return .lit vt.default
  -- a parameter of a subtype: no allocation
  if vt.hasRef then
    if let some i := params.findIdx? (fun pt => (pt.toVTy env).sub vt) then return .local i
  match t with
  | .param n _ => match env.dictSlot? dictBase n with
    | some d => return .local d
    | none => return .lit vt.default
  | .tup ts => return .prim .mkTup (← ts.mapM (slotDefault env dictBase params visiting))
  | .struct n ts =>
    -- a prototype of a class below `n` (#37): no allocation
    if env.isRefClass n then
      let addrs := env.protos.zipIdx.filterMap fun (x : (String × Nat × List Value) × Nat) =>
        if (env.concreteBelow n).contains x.1.1 && env.coreArgs x.1.1 [] == env.coreArgs n ts then some x.2
        else none
      if let some a := addrs.head? then return .lit (.ref a)
    if env.isRefClass n then
      -- the first class below `n` whose placeholder needs no instance of a
      -- class whose placeholder is being built
      let mut lastErr := s!"no class at or below {n} can be constructed without an instance of itself, so a variable or temporary of type {n} has no initial value"
      -- (instantiations that grow without end are cut off)
      let key := (Ty.struct n ts).show
      if visiting.length > 16 || key.length > 400 then throw lastErr
      for d in env.concreteBelow n do
        let dkey := s!"{d} as {key}"
        if visiting.contains dkey then continue
        -- (its fields at the slot's type arguments, #39)
        match (env.fieldsSeen n ts d).mapM fun (_, ft, _) =>
            slotDefault env dictBase params (dkey :: visiting) ft with
        | .ok fs => return .heap (.new (env.tagOf d)) fs
        | .error msg => lastErr := msg
      throw lastErr
    -- a parametric class starts with no option set, which has every such type
    if env.classes.contains n then return .lit vt.default
    return .prim .mkTup (← (env.fields n ts).mapM fun (_, t, _) => slotDefault env dictBase params visiting t)
  -- `[]`, the empty option and an empty map have every such type
  | _ => return .lit vt.default

/-- An instance of class `d` (its fields `rep`) as a value of static type
    `T` above it: `rep` in `d`'s option, the others empty. -/
def classWrap (env : TyEnv) (T d : String) (rep : Expr) : Expr :=
  .prim .mkTup ((env.concreteBelow T).map fun e => if e == d then .prim .mkSome [rep] else .lit .none)

/-- The Verse Core type of the fields of class `d`, as a front-end type. -/
def classRepTy (env : TyEnv) (d : String) (args : List Ty := []) : Ty :=
  .tup ((env.fields d args).map (·.2.1))

/-- `a` is a reference class below the class or interface `b`, or an array
    or option of such. -/
partial def refUp (env : TyEnv) : Ty → Ty → Bool
  | .struct S as, .struct T bs =>
    env.isRefClass S && env.isRefClass T && env.isSub S T && env.upArgs S as T == bs
  | .arr a, .arr b | .opt a, .opt b => refUp env a b
  | _, _ => false

/-- Convert a value `e` of type `a` to the supertype `b`, when `a` is a class
    below the class or interface `b`, or an array or option of such (arrays
    and options are covariant): the options of the classes below `a` move to
    their places among those below `b`. -/
partial def convert (env : TyEnv) (e : Expr) (a b : Ty) : EM (Option Expr) := do
  -- references: the same value has both types (Verse Core subtyping, #32)
  if refUp env a b then return some e
  match a, b with
  | .struct S [], .struct T [] =>
    if env.classes.contains S && env.classes.contains T && S != T && env.isSub S T then
      let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a })
      let below := env.concreteBelow S
      let parts := (env.concreteBelow T).map fun d => match below.idxOf? d with
        | some j => Expr.prim (.tupGet j) [.local x]
        | none => .lit .none
      return some (.seq (.assign x e) (.prim .mkTup parts))
    else return none
  | .arr a', .arr b' =>
    let i ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a' })
    match ← convert env (.local i) a' b' with
    | some c => return some (.forE i e (.lit (.logic true)) c)
    | none => return none
  | .opt a', .opt b' =>
    let i ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a' })
    match ← convert env (.local i) a' b' with
    | some c => return some (.ite (.assign i (.prim .query [e])) (.prim .mkSome [c]) (.lit .none))
    | none => return none
  | _, _ => return none

/-- Convert `r` to type `target`: equal types, `false` (bottom) to anything,
    anything to `void` (Book of Verse: "void accepts any value"), and a
    class to a class or interface above it (`convert`). -/
def coerce (p : Pos) (r : R) (target : Ty) : EM Expr := do
  if r.ty == target || r.ty == .never then return r.e
  if target == .void then return .seq r.e (.lit .void)
  match ← convert (← get).env r.e r.ty target with
  | some e =>
    -- a typed temporary: the checker cannot infer the type of an empty option
    let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push target })
    return .assign x e
  | none => eerr p s!"expected {target.show}, found {r.ty.show}"

/-- The type of a two-branch construct: two classes join at their nearest
    common supertype. -/
def join (p : Pos) (a b : Ty) (exp : Option Ty) : EM Ty := do
  match exp with
  | some .void => return .void
  | _ =>
    if a == .never then return b
    if b == .never then return a
    if a == b then return a
    -- void accepts any value (Book of Verse), so a void branch makes the
    -- construct void: `if{X := e} else {Print("none")}` (spec: IfElseMacro)
    if a == .void || b == .void then return .void
    let env := (← get).env
    if let (.struct S as, .struct T bs) := (a, b) then
      if env.classes.contains S && env.classes.contains T then
        -- the expected type, when both are below it, else the nearest
        -- common supertype (at the same type arguments, #39)
        let up (U : String) (us : List Ty) : Bool :=
          env.isSub S U && env.isSub T U && env.upArgs S as U == us && env.upArgs T bs U == us
        if let some (.struct U us) := exp then
          if env.classes.contains U && up U us then return .struct U us
        if let some U := (env.supers S).find? fun U => up U (env.upArgs S as U) then
          return .struct U (env.upArgs S as U)
    eerr p s!"the branches have different types: {a.show} and {b.show}"


/-- `M[k]` on the map in slot `tm` with the key in slot `tk`: the value of the
    first pair whose key equals `k` (fails when there is none). `tp` is a
    slot for the pairs. -/
def mapLookup (tm tk tp : Nat) : Expr :=
  .prim .index [.forE tp (.local tm) (.prim .eq [.prim (.tupGet 0) [.local tp], .local tk])
      (.prim (.tupGet 1) [.local tp]), .lit (.int 0)]

/-- The position of key `k` (slot `tk`) in the map in slot `tm` (fails when absent). -/
def mapFind (tm tk ti : Nat) : Expr :=
  .prim .index [.forE ti (.prim .range [.lit (.int 0), .prim .sub [.prim .len [.local tm], .lit (.int 1)]])
      (.prim .eq [.prim (.tupGet 0) [.prim .index [.local tm, .local ti]], .local tk]) (.local ti),
    .lit (.int 0)]

/-- Insert or update `(k, v)` (slots `tk`, `tv`) in the map in slot `tm`, in
    place when the key exists, at the end otherwise (Book of Verse §9.3). -/
def mapPut (tm tk tv ti tidx : Nat) : Expr :=
  let pair := Expr.prim .mkTup [.local tk, .local tv]
  .ite (.seq (.assign tidx (mapFind tm tk ti)) (.assign tm (.prim .arrSet [.local tm, .local tidx, pair])))
    (.lit .void)
    (.seq (.assign tm (.prim .concat [.local tm, .prim .mkArr [pair]])) (.lit .void))

/-- The position of a field in its struct. -/
def fieldIndex (fs : List (String × Ty × Option SExpr)) (f : String) : Option (Nat × Ty) :=
  ((fs.zip (List.range fs.length)).find? (·.1.1 == f)).map fun ((_, t, _), k) => (k, t)

/-- The UTF-8 encoding of the char32 in slot `tc`, a Unicode scalar value:
    its one to four bytes as chars, each looked up in the table of the 256
    byte values (Verse Core has no conversion from int to char; the lookups
    and the divisions cannot fail, but are guarded so that the checker sees
    no failure). -/
def utf8Of (tc : Nat) : EM Expr := do
  let table : Expr := .lit (.arr ((List.range 256).map Value.char))
  let int (i : Int) : Expr := .lit (.int i)
  let chr (b : Expr) : EM Expr := do
    let tch ← fresh .char
    return .ite (.assign tch (p2 .index table b)) (.local tch) (.prim .userErr [])
  let c := Expr.local tc
  let (a, b, d, e, r, r2) := (← fresh .int, ← fresh .int, ← fresh .int, ← fresh .int, ← fresh .int, ← fresh .int)
  let q (x : Expr) (n : Int) := p2 .quotient x (int n)
  let m (x : Expr) (n : Int) := p2 .modulo x (int n)
  let seqs : List Expr → Expr := fun es => (es.dropLast).foldr .seq (es.getLast?.getD (.lit .void))
  let plus (k : Int) (x : Nat) := p2 .add (int k) (.local x)
  let one := Expr.prim .mkArr [← chr c]
  let two := Expr.prim .mkArr [← chr (plus 192 a), ← chr (plus 128 b)]
  let three := Expr.prim .mkArr [← chr (plus 224 a), ← chr (plus 128 b), ← chr (plus 128 d)]
  let four := Expr.prim .mkArr [← chr (plus 240 a), ← chr (plus 128 b), ← chr (plus 128 d), ← chr (plus 128 e)]
  return .ite (p2 .lt c (int 0x80)) one
    (.ite (seqs [p2 .lt c (int 0x800), .assign a (q c 64), .assign b (m c 64)]) two
    (.ite (seqs [p2 .lt c (int 0x10000), .assign a (q c 4096), .assign r (m c 4096),
        .assign b (q (.local r) 64), .assign d (m (.local r) 64)]) three
    (.ite (seqs [.assign a (q c 262144), .assign r (m c 262144), .assign b (q (.local r) 4096),
        .assign r2 (m (.local r) 4096), .assign d (q (.local r2) 64), .assign e (m (.local r2) 64)]) four
      (.prim .userErr []))))

/-- A Verse Core type that several front-end types have: one with an
    `int` (also a char32 or an enum), a tuple (also a struct), or a type
    variable. -/
partial def _root_.OpenVerse.VTy.shared : VTy → Bool
  | .int | .tup _ | .var _ => true
  | .arr t | .opt t => t.shared
  | _ => false

/-- `ToString` for interpolation. -/
def toStringOf (p : Pos) (r : R) : EM Expr :=
  match r.ty with
  | .char32 => do
    let tc ← fresh .int
    return .seq (.assign tc r.e) (← utf8Of tc)
  | .int | .char => pure (.prim .toStr [r.e])
  | .arr .char => pure r.e
  | t => eerr p s!"no ToString for {t.show} (Verse defines it for int, char, char32 and string)"

mutual
partial def elabE (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  match se with
  | .int p n =>
    if !Int64.inRange n then eerr p s!"integer literal {n} does not fit in 64 bits"
    return ⟨.lit (.int n), .int⟩
  | .char _ c => return ⟨.lit (.char c), .char⟩
  | .char32 _ c => return ⟨.lit (.int c), .char32⟩
  | .str p parts =>
    let pieces ← parts.mapM fun part => match part with
      | .text s => pure (Expr.lit (Value.ofString s))
      | .code e => do toStringOf e.pos (← elabE ctx e none)
    let _ := p
    match pieces with
    | [] => return ⟨.lit (Value.ofString ""), Ty.string⟩
    | e :: es => return ⟨es.foldl (fun a b => p2 .concat a b) e, Ty.string⟩
  | .ident p n =>
    match n with
    | "true" => return ⟨.lit (.logic true), .logic⟩
    | "false" =>
      match exp with
      | some (.opt t) => return ⟨.lit .none, .opt t⟩
      | some (.arr t) => return ⟨.lit (.arr []), .arr t⟩
      | some .void => return ⟨.lit .void, .void⟩
      | _ => return ⟨.lit (.logic false), .logic⟩
    | _ =>
      match ctx.lookup n with
      | some l => return ⟨.local l.slot, l.ty⟩
      | none =>
        -- in a method, a field of `Self`
        if let some c := ctx.selfClass then
          if (ctx.types.fields c).any (·.1 == n) then
            return ← elabE ctx (.member p (.ident p "Self") n) exp
          if ctx.hasMethod c n then
            eerr p s!"'{n}' is a method: call it with {n}(…)"
        match ctx.sig? n with
        | some s =>
          if s.isConst then
            noteFx p s.fx (some s!"uses the constant {n}")
            return ⟨.call s.idx [], s.ret⟩
          else eerr p s!"'{n}' is a function: call it with {n}(…)"
        | none => eerr p s!"unknown identifier '{n}'"
  | .app p f args bracket => elabApp ctx p f args bracket exp
  | .member p (.ident _ n) m =>
    match ctx.lookup n, ctx.types.enums.lookup n with
    | none, some vals =>
      -- `color.Red`: an enumerator
      match vals.idxOf? m with
      | some k => return ⟨.lit (.int k), .enum n⟩
      | none => eerr p s!"enum {n} has no value '{m}'"
    | _, _ => elabMember ctx p (← elabE ctx (.ident p n) none) m
  | .member p e m => elabMember ctx p (← elabE ctx e none) m
  | .construct p name targs args => elabConstruct ctx p name targs args exp
  | .mapLit p entries => elabMapLit ctx p entries exp
  | .structDef p _ _ | .enumDef p _ => eerr p "struct and enum definitions must be at the top level"
  | .query p e =>
    let r ← elabE ctx e none
    match r.ty with
    | .opt t => return ⟨.prim .query [r.e], t⟩
    | .logic => return ⟨.prim .query [r.e], .logic⟩
    | t => eerr p s!"'?' needs an option or logic, found {t.show}"
  | .neg p e =>
    let r ← elabE ctx e (some .int)
    if r.ty != .int then eerr p s!"unary '-' needs an int, found {r.ty.show}"
    return ⟨.prim .neg [r.e], .int⟩
  | .notE _ e =>
    let r ← elabE { ctx with canFail := true } e none
    return ⟨Expr.notE r.e, .void⟩
  | .bin p "/" _ _ =>
    eerr p "integer '/' gives a rational; write Floor(X / Y), Ceil(X / Y) or Quotient[X, Y]"
  | .bin p op a b =>
    let ra ← elabE ctx a none
    let rb ← elabE ctx b (some ra.ty)
    match op, ra.ty, rb.ty with
    | "+", .int, .int => return ⟨p2 .add ra.e rb.e, .int⟩
    | "-", .int, .int => return ⟨p2 .sub ra.e rb.e, .int⟩
    | "*", .int, .int => return ⟨p2 .mul ra.e rb.e, .int⟩
    | "+", .arr t, .arr u =>
      if t == u then return ⟨p2 .concat ra.e rb.e, .arr t⟩
      else eerr p s!"cannot concatenate {ra.ty.show} and {rb.ty.show}"
    | _, ta, tb => eerr p s!"no operator '{op}' for {ta.show} and {tb.show}"
  | .cmp p a rest => elabCmp ctx p a rest
  | .andE _ a b =>
    -- each operand is its own scope: names defined in `a` are not visible in
    -- `b`, and names from either side do not escape the `and`
    let (ra, _) ← elabStmt ctx a none
    let (rb, _) ← elabStmt ctx b exp
    return ⟨Expr.andE ra.e rb.e, rb.ty⟩
  | .orE p a b =>
    let ra ← elabE { ctx with canFail := true } a exp
    let rb ← elabE ctx b (exp.getD ra.ty)
    let ty ← join p ra.ty rb.ty exp
    let t ← fresh ty
    return ⟨Expr.orE t (← coerce p ra ty) (← coerce p rb ty), ty⟩
  | .range p _ _ => eerr p "a range a..b can only be the source of a for clause"
  | .tuple _ [] => return ⟨.lit .void, .void⟩
  | .tuple _ es =>
    let exps : List (Option Ty) := match exp with
      | some (.tup ts) => if ts.length == es.length then ts.map some else es.map fun _ => none
      | _ => es.map fun _ => none
    let rs ← (es.zip exps).mapM fun (e, t) => elabE ctx e t
    return ⟨.prim .mkTup (rs.map (·.e)), .tup (rs.map (·.ty))⟩
  | .block _ ss =>
    let (r, _) ← elabSeq ctx ss exp
    return r
  | .arrayLit p es =>
    let elemExp : Option Ty := match exp with
      | some (.arr t) => some t
      | _ => none
    match es with
    | [] => match elemExp with
      | some t => return ⟨.lit (.arr []), .arr t⟩
      | none => eerr p "the type of an empty array{} must be given (e.g. X:[]int = array{})"
    | e :: rest =>
      let r ← elabE ctx e elemExp
      let t := elemExp.getD r.ty
      let first ← coerce e.pos r t
      let others ← rest.mapM fun e' => do coerce e'.pos (← elabE ctx e' (some t)) t
      return ⟨.prim .mkArr (first :: others), .arr t⟩
  | .optionLit _ e =>
    let inner : Option Ty := match exp with
      | some (.opt t) => some t
      | _ => none
    let r ← elabE { ctx with canFail := true } e inner
    -- an expression that cannot fail needs no failure context (and no
    -- saved state to roll back to: the interpreter's heap is not copied)
    if !(r.e.mayFail ctx.sigProg) then return ⟨.prim .mkSome [r.e], .opt r.ty⟩
    let t ← fresh r.ty
    return ⟨Expr.optionE t r.e, .opt r.ty⟩
  | .logicLit p e =>
    let r ← elabE { ctx with canFail := true } e none
    if !(r.e.mayFail ctx.sigProg) then eerr p "logic{…} needs an expression that can fail"
    return ⟨Expr.logicE r.e, .logic⟩
  | .ite p conds thenE elseE =>
    let (rc, ctxT) ← elabSeq { ctx with canFail := true } conds none
    if !(rc.e.mayFail ctx.sigProg) then
      eerr p "the condition of this if cannot fail (Verse requires a failable condition)"
    let thenCtx := { ctxT with canFail := ctx.canFail }
    match elseE with
    | none =>
      let rt ← elabE thenCtx thenE (some .void)
      return ⟨.ite rc.e (← coerce p rt .void) (.lit .void), .void⟩
    | some ee =>
      let rt ← elabE thenCtx thenE exp
      let re ← elabE ctx ee (exp.getD rt.ty)
      let ty ← join p rt.ty re.ty exp
      return ⟨.ite rc.e (← coerce p rt ty) (← coerce p re ty), ty⟩
  | .forE p clauses body => elabFor ctx p clauses body
  | .gen p _ _ _ => eerr p "a generator X : source can only appear in a for clause"
  | .loop _ body =>
    let r ← elabE { ctx with inLoop := true } body none
    return ⟨.loop r.e, .void⟩
  | .brk p =>
    if !ctx.inLoop then eerr p "break is only allowed inside loop (not for)"
    return ⟨.brk, .never⟩
  | .ret p none =>
    if ctx.inBlock then eerr p "return is not allowed in a block: clause (it would skip the clauses after it)"
    if ctx.retTy != .void then eerr p s!"return needs a value of type {ctx.retTy.show}"
    return ⟨.ret (.lit .void), .never⟩
  | .ret p (some e) =>
    if ctx.inBlock then eerr p "return is not allowed in a block: clause (it would skip the clauses after it)"
    let r ← elabE ctx e (some ctx.retTy)
    return ⟨.ret (← coerce p r ctx.retTy), .never⟩
  | .caseE p scrut arms => elabCase ctx p scrut arms exp
  | .decl p _ _ _ _ =>
    let (r, _) ← elabStmt ctx se exp
    let _ := p
    return r
  | .set p lhs op rhs => elabSet ctx p lhs op rhs

/-- A statement: like `elabE`, but a declaration extends the scope. Also
    enforces the failure discipline. -/
partial def elabStmt (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM (R × Ctx) := do
  let (r, ctx') ← match se with
    | .decl p n sty isVar rhs => do
      if ctx.lookup n |>.isSome then
        eerr p s!"'{n}' is already defined; Verse does not allow shadowing (use set {n} = … for a var)"
      if (ctx.sig? n).isSome || builtins.contains n then
        eerr p s!"'{n}' is already the name of a function or constant"
      if let some c := ctx.selfClass then
        if (ctx.types.fields c).any (·.1 == n) || ctx.hasMethod c n then
          eerr p s!"'{n}' is already a field or method of {c}; Verse does not allow shadowing"
      let ty? ← sty.mapM (resolveTy ctx.types p)
      let r ← elabE ctx rhs ty?
      let ty := ty?.getD r.ty
      if ty == .never then eerr p s!"cannot infer the type of '{n}'"
      let e ← coerce p r ty
      let slot ← fresh ty
      pure (⟨.assign slot e, ty⟩,
        { ctx with locals := { name := n, slot, ty, mutable := isVar } :: ctx.locals })
    | _ => do pure (← elabE ctx se exp, ctx)
  if !ctx.canFail && (r.e.mayFail ctx.sigProg) then
    eerr se.pos ("this expression can fail, but it is not in a failure context (an if " ++
      "condition, a for clause, option{…}, logic{…}, not, the left of or, or a <decides> function)")
  return (r, ctx')

/-- A sequence of statements, threading the scope; the value is the last one's. -/
partial def elabSeq (ctx : Ctx) (ss : List SExpr) (exp : Option Ty) : EM (R × Ctx) := do
  match ss with
  | [] => return (⟨.lit .void, .void⟩, ctx)
  | [s] => elabStmt ctx s exp
  | s :: rest =>
    let (r, ctx') ← elabStmt ctx s none
    let (r2, ctx'') ← elabSeq ctx' rest exp
    return (⟨.seq r.e r2.e, r2.ty⟩, ctx'')

partial def elabArgs (ctx : Ctx) (p : Pos) (args : List SExpr) (tys : List Ty) : EM (List Expr) := do
  if args.length != tys.length then
    eerr p s!"expected {tys.length} argument(s), found {args.length}"
  (args.zip tys).mapM fun (a, t) => do coerce a.pos (← elabE ctx a (some t)) t

partial def elabInts (ctx : Ctx) (p : Pos) (args : List SExpr) : EM (List Expr) :=
  elabArgs ctx p args (args.map fun _ => .int)

partial def elabApp (ctx : Ctx) (p : Pos) (f : SExpr) (args : List SExpr) (bracket : Bool)
    (exp : Option Ty) : EM R := do
  let needBracket (name : String) : EM Unit := do
    if !bracket then eerr p s!"{name} can fail: call it with {name}[…]"
  match f with
  | .ident _ name =>
    match ctx.lookup name with
    | some l => elabIndexLike ctx p ⟨.local l.slot, l.ty⟩ args bracket
    | none =>
    -- in a method, a method of `Self`, or a field of `Self` indexed
    let selfMember? : Bool := match ctx.selfClass with
      | some c => ctx.hasMethod c name ||
          ((ctx.types.fields c).any (·.1 == name) && !builtins.contains name)
      | none => false
    if selfMember? then elabApp ctx p (.member p (.ident p "Self") name) args bracket exp else
    -- `T[X]`, `T(X)`: a cast to class or interface `T`
    if ctx.types.classes.contains name && (ctx.sig? name).isNone then elabCast ctx p name args bracket else
    match name with
    | "Print" =>
      let es ← elabArgs ctx p args [Ty.string]
      return ⟨.print es.head!, .void⟩
    | "ToString" =>
      match args with
      | [a] => return ⟨← toStringOf p (← elabE ctx a none), Ty.string⟩
      | _ => eerr p "ToString takes one argument"
    | "Abs" => return ⟨.prim .abs (← elabInts ctx p args), .int⟩
    | "Floor" | "Ceil" =>
      match args with
      | [.bin _ "/" a b] =>
        let es ← elabInts ctx p [a, b]
        return ⟨.prim (if name == "Floor" then .floorDiv else .ceilDiv) es, .int⟩
      | _ => eerr p s!"openverse v1 supports {name}(X / Y) on ints only"
    | "Quotient" => needBracket name; return ⟨.prim .quotient (← elabInts ctx p args), .int⟩
    | "Mod" => needBracket name; return ⟨.prim .modulo (← elabInts ctx p args), .int⟩
    | "Min" | "Max" =>
      let es ← elabInts ctx p args
      let ta ← fresh .int
      let tb ← fresh .int
      let op := if name == "Min" then Prim.le else Prim.ge
      return ⟨.seq (.assign ta es[0]!) (.seq (.assign tb es[1]!)
        (.ite (p2 op (.local ta) (.local tb)) (.local ta) (.local tb))), .int⟩
    | "Err" => return ⟨.prim .userErr [], .never⟩
    | "$Show" =>
      -- the entry of `openverse run FILE do EXPR`: print the value when it
      -- has a ToString, else just evaluate it
      match args with
      | [a] =>
        let r ← elabE ctx a none
        match r.ty with
        | .int | .char | .arr .char => return ⟨.print (← toStringOf p r), .void⟩
        | _ => return ⟨.seq r.e (.lit .void), .void⟩
      | _ => eerr p "internal: $Show"
    | _ =>
      match ctx.sig? name with
      | some s =>
        -- a call has its callee's effects
        noteFx p s.fx (some (if s.isConst then s!"uses the constant {name}" else s!"calls {name}"))
        if s.isConst then
          elabIndexLike ctx p ⟨.call s.idx [], s.ret⟩ args bracket
        else
          if s.decides && !bracket then eerr p s!"{name} is <decides>: call it with {name}[…]"
          -- the call syntax marks failure (Book of Verse §8.1)
          if !s.decides && bracket then eerr p s!"{name} cannot fail: call it with {name}(…)"
          if !s.tparams.isEmpty then return ← elabGenericCall ctx p s args exp
          let isNamed : SExpr → Bool
            | .decl _ n _ _ _ => n.startsWith "?"
            | _ => false
          if s.named.isEmpty && !args.any isNamed then
            let es ← elabArgs ctx p args s.params
            return ⟨.call s.idx es, s.ret⟩
          -- named arguments: evaluate positional arguments left to right, then named ones as
          -- written, then the defaults of those omitted (Book of Verse §2.5), into temporaries
          let npos := s.params.length - s.named.length
          let pos := args.filter (!isNamed ·)
          let named := args.filterMap fun a => match a with
            | .decl ap n _ _ rhs => if n.startsWith "?" then some (ap, (n.drop 1).toString, rhs) else none
            | _ => none
          if pos.length != npos then
            -- a method's receiver is its first positional argument
            let (shown, off) := match name.splitOn "." with
              | [_, m] => (m, 1)
              | _ => (name, 0)
            eerr p s!"{shown} takes {npos - off} positional argument(s), found {pos.length - off}"
          for (ap, n, _) in named do
            if (s.named.find? (·.1 == n)).isNone then eerr ap s!"{name} has no parameter ?{n}"
          let ptys := s.params.toArray
          let mut steps : Array Expr := #[]
          let mut slots : Array (Option Nat) := Array.replicate s.params.length none
          for (a, k) in pos.zip (List.range npos) do
            let t := ptys[k]!
            let ta ← fresh t
            steps := steps.push (.assign ta (← coerce a.pos (← elabE ctx a (some t)) t))
            slots := slots.set! k (some ta)
          for (ap, n, rhs) in named do
            let k := npos + (s.named.findIdx? (·.1 == n)).get!
            let t := ptys[k]!
            let ta ← fresh t
            steps := steps.push (.assign ta (← coerce ap (← elabE ctx rhs (some t)) t))
            slots := slots.set! k (some ta)
          for ((n, dflt), j) in s.named.zip (List.range s.named.length) do
            let k := npos + j
            if slots[k]!.isNone then
              let some d := dflt | eerr p s!"{name} needs the argument ?{n}, which has no default"
              let t := ptys[k]!
              let ta ← fresh t
              steps := steps.push (.assign ta (← fxAt p (do coerce p (← elabE { ctx with locals := [], selfClass := none } d (some t)) t)))
              slots := slots.set! k (some ta)
          let call := Expr.call s.idx (slots.toList.map fun o => Expr.local o.get!)
          return ⟨steps.toList.foldr Expr.seq call, s.ret⟩
      | none => eerr p s!"unknown function '{name}'"
  | .member mp (.ident _ "(super:)") m =>
    -- `(super:)M(…)`: the implementation the current method's class inherits
    let some c := ctx.selfClass | eerr p "(super:) can only be used in a method"
    let some impl := ctx.mostSpecific? ((ctx.types.supers c).drop 1) m
      | eerr p s!"nothing above {c} implements '{m}'"
    elabApp ctx p (.ident mp s!"{impl}.{m}") (.ident mp "Self" :: args) bracket exp
  | .member mp obj m =>
    let r ← elabE ctx obj none
    match r.ty with
    | .struct c targs =>
      let env := ctx.types
      if let (true, some owner) := (env.classes.contains c, ctx.methodDecl? c m) then
        let ms := (ctx.sig? s!"{owner}.{m}").get!
        if ms.decides && !bracket then eerr p s!"{m} is <decides>: call it with {m}[…]"
        if !ms.decides && bracket then eerr p s!"{m} cannot fail: call it with {m}(…)"
        if ms.named.isEmpty && args.length + 1 != ms.params.length then
          eerr p s!"{m} takes {ms.params.length - 1} argument(s), found {args.length}"
        let slot ← fresh r.ty
        let recv := s!"$recv{slot}"
        let ds := env.concreteBelow c
        -- one implementation for every class below the receiver's type, above
        -- that type: a direct call (the receiver evaluated first, as `Self`)
        let direct : Option String := match (ds.map (ctx.implOf? · m)).eraseDups with
          | [some e] => if env.isSub c e then some e else none
          | _ => none
        -- the receiver as an instance of class `e`, above or below `c` (#39)
        let argsAt (e : String) : List Ty :=
          if env.isSub c e then env.upArgs c targs e else env.argsBelow c targs e
        if let some e := direct then
          let ctx' := { ctx with locals := { name := recv, slot, ty := .struct e (argsAt e), mutable := false } :: ctx.locals }
          let rc ← elabApp ctx' p (.ident mp s!"{e}.{m}") (.ident mp recv :: args) bracket exp
          return ⟨.seq (.assign slot r.e) rc.e, rc.ty⟩
        -- otherwise dispatch on the class of the receiver's value: the
        -- receiver, then the arguments, once each, then the implementation of
        -- the class whose option is set
        let ownerTps := ((env.sparams.lookup owner).getD []).map (·.1)
        if ms.tparams.length > ownerTps.length then
          eerr p s!"{m} has type parameters, so it cannot be dispatched on the class of the receiver (#18)"
        -- the declaration's types at the receiver's type arguments
        let σ := ownerTps.zip (argsAt owner)
        let msRet := ms.ret.subst σ
        if args.any (fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false) then
          eerr p s!"named arguments to a method dispatched on the class of the receiver are not supported (#18)"
        let mut pre : Array Expr := #[.assign slot r.e]
        let mut locs : List Local := [{ name := recv, slot, ty := r.ty, mutable := false }]
        let mut argIds : Array SExpr := #[]
        for (a, t0) in args.zip (ms.params.drop 1) do
          let t := t0.subst σ
          let ta ← fresh t
          pre := pre.push (.assign ta (← coerce a.pos (← elabE ctx a (some t)) t))
          locs := { name := s!"$arg{ta}", slot := ta, ty := t, mutable := false } :: locs
          argIds := argIds.push (.ident mp s!"$arg{ta}")
        let mut acc : Expr := .prim .userErr []   -- no option set: unreachable
        if env.isRefClass c then
          -- a reference: one test of the object's class per implementation (#34)
          let mut groups : Array (String × Array String) := #[]
          for d in ds do
            let some e := ctx.implOf? d m | eerr p s!"class {d} does not implement '{m}'"
            match groups.findIdx? (·.1 == e) with
            | some gi => groups := groups.modify gi fun (e', cls) => (e', cls.push d)
            | none => groups := groups.push (e, #[d])
          for (e, cls) in groups.toList.reverse do
            let sd ← fresh (.struct e (argsAt e))
            let ctx' := { ctx with locals := { name := s!"$self{sd}", slot := sd, ty := .struct e (argsAt e), mutable := false } :: (locs ++ ctx.locals) }
            let rc ← elabApp ctx' p (.ident mp s!"{e}.{m}") (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
            acc := .ite (.assign sd (.heap (.isTag (cls.toList.map env.tagOf)) [.local slot]))
              (← coerce p rc msRet) acc
          return ⟨pre.toList.foldr Expr.seq acc, msRet⟩
        for (d, j) in (ds.zip (List.range ds.length)).reverse do
          let some e := ctx.implOf? d m | eerr p s!"class {d} does not implement '{m}'"
          let td ← fresh (classRepTy env d)
          let sd ← fresh (.struct d [])
          let ctx' := { ctx with locals := { name := s!"$self{sd}", slot := sd, ty := .struct d [], mutable := false } :: (locs ++ ctx.locals) }
          let rc ← elabApp ctx' p (.ident mp s!"{e}.{m}") (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
          acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local slot]]))
            (.seq (.assign sd (classWrap env d d (.local td))) (← coerce p rc ms.ret)) acc
        let y ← fresh ms.ret
        return ⟨pre.toList.foldr Expr.seq (.assign y acc), ms.ret⟩
      else if (ctx.types.fields c targs).any (·.1 == m) then
        -- `S.F[i]`, `S.F(k)`: a field, indexed
        elabIndexLike ctx p (← elabMember ctx p r m) args bracket
      else if ctx.types.classes.contains c then eerr p s!"class {c} has no method '{m}'"
      else eerr p s!"struct {c} has no field '{m}' (structs have no methods)"
    | _ => elabMethod ctx p r m args bracket
  | _ => elabIndexLike ctx p (← elabE ctx f none) args bracket

/-- `T[X]`: `X` as a value of class or interface `T`, failing unless its class
    is below `T`; `T(X)`: an upcast, which cannot fail (Book of Verse ch. 10). -/
partial def elabCast (ctx : Ctx) (p : Pos) (T : String) (args : List SExpr) (bracket : Bool) : EM R := do
  let env := ctx.types
  let [a] := args | eerr p s!"a cast {T}[X] takes one value"
  let r ← elabE ctx a none
  let (S, sargs) ← match r.ty with
    | .struct S sargs => if env.classes.contains S then pure (S, sargs) else eerr p s!"cannot cast a {S} to {T}"
    | t => eerr p s!"cannot cast a {t.show} to {T}"
  -- a parametric class's type arguments are those of the value (#39), in the
  -- same hierarchy
  let parametric := (env.sparams.lookup T).isSome || !(env.coreArgs T []).isEmpty
  if parametric && env.rootOf S != env.rootOf T then
    eerr p s!"cannot cast a {S} to {T}: {T}'s type arguments would be unknown (they are not {S}'s)"
  let targs := if env.isSub S T then env.upArgs S sargs T else env.argsBelow S sargs T
  if parametric && (env.coreArgs T targs).length > (env.coreArgs S sargs).length then
    eerr p s!"cannot cast a {r.ty.show} to {T}: {T} has type parameters that {S} does not have, which would be unknown"
  let tty : Ty := .struct T targs
  if !bracket then
    if !env.isSub S T then
      eerr p s!"{T}(…) converts to a supertype, and {S} is not below {T}: use {T}[…] to cast down"
    return ⟨← coerce p r tty, tty⟩
  let below := env.concreteBelow S
  let common := below.filter (env.isSub · T)
  if common.isEmpty then
    eerr p s!"no class is below both {r.ty.show} and {T}, so {T}[…] would always fail"
  if parametric && env.coreArgs T targs != env.coreArgs S sargs then
    eerr p s!"a {r.ty.show} is never a {T}: their type arguments differ, so {T}[…] would always fail"
  -- a reference: a test of its object's class (#34)
  if env.isRefClass S then return ⟨.heap (.isTag (common.map env.tagOf)) [r.e], tty⟩
  let x ← fresh r.ty
  let mut acc : Expr := .prim .fail []
  for d in common.reverse do
    let j := (below.idxOf? d).getD 0
    let td ← fresh (classRepTy env d)
    acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local x]])) (classWrap env T d (.local td)) acc
  let y ← fresh (.struct T [])
  return ⟨.seq (.assign x r.e) (.assign y acc), .struct T []⟩

/-- A call of a generic function. Its type arguments are inferred by matching
    its signature: the result type against the expected type (unless that is
    `void`, which accepts anything), then each parameter type against its
    argument's, left to right. An argument whose parameter type is already
    determined is elaborated against it, so `array{}` and `false` work. -/
partial def elabGenericCall (ctx : Ctx) (p : Pos) (s : Sig) (args : List SExpr) (exp : Option Ty) :
    EM R := do
  if args.any fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false then
    eerr p s!"{s.name} is generic: openverse does not support named arguments to generic functions"
  if args.length != s.params.length then
    eerr p s!"{s.name} takes {s.params.length} argument(s), found {args.length}"
  let mut σ : List (String × Ty) := []
  if let some et := exp then
    if !(et == .void) then
      if let some σ' := s.ret.matchArg ctx.types σ et then σ := σ'
  let bound (σ : List (String × Ty)) (t : Ty) := t.params.all fun v => (σ.lookup v).isSome
  -- `false`, `array{}` and `map{}` take their type from context, so they are
  -- elaborated after the other arguments (they are still evaluated in order)
  let fromContext : SExpr → Bool
    | .ident _ "false" | .arrayLit _ [] | .mapLit _ [] => true
    | _ => false
  let mut es : Array Expr := Array.replicate args.length (.lit .void)
  -- arguments left for the second pass; an argument whose type contains
  -- `false` (like `array{Err()}`) binds nothing, so it joins them
  let mut deferred : Array Bool := (args.map fromContext).toArray
  for pass in [0, 1] do
    for ((a, pt), i) in (args.zip s.params).zip (List.range args.length) do
      if (pass == 0) == deferred[i]! then continue
      if bound σ pt then
        let t := pt.subst σ
        let r ← elabE ctx a (some t)
        let e ← tryCatch (coerce a.pos r t) fun msg => throw s!"{msg} (in a call of {s.name})"
        es := es.set! i e
      else
        if fromContext a then
          let v := (pt.params.filter fun v => (σ.lookup v).isNone).headD "t"
          eerr a.pos s!"cannot infer type parameter {v} of {s.name} from the arguments of this call"
        let r ← elabE ctx a none
        match pt.matchArg ctx.types σ r.ty with
        | some σ' =>
          σ := σ'
          if pass == 0 && !bound σ pt then
            deferred := deferred.set! i true
          else
            es := es.set! i (← coerce a.pos r (pt.subst σ))
        | none => eerr a.pos s!"expected {(pt.subst σ).show}, found {r.ty.show} (in a call of {s.name})"
  let mut targs : Array Ty := #[]
  for (v, cmp) in s.tparams do
    let some t := σ.lookup v
      | eerr p s!"cannot infer type parameter {v} of {s.name} from the arguments of this call"
    if cmp && !t.comparable ctx.types then eerr p (notComparable ctx.types t s!"type parameter {v} of {s.name}")
    targs := targs.push t
  -- the hidden arguments: a value of each type argument
  let dicts ← targs.toList.mapM (witness ctx.types ctx.dictBase ctx.dictVars)
  return ⟨.call s.idx (es.toList ++ dicts), s.ret.subst σ⟩

/-- The failable array methods of the Book of Verse (§9.1):
    `A.Slice[i, j]`, `A.Slice[i]`, `A.Find[x]`, `A.RemoveElement[i]`,
    `A.ReplaceElement[i, x]`, `A.Insert[i, B]`. Each fails when an index is
    out of range (or, for `Find`, when there is no such element). -/
partial def elabMethod (ctx : Ctx) (p : Pos) (r : R) (m : String) (args : List SExpr) (bracket : Bool) :
    EM R := do
  let .arr t := r.ty | eerr p s!"{r.ty.show} has no method '{m}'"
  if !bracket then eerr p s!"{m} can fail: call it with A.{m}[…]"
  let ta ← fresh r.ty
  let len := Expr.prim .len [.local ta]
  let int (i : Int) : Expr := .lit (.int i)
  -- the elements of A at indices lo, …, hi - 1 (lo ≤ hi known)
  let slice (lo hi : Expr) : EM Expr := do
    let ti ← fresh .int
    let tx ← fresh t
    return .forE ti (.prim .range [lo, p2 .sub hi (int 1)]) (.assign tx (p2 .index (.local ta) (.local ti)))
      (.local tx)
  let start := Expr.assign ta r.e
  match m, args with
  | "Slice", [a, b] =>
    let es ← elabInts ctx p [a, b]
    let tlo ← fresh .int
    let thi ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (.seq (p2 .le (.local tlo) (.local thi))
      (p2 .le (.local thi) len))
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq (.assign thi es[1]!) (.seq chk
      (← slice (.local tlo) (.local thi))))), r.ty⟩
  | "Slice", [a] =>
    let es ← elabInts ctx p [a]
    let tlo ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (p2 .le (.local tlo) len)
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq chk (← slice (.local tlo) len))), r.ty⟩
  | "Find", [x] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t "the element type of Find")
    let rx ← elabE ctx x (some t)
    let tx ← fresh t
    let ti ← fresh .int
    let found := Expr.forE ti (.prim .range [int 0, p2 .sub len (int 1)])
      (p2 .eq (p2 .index (.local ta) (.local ti)) (.local tx)) (.local ti)
    return ⟨.seq start (.seq (.assign tx (← coerce p rx t)) (p2 .index found (int 0))), .int⟩
  | "RemoveElement", [i] =>
    let es ← elabInts ctx p [i]
    let tk ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tk)) (p2 .lt (.local tk) len)
    return ⟨.seq start (.seq (.assign tk es[0]!) (.seq chk
      (p2 .concat (← slice (int 0) (.local tk)) (← slice (p2 .add (.local tk) (int 1)) len)))), r.ty⟩
  | "ReplaceElement", [i, x] =>
    let es ← elabInts ctx p [i]
    let rx ← elabE ctx x (some t)
    return ⟨.seq start (.prim .arrSet [.local ta, es[0]!, ← coerce p rx t]), r.ty⟩
  | "Insert", [i, b] =>
    let es ← elabInts ctx p [i]
    let rb ← elabE ctx b (some r.ty)
    let tk ← fresh .int
    let tb ← fresh r.ty
    let chk := Expr.seq (p2 .le (int 0) (.local tk)) (p2 .le (.local tk) len)
    return ⟨.seq start (.seq (.assign tk es[0]!) (.seq (.assign tb (← coerce p rb r.ty)) (.seq chk
      (p2 .concat (p2 .concat (← slice (int 0) (.local tk)) (.local tb)) (← slice (.local tk) len))))), r.ty⟩
  | _, _ => eerr p s!"unknown array method '{m}' with {args.length} argument(s) (openverse supports Slice, Find, RemoveElement, ReplaceElement, Insert)"

/-- `A[i]` on an array (failable) or `T(k)` on a tuple. -/
partial def elabIndexLike (ctx : Ctx) (p : Pos) (r : R) (args : List SExpr) (bracket : Bool) : EM R := do
  match r.ty, args, bracket with
  | .arr t, [i], true =>
    let ri ← elabE ctx i (some .int)
    if ri.ty != .int then eerr p s!"an array index must be an int, found {ri.ty.show}"
    return ⟨p2 .index r.e ri.e, t⟩
  | .map kt vt, [k], true =>
    let tm ← fresh r.ty
    let rk ← elabE ctx k (some kt)
    let tk ← fresh kt
    let tp ← fresh (.tup [kt, vt])
    return ⟨.seq (.assign tm r.e) (.seq (.assign tk (← coerce p rk kt)) (mapLookup tm tk tp)), vt⟩
  | .tup ts, [.int _ k], false =>
    if k < 0 || k.toNat ≥ ts.length then eerr p s!"tuple index {k} out of range"
    return ⟨.prim (.tupGet k.toNat) [r.e], ts[k.toNat]!⟩
  | t, _, _ => eerr p s!"cannot call or index a value of type {t.show}"

partial def elabCmp (ctx : Ctx) (p : Pos) (a : SExpr) (rest : List (String × SExpr)) : EM R := do
  let opOf : String → Prim
    | "=" => .eq | "<>" => .ne | "<" => .lt | "<=" => .le | ">" => .gt | _ => .ge
  let checkTys (op : String) (ta tb : Ty) : EM Unit := do
    if op == "=" || op == "<>" then
      if !isComparable ctx.types ta || !isComparable ctx.types tb then
        if !ta.comparable ctx.types then eerr p (notComparable ctx.types ta s!"an operand of '{op}'")
        if !tb.comparable ctx.types then eerr p (notComparable ctx.types tb s!"an operand of '{op}'")
        eerr p "these values cannot be compared"
      -- different types with the same Verse Core type (a char32 or an enum
      -- and an int, two structs with the same fields, also inside
      -- containers) would compare equal there
      -- (or could be, at some instance of the type parameters they mention:
      -- two different ones, or one and a type that several types share in
      -- Core, one with an int or a tuple)
      let (va, vb) := (ta.toVTy ctx.types, tb.toVTy ctx.types)
      let (pa, pb) := (!ta.params.isEmpty, !tb.params.isEmpty)
      if !(ta == tb) && ta != .never && tb != .never &&
          (va == vb || (pa && pb) || (pa && vb.shared) || (pb && va.shared)) then
        eerr p s!"'{op}' compares values of different types, {ta.show} and {tb.show}"
    else if !((ta == .int && tb == .int) || (ta == .char && tb == .char) || (ta == .char32 && tb == .char32)) then
      eerr p s!"'{op}' compares ints, chars or char32s, found {ta.show} and {tb.show}"
  let ra ← elabE ctx a none
  match rest with
  | [(op, b)] =>
    let rb ← elabE ctx b (some ra.ty)
    checkTys op ra.ty rb.ty
    return ⟨p2 (opOf op) ra.e rb.e, ra.ty⟩
  | _ =>
    -- a chain: each operand is evaluated once, every adjacent pair is checked,
    -- and the result is the leftmost operand (Book of Verse §5.4)
    let t0 ← fresh ra.ty
    let mut prev := t0
    let mut prevTy := ra.ty
    let mut steps : Array Expr := #[.assign t0 ra.e]
    for (op, b) in rest do
      let rb ← elabE ctx b (some prevTy)
      checkTys op prevTy rb.ty
      let tb ← fresh rb.ty
      steps := steps.push (.assign tb rb.e)
      steps := steps.push (p2 (opOf op) (.local prev) (.local tb))
      prev := tb
      prevTy := rb.ty
    return ⟨steps.foldr Expr.seq (.local t0), ra.ty⟩

partial def elabSet (ctx : Ctx) (p : Pos) (lhs0 : SExpr) (op : Option String) (rhs : SExpr) : EM R := do
  -- in a method, a path from a field of `Self` (as when one is read)
  let rec selfRoot : SExpr → SExpr
    | .ident ip n =>
      match ctx.lookup n, ctx.selfClass with
      | none, some c => if (ctx.types.fields c).any (·.1 == n) then .member ip (.ident ip "Self") n else .ident ip n
      | _, _ => .ident ip n
    | .member sp e f => .member sp (selfRoot e) f
    | .app sp e [k] true => .app sp (selfRoot e) [k] true
    | .query sp e => .query sp (selfRoot e)
    | e => e
  let lhs := selfRoot lhs0
  let combine (old : Expr) (ty : Ty) (o : String) (new : R) : EM Expr :=
    match o, ty, new.ty with
    | "+", .int, .int => pure (p2 .add old new.e)
    | "-", .int, .int => pure (p2 .sub old new.e)
    | "*", .int, .int => pure (p2 .mul old new.e)
    | "+", .arr t, .arr u => if t == u then pure (p2 .concat old new.e)
        else eerr p s!"cannot concatenate {ty.show} and {new.ty.show}"
    | "/", .int, _ => eerr p "set /= is not defined on int (integer division can fail)"
    | _, _, _ => eerr p s!"no operator '{o}=' for {ty.show} and {new.ty.show}"
  let mutableLocal (n : String) : EM Local := do
    match ctx.lookup n with
    | some l => if l.mutable then pure l else eerr p s!"'{n}' is not a var; declare it with var {n}:t = …"
    | none => eerr p s!"unknown variable '{n}'"
  -- a path `X.F[i]…`: the root variable and its steps (`some f` a field,
  -- `none` with an expression an index or key)
  let rec path : SExpr → Option (String × List (Pos × Option String × Option SExpr))
    | .ident _ n => some (n, [])
    | .member sp e f => (path e).map fun (n, ss) => (n, ss ++ [(sp, some f, none)])
    | .app sp e [k] true => (path e).map fun (n, ss) => (n, ss ++ [(sp, none, some k)])
    -- `X?`: the value inside an option (spec: DeoptionSet); fails when empty
    | .query sp e => (path e).map fun (n, ss) => (n, ss ++ [(sp, some "?", none)])
    | _ => none
  let general : List (Pos × Option String × Option SExpr) → Bool
    | steps@(_ :: _ :: _) => !steps.isEmpty
    | steps => steps.any (·.2.1 == some "?")
  if let some (root, steps) := path lhs then if general steps then
    -- `set X.p = e` with a path of two or more steps (Book of Verse §3.5, §9.3):
    -- the indices and keys are evaluated once, left to right; then each
    -- intermediate container is read (an index or an intermediate key that
    -- is missing makes the set fail); then the new leaf; then the
    -- containers are rebuilt from the leaf up, ending with the variable
    -- the variable must be a var unless the path writes an object (below)
    let l ← match ctx.lookup root with
      | some l => pure l
      | none => eerr p s!"unknown variable '{root}'"
    let mut pre : Array Expr := #[]
    -- per step: the container's slot and type, and the step
    let mut levels : Array (Nat × Ty × Pos × Option String × Option (Nat × Ty)) := #[]
    let mut cur := l.slot
    let mut ty := l.ty
    -- first the indices and keys
    let mut keys : Array (Option (Nat × Ty)) := #[]
    let mut tys : Array Ty := #[]
    for (sp, f?, k?) in steps do
      tys := tys.push ty
      match f?, k?, ty with
      | some "?", _, .opt t => keys := keys.push none; ty := t
      | some "?", _, t => eerr sp s!"'?' in a set needs an option, found {t.show}"
      | some f, _, .struct sn targs =>
        match fieldIndex (ctx.types.fields sn targs) f with
        | some (_, ft) => keys := keys.push none; ty := ft
        | none => eerr sp s!"{ty.show} has no field '{f}'"
      | some f, _, t => eerr sp s!"{t.show} has no field '{f}'"
      | none, some k, .arr t =>
        let ri ← elabE ctx k (some .int)
        if ri.ty != .int then eerr sp "an array index must be an int"
        let ti ← fresh .int
        pre := pre.push (.assign ti ri.e)
        keys := keys.push (some (ti, .int)); ty := t
      | none, some k, .map kt vt =>
        let rk ← elabE ctx k (some kt)
        let tk ← fresh kt
        pre := pre.push (.assign tk (← coerce sp rk kt))
        keys := keys.push (some (tk, kt)); ty := vt
      | _, _, t => eerr sp s!"cannot index a value of type {t.show}"
    let leafTy := ty
    -- the last step from an object (#34): it writes the object in place, so
    -- the path above it is only read, and its field must be a var
    let tysA := tys
    let refLevel? : Option Nat := (List.range steps.length).reverse.find? fun k =>
      match tysA[k]! with
      | .struct sn _ => ctx.types.isRefClass sn
      | _ => false
    if let some kr := refLevel? then
      let (sp, f?, _) := steps.toArray[kr]!
      match tysA[kr]!, f? with
      | .struct sn _, some f =>
        if !ctx.types.isVarField sn f then eerr sp (classSetMsg sn f)
        let ds := ctx.types.concreteBelow sn
        let k0 := ((fieldIndex (ctx.types.fields sn []) f).map (·.1)).getD 0
        if ds.any fun d => ((fieldIndex (ctx.types.fields d []) f).map (·.1)).getD k0 != k0 then
          eerr sp s!"set of field '{f}' of interface {sn}, which is at different places in the classes that implement it, is not supported yet"
      | _, _ => eerr p "internal: set path"
    -- a value of a class with no instance cannot exist: the set is unreachable
    if tysA.any fun | .struct sn _ => ctx.types.isEmptyClass sn | _ => false then
      let tu ← fresh leafTy
      return ⟨.assign tu (.prim .userErr []), leafTy⟩
    if refLevel?.isNone && !l.mutable then
      eerr p s!"'{root}' is not a var; declare it with var {root}:t = …"
    -- the values below the object (or all of them) are rebuilt: a parametric
    -- class among them would change, but it is a value with no var field
    for k in [0:steps.length] do
      if refLevel?.all (k > ·) then
        if let .struct sn _ := tysA[k]! then
          if ctx.types.classes.contains sn && !ctx.types.isRefClass sn then
            let (sp, f?, _) := steps.toArray[k]!
            eerr sp s!"field '{f?.getD "?"}' of the parametric class {sn} cannot be set: a parametric class is a value (#34)"
    -- read one step of the container in slot `c` of type `cty`
    let readStep (c : Nat) (cty : Ty) (step : Option String) (key : Option (Nat × Ty)) : EM Expr := do
      match step, key, cty with
      | some "?", _, .opt _ => pure (.prim .query [.local c])
      | some f, _, .struct sn targs =>
        -- a class's field as when it is read (an interface field may sit at
        -- different places in different classes)
        if ctx.types.classes.contains sn then return (← elabMember ctx p ⟨.local c, cty⟩ f).e
        let (j, _) := (fieldIndex (ctx.types.fields sn targs) f).get!
        pure (.prim (.tupGet j) [.local c])
      | none, some (ti, _), .arr _ => pure (p2 .index (.local c) (.local ti))
      | none, some (tk, kt), .map _ vt =>
        let tp ← fresh (.tup [kt, vt])
        pure (mapLookup c tk tp)
      | _, _, _ => eerr p "internal: set path"
    -- the intermediate containers: level 0 is a copy of the variable, taken
    -- after the indices, so that the right-hand side cannot change what is
    -- rebuilt (as for `set A[i] = e`); the variable is written once, last
    let c0 ← fresh l.ty
    pre := pre.push (.assign c0 (.local l.slot))
    cur := c0
    let stepsA := steps.toArray
    -- with an object on the path, the right-hand side runs once the path has
    -- reached it, before the values in the object are read (#34): a write it
    -- makes through the object is not lost. Without, it runs after every
    -- container is read, as for `set A[i] = e`.
    let rhsAfter : Nat := match refLevel? with
      | some kr => kr
      | none => stepsA.size
    let mut rhsVal : Option R := none
    for k in [0:stepsA.size] do
      let (sp, f?, _) := stepsA[k]!
      levels := levels.push (cur, tys[k]!, sp, f?, keys[k]!)
      if k == rhsAfter then
        let r ← elabE ctx rhs (some leafTy)
        let tr ← fresh r.ty
        pre := pre.push (.assign tr r.e)
        rhsVal := some ⟨.local tr, r.ty⟩
      if k + 1 < stepsA.size then
        let c ← fresh tys[k + 1]!
        pre := pre.push (.assign c (← readStep cur tys[k]! f? keys[k]!))
        cur := c
    let (lc, lty, _, lf, lkey) := levels[levels.size - 1]!
    -- a last `?` step also needs the option to be set
    if lf == some "?" then pre := pre.push (.seq (.prim .query [.local lc]) (.lit .void))
    -- the new leaf value
    let r ← match rhsVal with
      | some r => pure r
      | none => elabE ctx rhs (some leafTy)
    let leaf ← match op with
      | none => coerce p r leafTy
      | some o => combine (← readStep lc lty lf lkey) leafTy o r
    let tv ← fresh leafTy
    pre := pre.push (.assign tv leaf)
    -- rebuild, from the leaf up, as far as the object written in place
    let mut newVal : Expr := .local tv
    let mut wroteObject := false
    for k' in [0:levels.size] do
      let k := levels.size - 1 - k'
      if wroteObject then break
      let (c, cty, _, f?, key) := levels[k]!
      match f?, key, cty with
      | some "?", _, .opt _ => pre := pre.push (.assign c (.prim .mkSome [newVal]))
      | some f, _, .struct sn targs =>
        if ctx.types.isRefClass sn then
          let (j, _) := (fieldIndex (ctx.types.fields sn targs) f).get!
          pre := pre.push (.heap (.set j) [.local c, newVal])
          noteFx p ["writes"]
          wroteObject := true
        else
          let fs := ctx.types.fields sn targs
          let (j, _) := (fieldIndex fs f).get!
          let parts := (List.range fs.length).map fun i =>
            if i == j then newVal else Expr.prim (.tupGet i) [.local c]
          pre := pre.push (.assign c (.prim .mkTup parts))
      | none, some (ti, _), .arr _ =>
        pre := pre.push (.assign c (.prim .arrSet [.local c, .local ti, newVal]))
      | none, some (tk, _), .map _ vt =>
        -- the last key inserts or updates; an intermediate one was read above, so it exists
        let tvk ← fresh vt
        let ti ← fresh .int
        let tidx ← fresh .int
        pre := pre.push (.assign tvk newVal)
        pre := pre.push (mapPut c tk tvk ti tidx)
      | _, _, _ => eerr p "internal: set path"
      newVal := .local c
    if !wroteObject then pre := pre.push (.assign l.slot (.local c0))
    return ⟨pre.toList.foldr Expr.seq (.local tv), leafTy⟩
  match lhs with
  | .ident _ n =>
    let l ← mutableLocal n
    let r ← elabE ctx rhs (some l.ty)
    let v ← match op with
      | none => coerce p r l.ty
      | some o => combine (.local l.slot) l.ty o r
    return ⟨.assign l.slot v, l.ty⟩
  | .app _ (.ident _ n) [k] true =>
    let l ← mutableLocal n
    match l.ty with
    | .map kt vt =>
      let rk ← elabE ctx k (some kt)
      let tk ← fresh kt
      let tp ← fresh (.tup [kt, vt])
      let r ← elabE ctx rhs (some vt)
      let v ← match op with
        | none => coerce p r vt
        -- `set M[k] op= v` fails when k is not a key (Book of Verse §9.3)
        | some o => combine (mapLookup l.slot tk tp) vt o r
      let tv ← fresh vt
      let ti ← fresh .int
      let tidx ← fresh .int
      return ⟨.seq (.assign tk (← coerce p rk kt)) (.seq (.assign tv v)
        (.seq (mapPut l.slot tk tv ti tidx) (.local tv))), vt⟩
    | .arr t =>
      let i := k
      let ri ← elabE ctx i (some .int)
      if ri.ty != .int then eerr p "an array index must be an int"
      let ti ← fresh .int
      let tv ← fresh t
      let r ← elabE ctx rhs (some t)
      let v ← match op with
        | none => coerce p r t
        | some o => combine (p2 .index (.local l.slot) (.local ti)) t o r
      -- `set A[i] = v` fails out of range and returns `v` (Book of Verse §3.3)
      return ⟨.seq (.assign ti ri.e)
        (.seq (.assign l.slot (.prim .arrSet [.local l.slot, .local ti, .assign tv v])) (.local tv)), t⟩
    | ty => eerr p s!"cannot index a value of type {ty.show}"
  | .member mp (.ident _ n) f =>
    -- an object's field: written in place, through any variable (#34)
    if let some l := ctx.lookup n then
      if let .struct sn _ := l.ty then
        if ctx.types.isRefClass sn then
          let targs := match l.ty with | .struct _ ts => ts | _ => []
          let some (k, t) := fieldIndex (ctx.types.fields sn targs) f
            | eerr p s!"class {sn} has no field '{f}'"
          if !ctx.types.isVarField sn f then eerr p (classSetMsg sn f)
          let ds := ctx.types.concreteBelow sn
          if ds.any fun d => ((fieldIndex (ctx.types.fields d []) f).map (·.1)).getD k != k then
            eerr mp s!"set of field '{f}' of interface {sn}, which is at different places in the classes that implement it, is not supported yet"
          let r ← elabE ctx rhs (some t)
          noteFx p (if op.isSome then ["reads", "writes"] else ["writes"])
          let v ← match op with
            | none => coerce p r t
            | some o => combine (.heap (.get k) [.local l.slot]) t o r
          return ⟨.heap (.set k) [.local l.slot, v], t⟩
    if let some l := ctx.lookup n then
      if let .struct sn targs := l.ty then
        if ctx.types.isEmptyClass sn then
          -- no instance can exist: unreachable
          let some (_, t) := fieldIndex (ctx.types.fields sn targs) f | eerr p s!"class {sn} has no field '{f}'"
          let tu ← fresh t
          return ⟨.assign tu (.prim .userErr []), t⟩
        if ctx.types.classes.contains sn && !ctx.types.isRefClass sn then
          eerr p s!"field '{f}' of the parametric class {sn} cannot be set: a parametric class is a value (#34)"
    let l ← mutableLocal n
    match l.ty with
    | .struct sn targs =>
      if ctx.types.classes.contains sn then eerr p (classSetMsg sn f)
      let fs := ctx.types.fields sn targs
      match fieldIndex fs f with
      | some (k, t) =>
        let r ← elabE ctx rhs (some t)
        let v ← match op with
          | none => coerce p r t
          | some o => combine (.prim (.tupGet k) [.local l.slot]) t o r
        let tv ← fresh t
        -- the struct is rebuilt with field k replaced; `set` returns the new field value
        let parts := (List.range fs.length).map fun i =>
          if i == k then Expr.assign tv v else Expr.prim (.tupGet i) [.local l.slot]
        return ⟨.seq (.assign l.slot (.prim .mkTup parts)) (.local tv), t⟩
      | none => eerr p s!"struct {sn} has no field '{f}'"
    | ty => eerr p s!"{ty.show} has no field '{f}'"
  | _ => eerr p "openverse supports set X = …, and set on a path of fields, indices and keys from a variable (set S.F[i].G = …); not through a tuple element or a call result"

/-- `for`: clauses are generators, bindings and filters; each generator opens
    a nested `forE`, and nested results are flattened (cartesian product,
    leftmost outermost). The clauses are a failure context; the body is not. -/
partial def elabFor (ctx : Ctx) (p : Pos) (clauses : List SExpr) (body : SExpr) : EM R := do
  -- split into groups: [filters before the first generator], then (generator, filters)…
  let isGen : SExpr → Bool
    | .gen .. => true
    | .decl _ _ none false (.range ..) => true
    | _ => false
  let pre := clauses.takeWhile (!isGen ·)
  let rest := clauses.dropWhile (!isGen ·)
  let rec groups : List SExpr → List (SExpr × List SExpr)
    | [] => []
    | g :: cs =>
      let fs := cs.takeWhile (!isGen ·)
      (g, fs) :: groups (cs.dropWhile (!isGen ·))
  let gs := groups rest
  let bodyCtx (c : Ctx) : Ctx := { c with canFail := ctx.canFail, inLoop := false }
  -- elaborate the filters of one generator (in a failure context)
  let elabFilters (c : Ctx) (fs : List SExpr) : EM (Expr × Ctx) := do
    match fs with
    | [] => return (.lit (.logic true), c)
    | _ =>
      let (r, c') ← elabSeq { c with canFail := true } fs none
      return (r.e, c')
  let rec build (c : Ctx) (gs : List (SExpr × List SExpr)) : EM R := do
    match gs with
    | [] =>
      let r ← elabE (bodyCtx c) body none
      return r
    | (g, fs) :: more =>
      let declare (c : Ctx) (n : String) (ty : Ty) : EM (Nat × Ctx) := do
        if c.lookup n |>.isSome then eerr g.pos s!"'{n}' is already defined"
        let slot ← fresh ty
        return (slot, { c with locals := { name := n, slot, ty, mutable := false } :: c.locals })
      -- the source: evaluated before the iterations; a failing source gives no iterations
      let (slot, src, c1, pre) ← match g with
        | .decl gp n none false (.range _ lo hi) => do
          let es ← elabInts { c with canFail := true } gp [lo, hi]
          let (slot, c1) ← declare c n .int
          pure (slot, Expr.prim .range es, c1, Expr.lit (.logic true))
        | .gen gp x idx srcE => do
          let rs ← elabE { c with canFail := true } srcE none
          match rs.ty with
          | .map kt vt =>
            -- `for (V : M)` and `for (K -> V : M)`: over the (key, value) pairs
            let tmp ← fresh rs.ty
            let src := if (rs.e.mayFail ctx.sigProg) then
                Expr.orE tmp rs.e (.lit (.arr [])) else rs.e
            let tp ← fresh (.tup [kt, vt])
            let (pre, c1) ← match idx with
              | none => do
                let (xs, c1) ← declare c x vt
                pure (Expr.assign xs (.prim (.tupGet 1) [.local tp]), c1)
              | some i => do
                let (is, c1) ← declare c i kt
                let (xs, c2) ← declare c1 x vt
                pure (Expr.seq (.assign is (.prim (.tupGet 0) [.local tp]))
                  (.assign xs (.prim (.tupGet 1) [.local tp])), c2)
            pure (tp, src, c1, pre)
          | _ =>
          match idx with
          | some i => do
            -- `I -> X : A`: iterate over the indices of A
            let ty ← match rs.ty with
              | .arr t => pure t
              | t => eerr gp s!"a for generator needs an array, string or map, found {t.show}"
            let tmp ← fresh rs.ty
            let src0 := if (rs.e.mayFail ctx.sigProg) then
                Expr.orE tmp rs.e (.lit (.arr [])) else rs.e
            let ta ← fresh rs.ty
            let (islot, c1) ← declare c i .int
            let (xslot, c2) ← declare c1 x ty
            let src := Expr.seq (.assign ta src0)
              (.prim .range [.lit (.int 0), p2 .sub (.prim .len [.local ta]) (.lit (.int 1))])
            pure (islot, src, c2, Expr.assign xslot (p2 .index (.local ta) (.local islot)))
          | none => do
          let ty ← match rs.ty with
            | .arr t => pure t
            | t => eerr gp s!"a for generator needs an array, string or map, found {t.show}"
          let tmp ← fresh rs.ty
          let src := if (rs.e.mayFail ctx.sigProg) then
              Expr.orE tmp rs.e (.lit (.arr [])) else rs.e
          let (slot, c1) ← declare c x ty
          pure (slot, src, c1, Expr.lit (.logic true))
        | _ => eerr g.pos "bad for clause"
      let (filt, c2) ← elabFilters c1 fs
      let filt := if fs.isEmpty then pre else
        match pre with
        | .lit _ => filt
        | e => .seq e filt
      let inner ← build c2 more
      let loopE := Expr.forE slot src filt inner.e
      match more with
      | [] => return ⟨loopE, .arr inner.ty⟩
      | _ =>
        match inner.ty with
        | .arr t => return ⟨.prim .flatten [loopE], .arr t⟩
        | _ => eerr p "internal: nested for"
  match pre with
  | [] => build ctx gs
  | _ =>
    -- filters before any generator: iterate once over a one-element array
    let (filt, c1) ← elabFilters ctx pre
    let slot ← fresh .void
    let inner ← build c1 gs
    match gs with
    | [] => return ⟨.forE slot (.lit (.arr [.tup []])) filt inner.e, .arr inner.ty⟩
    | _ =>
      match inner.ty with
      | .arr t => return ⟨.prim .flatten [.forE slot (.lit (.arr [.tup []])) filt inner.e], .arr t⟩
      | _ => eerr p "internal: nested for"

/-- `e.m`: `.Length` of an array or string, or a field of a struct. -/
partial def elabMember (ctx : Ctx) (p : Pos) (r : R) (m : String) : EM R := do
  match r.ty, m with
  | .arr _, "Length" => return ⟨.prim .len [r.e], .int⟩
  | .map _ _, "Length" => return ⟨.prim .len [r.e], .int⟩
  | .struct sn targs, f =>
    match fieldIndex (ctx.types.fields sn targs) f with
    | some (k, t) =>
      if ctx.types.isRefClass sn then
        -- a reference: the field of its object (#34), at the same position in
        -- every class below a class (inherited fields come first), but maybe
        -- not below an interface: then one test of the object's class each
        let ds := ctx.types.concreteBelow sn
        let pos := ds.map fun d => ((fieldIndex (ctx.types.fields d []) f).map (·.1)).getD k
        if ctx.types.isVarField sn f then noteFx p ["reads"]
        if pos.all (· == k) then return ⟨.heap (.get k) [r.e], t⟩
        let x ← fresh r.ty
        let mut acc : Expr := .prim .userErr []   -- no class: unreachable
        for (d, kd) in (ds.zip pos).reverse do
          let yd ← fresh (.struct d [])
          acc := .ite (.assign yd (.heap (.isTag [ctx.types.tagOf d]) [.local x])) (.heap (.get kd) [.local yd]) acc
        return ⟨.seq (.assign x r.e) acc, t⟩
      if ctx.types.classes.contains sn then
        -- a class: the field of whichever option is set (inherited fields come
        -- first, so it has the same position in all of them)
        let ds := ctx.types.concreteBelow sn
        let x ← fresh r.ty
        let mut acc : Expr := .prim .userErr []   -- no option set: unreachable
        for (d, j) in (ds.zip (List.range ds.length)).reverse do
          let dargs := if d == sn then targs else []
          -- the field's position in `d` (the same in all the classes below a
          -- class, but not below an interface)
          let kd := ((fieldIndex (ctx.types.fields d dargs) f).map (·.1)).getD k
          let td ← fresh (classRepTy ctx.types d dargs)
          acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local x]])) (.prim (.tupGet kd) [.local td]) acc
        let y ← fresh t
        return ⟨.seq (.assign x r.e) (.assign y acc), t⟩
      return ⟨.prim (.tupGet k) [r.e], t⟩
    | none =>
      if ctx.types.classes.contains sn then
        if ctx.hasMethod sn f then eerr p s!"'{f}' is a method of {sn}: call it with {f}(…)"
        eerr p s!"class {sn} has no field '{f}'"
      eerr p s!"struct {sn} has no field '{f}'"
  | t, m => eerr p s!"{t.show} has no member '{m}'"

/-- `name{F := e, …}` or `name(t₁, …){F := e, …}`: the struct's fields in
    declaration order; omitted fields take their default values. The type
    arguments of a parametric struct are written, or are those of the
    expected type. -/
partial def elabConstruct (ctx : Ctx) (p : Pos) (name : String) (targs : List STy) (args : List SExpr)
    (exp : Option Ty) : EM R := do
  if (ctx.types.structs.lookup name).isNone then eerr p s!"unknown struct '{name}'"
  let ty ← match targs, exp with
    | [], some (.struct n ts) => if n == name then pure (.struct n ts) else resolveTy ctx.types p (.name name)
    | [], _ => resolveTy ctx.types p (.name name)
    | ts, _ => resolveTy ctx.types p (.app name ts)
  let tas := match ty with | .struct _ tas => tas | _ => []
  let fs := ctx.types.fields name tas
  -- a default is elaborated with the struct's own type parameters in scope
  let σ := ((ctx.types.sparams.lookup name).getD [] |>.map (·.1)).zip tas
  let dctx := { ctx with locals := [], types := { ctx.types with tvars := σ }, selfClass := none }
  let given ← args.mapM fun a => match a with
    | .decl _ f none false rhs => pure (f, rhs)
    | a => eerr a.pos "a struct field is given as Name := value"
  for (f, _) in given do
    if (fs.find? (·.1 == f)).isNone then eerr p s!"struct {name} has no field '{f}'"
  let es ← fs.mapM fun (f, t, dflt) => do
    match given.lookup f, dflt with
    | some rhs, _ => coerce p (← elabE ctx rhs (some t)) t
    | none, some d =>
      -- the default is code of its home class, at its type arguments here
      let home := (ctx.types.defaultHome.lookup (name, f)).getD name
      let hσ := (((ctx.types.sparams.lookup home).getD []).map (·.1)).zip (ctx.types.argsAt name tas home)
      let dctx := { dctx with types := { ctx.types with tvars := hσ } }
      if dctx.defaults.contains (name, f) then
        eerr p s!"the default of field '{f}' of {name} depends on itself"
      fxAt p (do coerce p (← elabE { dctx with defaults := (name, f) :: dctx.defaults } d (some t)) t)
    | none, none => eerr p s!"field '{f}' of {name} has no default value and must be given"
  if ctx.types.classes.contains name then
    let i := ctx.types.info name
    if i.isIface then eerr p s!"{name} is an interface: it cannot be constructed"
    if i.isAbstract then eerr p s!"{name} is <abstract>: it cannot be constructed"
    -- a new object (#34); one that can change, or has an identity, allocates
    if ctx.types.isRefClass name then
      if ctx.types.isUnique name || fs.any (fun (f, _, _) => ctx.types.isVarField name f) then
        noteFx p ["allocates"]
      -- then the `block:` clauses of its class chain, from the top
      let chain := ((ctx.types.supers name).filter fun d => !(ctx.types.info d).isIface).reverse
      let blocks := chain.filterMap fun d => (ctx.sig? s!"{d}.$block").map (d, ·)
      if blocks.isEmpty then
        -- a parametric class's object goes through a temporary of its type,
        -- which gives the checker its type arguments (#39)
        if tas.isEmpty then return ⟨.heap (.new (ctx.types.tagOf name)) es, ty⟩
        let x ← fresh ty
        return ⟨.assign x (.heap (.new (ctx.types.tagOf name)) es), ty⟩
      let x ← fresh ty
      let mut calls : List Expr := []
      for (d, s) in blocks do
        noteFx p s.fx (some s!"constructs {name}, whose block: (in {d})")
        if s.tparams.isEmpty then
          calls := calls ++ [.call s.idx [.local x]]
        else
          -- a parametric class's `block:` is generic (#39): called as a
          -- method, on the new object at its type arguments as a `d`
          let self := s!"$new{x}"
          let dty := Ty.struct d (ctx.types.upArgs name tas d)
          let ctx' := { ctx with locals := { name := self, slot := x, ty := dty, mutable := false } :: ctx.locals }
          let rc ← elabApp ctx' p (.ident p s!"{d}.$block") [.ident p self] false none
          calls := calls ++ [rc.e]
      return ⟨.seq (.assign x (.heap (.new (ctx.types.tagOf name)) es)) (calls.foldr .seq (.local x)), ty⟩
    let x ← fresh ty
    return ⟨.assign x (classWrap ctx.types name name (.prim .mkTup es)), ty⟩
  return ⟨.prim .mkTup es, ty⟩

/-- `map{k₁ => v₁, …}`: entries are evaluated in order; a key given twice
    keeps its last value, at the position of its last occurrence (Book of
    Verse §9.3). -/
partial def elabMapLit (ctx : Ctx) (p : Pos) (entries : List (SExpr × SExpr)) (exp : Option Ty) : EM R := do
  let (kt?, vt?) := match exp with
    | some (.map k v) => (some k, some v)
    | _ => (none, none)
  match entries with
  | [] =>
    match kt?, vt? with
    | some k, some v => return ⟨.lit (.arr []), .map k v⟩
    | _, _ => eerr p "the type of an empty map{} must be given (e.g. M:[string]int = map{})"
  | (k0, v0) :: _ =>
    let rk0 ← elabE ctx k0 kt?
    let rv0 ← elabE ctx v0 vt?
    let kt := kt?.getD rk0.ty
    if !kt.comparable ctx.types then eerr p (notComparable ctx.types kt "a map key")
    let vt := vt?.getD rv0.ty
    let mut steps : Array Expr := #[]
    let mut slots : Array (Nat × Nat) := #[]
    for (k, v) in entries do
      let rk ← elabE ctx k (some kt)
      let rv ← elabE ctx v (some vt)
      let tk ← fresh kt
      let tv ← fresh vt
      steps := steps.push (.assign tk (← coerce k.pos rk kt))
      steps := steps.push (.assign tv (← coerce v.pos rv vt))
      slots := slots.push (tk, tv)
    let n := slots.size
    let items := (List.range n).map fun i =>
      let (tk, tv) := slots[i]!
      let later := ((List.range n).filter (· > i)).map fun j => Expr.prim .ne [.local tk, .local slots[j]!.1]
      let cond := later.foldr Expr.seq (.lit (.logic true))
      Expr.ite cond (.prim .mkArr [.prim .mkTup [.local tk, .local tv]]) (.lit (.arr []))
    let built := Expr.prim .flatten [.prim .mkArr items]
    return ⟨steps.toList.foldr Expr.seq built, .map kt vt⟩

partial def elabCase (ctx : Ctx) (p : Pos) (scrut : SExpr) (arms : List (Option SExpr × SExpr))
    (exp : Option Ty) : EM R := do
  let rs ← elabE ctx scrut none
  match rs.ty with
  | .int | .logic | .char | .char32 | .arr .char | .enum _ => pure ()
  | t => eerr p s!"case works on int, logic, char, char32, string and enums, not {t.show}"
  let t ← fresh rs.ty
  let elabArms : List (Option SExpr × SExpr) → EM (Expr × Ty) := fun arms => do
    let mut results : Array (Option Expr × R) := #[]
    for (pat, v) in arms do
      let rv ← elabE ctx v exp
      match pat with
      | none => results := results.push (none, rv)
      | some pe =>
        let rp ← elabE ctx pe (some rs.ty)
        if rp.ty != rs.ty then eerr pe.pos s!"pattern of type {rp.ty.show} for a value of type {rs.ty.show}"
        results := results.push (some rp.e, rv)
    let mut ty : Ty := .never
    for (_, rv) in results do ty ← join p ty rv.ty exp
    let hasDefault := results.any (·.1.isNone)
    -- an enum case that names every enumerator needs no `_` (Book of Verse §7.6)
    let exhaustive := match rs.ty with
      | .enum n =>
        let k := ((ctx.types.enums.lookup n).getD []).length
        (List.range k).all fun i => results.any fun (pat, _) => match pat with
          | some (.lit (.int j)) => j == i
          | _ => false
      | _ => false
    let mut acc : Expr ← if hasDefault then pure (.lit .void) else
      if exhaustive then pure (.prim .userErr [])   -- unreachable
      else if ctx.canFail then pure (.prim .fail [])
      else eerr p "a case without _ is only allowed where failure is (e.g. a <decides> function), or on an enum when every value is named"
    for (pat, rv) in results.reverse do
      let v ← coerce p rv ty
      match pat with
      | none => acc := v
      | some pe => acc := .ite (p2 .eq (.local t) pe) v acc
    return (acc, ty)
  let (body, ty) ← elabArms arms
  return ⟨.seq (.assign t rs.e) body, ty⟩
end

/-- An elaborated program and the certificate under which it type-checks:
    `prog.check`, `prog.checkTypes sigs slotTys` and `prog.checkControl` hold,
    so `Prog.accepted` applies to it. -/
structure Compiled where
  prog    : Prog
  sigs    : Sigs
  slotTys : List (List VTy)

/-- Names a type parameter cannot have. -/
def typeNames : List String :=
  ["int", "logic", "char", "string", "void", "float", "rational", "any", "comparable", "type", "subtype"]

/-- The type parameters of a generic function or a parametric struct: name,
    and whether declared `subtype(comparable)`. -/
def checkTParams (env : TyEnv) (tps : List TParam) : Except String (List (String × Bool)) := do
  let mut out : Array (String × Bool) := #[]
  for tp in tps do
    if out.any (·.1 == tp.name) then
      throw s!"{tp.pos.show}: type parameter {tp.name} is declared twice (several constraints on one type parameter are not supported)"
    if typeNames.contains tp.name || (env.structs.lookup tp.name).isSome ||
        (env.enums.lookup tp.name).isSome then
      throw s!"{tp.pos.show}: type parameter {tp.name} has the name of a type"
    match tp.constraint with
    | "type" => out := out.push (tp.name, false)
    | "comparable" => out := out.push (tp.name, true)
    | c => throw s!"{tp.pos.show}: unknown constraint subtype({c}) (openverse supports {tp.name}:type and {tp.name}:subtype(comparable))"
  return out.toList

/-- How a program is compiled from the command line (spec: expected
    tooling): its shell arguments, bound to `Args : []string` (unless the
    program defines `Args`), and an expression to run instead of `Main`. -/
structure Options where
  args : Option (List String) := none
  entry : Option SExpr := none

/-- A class or interface definition, as parsed. -/
structure CDef where
  pos : Pos
  name : String
  tps : List TParam
  specs : List String
  parents : List String
  /-- Each parent's type arguments (#39), in terms of this class's type parameters. -/
  parentArgs : List (List STy) := []
  isIface : Bool
  fields : List (String × STy × Option SExpr × Bool)
  overrides : List String
  methods : List STop

/-- Elaborate a parsed program into a Verse Core program that passes `Prog.check`
    and `Prog.checkTypes`. -/
def elabProgram (allTops00 : List STop) (opts : Options := {}) : Except String Compiled := do
  -- the command line (spec: expected tooling): `Args`, and an entry expression
  let defines (n : String) := allTops00.any fun
    | .fn _ m .. | .const _ m .. | .classDef _ m .. => m == n
  let argsTop : List STop :=
    match opts.args with
    | some as =>
      if defines "Args" then []
      else [.const { line := 0, col := 0 } "Args" (some (.arr (.name "string")))
              (.arrayLit { line := 0, col := 0 } (as.map fun a => .str { line := 0, col := 0 } [.text a]))]
    | none => []
  let entryTop : List STop := match opts.entry with
    | some e => [.fn e.pos "$Do" [] [] ["decides"] (.name "void") (.app e.pos (.ident e.pos "$Show") [e] false)]
    | none => []
  let allTops0 := allTops00 ++ argsTop ++ entryTop
  -- classes and interfaces (#14, #18): each is a struct whose fields are
  -- those inherited first, then its own; each method `M` of `c` a function
  -- `c.M` whose first parameter is `Self`, generic over the class's type
  -- parameters and then its own; an abstract method one whose body is
  -- unreachable
  let cdefs : List CDef := allTops0.filterMap fun
    | .classDef p n tps specs parents isIface fields overrides methods =>
      let names := parents.map fun | .name q => q | .app q _ => q | _ => "?"
      let args := parents.map fun | .app _ as => as | _ => []
      some { pos := p, name := n, tps, specs, parents := names, parentArgs := args, isIface, fields,
             overrides, methods }
    | _ => none
  let cdef? (n : String) : Option CDef := cdefs.find? (·.name == n)
  let methodNamed (cd : CDef) (m : String) : Option STop := cd.methods.find? fun
    | .fn _ x .. => x == m
    | _ => false
  let declares (n m : String) : Bool := ((cdef? n).bind (methodNamed · m)).isSome
  let hasBody (n m : String) : Bool := match (cdef? n).bind (methodNamed · m) with
    | some (.fn _ _ _ _ effs _ _) => !effs.contains "$abstract"
    | _ => false
  -- the hierarchy
  let mut cinfo : Array (String × ClassInfo) := #[]
  for cd in cdefs do
    let p := cd.pos
    for sp in cd.specs do
      match sp with
      | "persistable" | "final_super" => throw s!"{p.show}: <{sp}> classes are not supported yet (#11)"
      | _ => pure ()
    let mut parent : Option String := none
    let mut ifaces : Array String := #[]
    for (q, qargs) in cd.parents.zip cd.parentArgs do
      let some qd := cdef? q
        | if allTops0.any (fun | .const _ n' none (.structDef ..) => n' == q | _ => false) then
            throw s!"{p.show}: {q} is a struct: only classes and interfaces can be inherited from"
          else throw s!"{p.show}: unknown class or interface '{q}'"
      if qd.isIface && !qargs.isEmpty then
        throw s!"{p.show}: interface {q} takes no type arguments"
      if qd.isIface && (!qd.tps.isEmpty || !cd.tps.isEmpty) then
        throw s!"{p.show}: parametric classes cannot implement interfaces yet (#39)"
      if !qd.isIface then
        if qargs.length != qd.tps.length then
          throw s!"{p.show}: {q} takes {qd.tps.length} type argument(s), found {qargs.length}"

      if qd.isIface then ifaces := ifaces.push q
      else
        if cd.isIface then throw s!"{p.show}: interface {cd.name} cannot extend class {q}"
        if parent.isSome then throw s!"{p.show}: class {cd.name} has two superclasses (a class inherits from at most one)"
        if qd.specs.contains "final" then throw s!"{p.show}: class {q} is <final>: it cannot be inherited from"
        parent := some q
    let info : ClassInfo := { parent, ifaces := ifaces.toList, isIface := cd.isIface,
                              isAbstract := cd.specs.contains "abstract", isFinal := cd.specs.contains "final" }
    cinfo := cinfo.push (cd.name, info)
  let henv : TyEnv := { classes := cdefs.map (·.name), cinfo := cinfo.toList }
  let directUp (n : String) : List String := (henv.info n).parent.toList ++ (henv.info n).ifaces
  for cd in cdefs do
    let mut seen : List String := []
    let mut frontier := directUp cd.name
    for _ in [0:cdefs.length + 1] do
      let new := frontier.filter (!seen.contains ·)
      seen := seen ++ new
      frontier := new.flatMap directUp
    if seen.contains cd.name then throw s!"{cd.pos.show}: {cd.name} inherits from itself"
  -- the fields of each class: its superclass's, then those of the
  -- interfaces above it that are not there yet (once, along a diamond), then
  -- its own (an `<override>` field gives an inherited one a new default)
  let mut full : Array (String × List (String × STy × Option SExpr × Bool)) := #[]
  let mut fieldOverrides : Array (Pos × String × String × STy) := #[]
  let mut defaultClashes : Array String := #[]
  for _ in [0:cdefs.length + 1] do
    for cd in cdefs do
      if (full.find? (·.1 == cd.name)).isSome then continue
      let inherited? : Option (List (String × STy × Option SExpr × Bool)) :=
        match (henv.info cd.name).parent with
        | none => some []
        | some q =>
          -- in terms of this class's type parameters (#39)
          let qargs := ((cd.parents.zip cd.parentArgs).lookup q).getD []
          let σ := ((((cdef? q).map (·.tps)).getD []).map (·.name)).zip qargs
          (full.find? (·.1 == q)).map fun (_, fs) => fs.map fun (f, sty, d, v) => (f, sty.substNames σ, d, v)
      let some inh := inherited? | continue
      -- the interfaces above must be resolved first
      let ifacesUp := ((henv.supers cd.name).drop 1).filter (henv.info · |>.isIface)
      if ifacesUp.any (fun i => (full.find? (·.1 == i)).isNone) then continue
      let mut fs : List (String × STy × Option SExpr × Bool) := inh
      -- each interface field not inherited through the class chain, once; its
      -- default is that of the most specific interface that gives one (as for
      -- methods, whatever the order of the parents)
      for i in ifacesUp do
        for (f, sty, _, isVar) in ((full.find? (·.1 == i)).map (·.2)).getD [] do
          if ((henv.supers cd.name).drop 1).any (declares · f) then
            throw s!"{cd.pos.show}: field '{f}' of {cd.name} has the name of an inherited method"
          if let some (_, _, _, v0) := fs.find? (·.1 == f) then
            -- reached again: its type must agree (checked once types are
            -- resolved), and whether it is a var
            if v0 != isVar then
              throw s!"{cd.pos.show}: {cd.name} inherits field '{f}' as a var from one parent and not from another"
            fieldOverrides := fieldOverrides.push (cd.pos, cd.name, f, sty)
          else
            -- the interfaces that give the field a default themselves (an
            -- inherited default is its declaring interface's)
            let ownDefault (j : String) : Option SExpr :=
              (((cdef? j).map (·.fields)).getD []).findSome? fun (g, _, d, _) => if g == f then d else none
            let withDefault := ifacesUp.filter fun j => (ownDefault j).isSome
            let best := withDefault.filter fun j => !withDefault.any fun j' => j' != j && henv.isSub j' j
            if best.length > 1 && !cd.overrides.contains f then
              defaultClashes := defaultClashes.push
                s!"{cd.pos.show}: {cd.name} inherits a default for field '{f}' from both {best[0]!} and {best[1]!}: give it one with {f}<override>:t = e"
            let d := best.head?.bind ownDefault
            fs := fs ++ [(f, sty, d, isVar)]
      for (f, sty, d, isVar) in cd.fields do
        if f == "Self" then throw s!"{cd.pos.show}: a field of {cd.name} cannot be called Self"
        if ((henv.supers cd.name).drop 1).any (declares · f) then
          throw s!"{cd.pos.show}: field '{f}' of {cd.name} has the name of an inherited method"
        match fs.findIdx? (fun (g : String × STy × Option SExpr × Bool) => g.1 == f) with
        | some k =>
          if cd.overrides.contains f && d.isNone then
            throw s!"{cd.pos.show}: {f}<override> must give a new default: write {f}<override>:t = e"
          if !cd.overrides.contains f then
            throw s!"{cd.pos.show}: field '{f}' of {cd.name} has the name of an inherited field (write {f}<override>:t = … to give it a new default)"
          let (_, sty0, _, v0) := fs[k]!
          if isVar != v0 then
            throw s!"{cd.pos.show}: {f}<override> cannot change whether the field is a var"
          fs := fs.set k (f, sty0, d, v0)
          fieldOverrides := fieldOverrides.push (cd.pos, cd.name, f, sty)
        | none =>
          if cd.overrides.contains f then
            throw s!"{cd.pos.show}: {f}<override> in {cd.name} does not override an inherited field"
          fs := fs ++ [(f, sty, d, isVar)]
      full := full.push (cd.name, fs)
  let fullOf (n : String) := ((full.find? (·.1 == n)).map (·.2)).getD []
  for cd in cdefs do
    for (f, _, _, _) in fullOf cd.name do
      if (henv.supers cd.name).any (declares · f) then
        throw s!"{cd.pos.show}: '{f}' is both a field and a method of {cd.name}"
  -- the methods
  let mut expanded : Array STop := #[]
  let mut abstracts : Array (String × String) := #[]
  let mut overridePairs : Array (Pos × String × String) := #[]
  let mut implChecks : Array (Pos × String × String × String) := #[]
  for t in allTops0 do
    match t with
    | .classDef .. => pure ()
    | t => expanded := expanded.push t
  for cd in cdefs do
    let n := cd.name
    let fs := fullOf n
    expanded := expanded.push (.const cd.pos n none (.structDef cd.pos cd.tps fs))
    let selfTy : STy := if cd.tps.isEmpty then .name n else .app n (cd.tps.map fun tp => STy.name tp.name)
    for m in cd.methods do
      match m with
      | .fn mp mn ps mtps effs ret body =>
        if fs.any (·.1 == mn) then throw s!"{mp.show}: '{mn}' is both a field and a method of {n}"
        if ps.any (·.name == "Self") then throw s!"{mp.show}: a method parameter cannot be called Self"
        if builtins.contains mn then throw s!"{mp.show}: a method cannot be called {mn}, the name of a built-in function"
        for prm in ps do
          if fs.any (·.1 == prm.name) || (henv.supers n).any (declares · prm.name) then
            throw s!"{mp.show}: parameter '{prm.name}' of {mn} is already a field or method of {n}; Verse does not allow shadowing"
        -- a class's `block:` clauses: run at construction, after those of the
        -- classes above it, so never overridden
        -- overriding (Book of Verse ch. 10: `M<override>`, the same signature)
        let isOverride := effs.contains "override"
        match if mn == "$block" then [] else ((henv.supers n).drop 1).filter (declares · mn) with
        | [] =>
          if isOverride then throw s!"{mp.show}: {mn}<override> does not override an inherited method"
        | qs@(q :: _) =>
          if !isOverride then throw s!"{mp.show}: {mn} is inherited from {q}: mark it {mn}<override> to override it"
          for q in qs do
            match (cdef? q).bind (methodNamed · mn) with
            | some (.fn _ _ _ qtps qeffs _ _) =>
              if qeffs.contains "final" then throw s!"{mp.show}: {q}.{mn} is <final>: it cannot be overridden"
              if !qtps.isEmpty || !mtps.isEmpty then
                throw s!"{mp.show}: a method with its own type parameters cannot be overridden yet (#18)"
            | _ => pure ()
            overridePairs := overridePairs.push (mp, s!"{n}.{mn}", s!"{q}.{mn}")
        let body ← if effs.contains "$abstract" then do
            if !cd.isIface && !cd.specs.contains "abstract" then
              throw s!"{mp.show}: {mn} has no body: give it one, or make {n} <abstract>"
            abstracts := abstracts.push (n, mn)
            pure (SExpr.app mp (.ident mp "Err") [] false)   -- never called
          else pure body
        expanded := expanded.push
          (.fn mp s!"{n}.{mn}" ({ name := "Self", ty := selfTy } :: ps) (cd.tps ++ mtps) effs ret body)
      | _ => pure ()
  -- a concrete class implements every method it has, each unambiguously
  for cd in cdefs do
    let i := henv.info cd.name
    if i.isIface || i.isAbstract then continue
    let ups := henv.supers cd.name
    let names := (ups.flatMap fun u => ((cdef? u).map (·.methods)).getD [] |>.filterMap fun
      | .fn _ x .. => some x
      | _ => none).eraseDups
    -- (a `block:` is not a method: each class runs its own)
    for mn in names.filter (· != "$block") do
      -- the implementation: the nearest in the class chain, else the most
      -- specific interface default (as `Ctx.implOf?` chooses at a call)
      let impls := ups.filter (hasBody · mn)
      let classImpl := impls.find? fun e => !(henv.info e).isIface
      let ms := impls.filter fun e => !impls.any fun e' => e' != e && henv.isSub e' e
      if impls.isEmpty then
        let q := (ups.find? (declares · mn)).getD cd.name
        throw s!"{cd.pos.show}: {cd.name} must implement {mn} (declared abstract in {q})"
      if classImpl.isNone && ms.length > 1 then
        throw s!"{cd.pos.show}: {cd.name} inherits {mn} from both {ms[0]!} and {ms[1]!}: override it in {cd.name}"
      let impl := classImpl.getD ms.head!
      for q in ups.filter (declares · mn) do
        if q != impl then implChecks := implChecks.push (cd.pos, cd.name, s!"{impl}.{mn}", s!"{q}.{mn}")
  let allTops := expanded.toList
  -- the type definitions: `name := struct …` and `name := enum …`
  let isTypeDef : STop → Bool
    | .const _ _ none (.structDef ..) | .const _ _ none (.enumDef ..) => true
    | _ => false
  let tops := allTops.filter (!isTypeDef ·)
  let varFields : List (String × String) := cdefs.flatMap fun cd =>
    (fullOf cd.name).filterMap fun (f, _, _, isVar) => if isVar then some (cd.name, f) else none
  let uniques : List String := (cdefs.filter (·.specs.contains "unique")).map (·.name)
  let mut env : TyEnv := { classes := henv.classes, cinfo := henv.cinfo, abstracts := abstracts.toList }
  env := { env with varFields := varFields, uniques := uniques }
  -- the class whose code each inherited field default is (#39): the nearest
  -- one, the class's own first, that gives the field a default itself
  let homeOf (c f : String) : String :=
    ((henv.supers c).find? fun x =>
      ((cdef? x).map fun xd => xd.fields.any fun (g, _, d, _) => g == f && d.isSome).getD false).getD c
  env := { env with defaultHome := cdefs.flatMap fun cd =>
    (fullOf cd.name).filterMap fun (f, _, d, _) => d.map fun _ => ((cd.name, f), homeOf cd.name f) }
  for t in allTops do
    match t with
    | .const _ n none (.enumDef _ vals) => env := { env with enums := env.enums ++ [(n, vals)] }
    | .const _ n none (.structDef _ _ _) => env := { env with structs := env.structs ++ [(n, [])] }
    | _ => pure ()
  -- the type parameters of parametric structs
  for t in allTops do
    match t with
    | .const _ n none (.structDef _ tps@(_ :: _) _) =>
      env := { env with sparams := env.sparams ++ [(n, ← checkTParams env tps)] }
    | _ => pure ()
  let shell := env
  let mut structs := #[]
  for t in allTops do
    match t with
    | .const p n none (.structDef _ _ fs) =>
      let senv := { shell with tvars := (shell.sparams.lookup n).getD [] |>.map fun (v, c) => (v, Ty.param v c) }
      let fields ← fs.mapM fun (f, sty, d, _) => do
        let (ty, _) ← (resolveTy senv p sty).run {}
        pure (f, ty, d)
      structs := structs.push (n, fields)
    | _ => pure ()
  env := { env with structs := structs.toList }
  -- the type arguments of each class's parametric superclass (#39)
  let mut pargs : Array (String × List Ty) := #[]
  for cd in cdefs do
    if let some q := (henv.info cd.name).parent then
      let qargs := ((cd.parents.zip cd.parentArgs).lookup q).getD []
      if !qargs.isEmpty then
        let cenv := { env with tvars := ((env.sparams.lookup cd.name).getD []).map fun (v, c) => (v, Ty.param v c) }
        let tys ← qargs.mapM fun sty => do
          let (ty, _) ← (resolveTy cenv cd.pos sty).run {}
          pure ty
        -- a type argument the parent requires to be comparable is
        for (ty, (v, needComp)) in tys.zip ((env.sparams.lookup q).getD []) do
          if needComp && !ty.comparable env then
            throw s!"{cd.pos.show}: {cd.name} gives {q} the type argument {ty.show} for {v}, which must be comparable"
        pargs := pargs.push (cd.name, tys)
  env := { env with pargs := pargs.toList }
  -- a class overrides a method only if its Verse Core type arguments are its
  -- own distinct type parameters, as many as the declaring class's: code
  -- generic over that class can then call its implementation (it could not
  -- give it a type argument it fixes, nor one it adds)
  let core (c : String) : List Ty :=
    env.coreArgs c (((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k)
  for (mp, dm, qm) in overridePairs do
    let d := (dm.splitOn ".").head!
    let q := (qm.splitOn ".").head!
    let mn := (dm.splitOn ".").getLast!
    let (cd', cq) := (core d, core q)
    if cd'.length != cq.length then
      throw s!"{mp.show}: {d} has type parameters that {q} does not have, so it cannot override {mn} yet: code generic over {q} could not give them (#39)"
    -- its Verse Core type arguments are {q}'s, up to renaming
    if ((cq.zip cd').foldlM (fun m (a, b) => Ty.alpha m a b) []).isNone then
      throw s!"{mp.show}: {d} fixes or repeats type arguments that {q} leaves open, so it cannot override {mn} yet: code generic over {q} could not call it (#39)"
  -- a class with Verse Core type arguments cannot be below an interface:
  -- an interface's references have none (C2 of the #39 review)
  for cd in cdefs do
    if !cd.isIface && !(core cd.name).isEmpty then
      if let some i := (env.supers cd.name).find? (env.info · |>.isIface) then
        throw s!"{cd.pos.show}: {cd.name} has type arguments (its own or fixed for a parent), so it cannot implement the interface {i} yet (#39)"
  env := { env with protos := env.makeProtos }
  if let some n := env.recursiveStruct? then
    throw s!"struct {n} contains itself (recursive struct types are not supported)"
  -- map keys in field types, now that every struct's fields are known
  -- (a key type can be a struct that holds a class)
  for (sn, fs) in env.structs do
    for (f, ft, _) in fs do
      if !ft.mapKeysOK env then
        throw s!"field '{f}' of {sn}: a map key must be comparable, and {ft.show} has a key that is not"
  -- generic functions (those with a `where` clause) are numbered after the
  -- other functions and constants
  let isGeneric : STop → Bool
    | .fn _ _ _ (_ :: _) .. => true
    | _ => false
  let generics := tops.filter isGeneric
  let names := tops.map fun | .fn _ n .. => n | .const _ n .. => n | .classDef _ n .. => n
  let tops := tops.filter (!isGeneric ·)
  for (n, i) in names.zip (List.range names.length) do
    if names.take i |>.contains n then throw s!"'{n}' is defined twice (openverse v1 has no overloading)"
    if builtins.contains n then throw s!"'{n}' is a built-in function"
  -- a function's parameter and result types
  let fnTypes (env : TyEnv) (p : Pos) (n : String) (ps : List SParam) (effs : List String) (ret : STy) :
      Except String (List Ty × Ty) := do
    if effs.contains "suspends" then throw s!"{p.show}: <suspends> (concurrency) is not supported by openverse v1"
    let (tys, _) ← ((ps.mapM fun prm => resolveTy env p prm.ty).run {})
    let (rt, _) ← (resolveTy env p ret).run {}
    -- named parameters come last (Book of Verse §8.2)
    let rec namedLast : List SParam → Bool
      | [] => true
      | q :: qs => if q.named then qs.all (·.named) else namedLast qs
    if !namedLast ps then throw s!"{p.show}: in {n}, every parameter after a named one must be named"
    return (tys, rt)
  -- signatures: functions from their annotations, constants from theirs or by inference
  let mut sigs : Array Sig := #[]
  for (top, idx) in tops.zip (List.range tops.length) do
    match top with
    | .fn p n ps _ effs ret _ =>
      let (tys, rt) ← fnTypes env p n ps effs ret
      if effs.contains "computes" && ("transacts" :: heapFx).any effs.contains then
        throw s!"{p.show}: <computes> excludes the heap effects (<reads>, <writes>, <allocates>, <transacts>) that {n} also has"
      sigs := sigs.push { idx, name := n, params := tys, ret := rt, decides := effs.contains "decides",
                          -- (a `block:`'s effects are inferred below, from none, as a
                          -- constant's: blocks that construct each other's classes)
                          fx := if n.endsWith ".$block" then [] else allowedFx effs,
                          isConst := false,
                          named := (ps.filter (·.named)).map fun q => (q.name, q.default) }
    | .const p n sty _ =>
      let rt ← match sty with
        | some t => do let (rt, _) ← (resolveTy env p t).run {}; pure rt
        | none => pure .never   -- inferred below
      -- a constant's heap effects are inferred below, from none
      sigs := sigs.push { idx, name := n, params := [], ret := rt, decides := false, isConst := true, fx := [] }
    | .classDef .. => pure ()   -- expanded above
  -- the signatures of the generic functions, over their type parameters
  let mut gsigs : Array Sig := #[]
  for (top, gidx) in generics.zip (List.range generics.length) do
    match top with
    | .fn p n ps tps effs ret _ =>
      if n == "Main" then throw s!"{p.show}: Main cannot be generic"
      if ps.any (·.named) then
        throw s!"{p.show}: {n} is generic: openverse does not support named parameters in generic functions"
      let tparams ← checkTParams env tps
      let genv := { env with tvars := tparams.map fun (v, c) => (v, Ty.param v c) }
      let (tys, rt) ← fnTypes genv p n ps effs ret
      if effs.contains "computes" && ("transacts" :: heapFx).any effs.contains then
        throw s!"{p.show}: <computes> excludes the heap effects (<reads>, <writes>, <allocates>, <transacts>) that {n} also has"
      -- generic functions come after the others
      gsigs := gsigs.push { idx := tops.length + gidx, name := n, params := tys, ret := rt,
                            decides := effs.contains "decides", isConst := false,
                            -- (a parametric class's `block:`: inferred from none, #41)
                            fx := if n.endsWith ".$block" then [] else allowedFx effs,
                            tparams }
    | _ => pure ()
  let mkSigProg (sigs : Array Sig) : Prog :=
    { fns := (sigs ++ gsigs).toList.map fun s =>
        { name := s.name, arity := s.params.length + s.tparams.length, nslots := 0,
          decides := s.decides, writes := s.fx.contains "writes", body := .lit .void },
      main := 0 }
  -- infer the types of unannotated constants: in order, in rounds, so that a
  -- constant may use one defined after it (until a round makes no progress)
  let unannotated := (tops.zip (List.range tops.length)).filter fun
    | (.const _ _ none _, _) => true
    | _ => false
  let mut todo := unannotated
  for _ in [0:unannotated.length + 1] do
    let mut left := #[]
    for (top, idx) in todo do
      match top with
      | .const _ _ _ body =>
        let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env }
        match (elabE ctx body none).run { env } with
        | .ok (r, _) =>
          if r.ty == .never then left := left.push (top, idx)
          else sigs := sigs.set! idx { sigs[idx]! with ret := r.ty }
        | .error _ => left := left.push (top, idx)
      | _ => pure ()
    if left.size == todo.length then break
    todo := left.toList
  -- the first constant still unknown gives its own error
  for (top, _) in todo do
    match top with
    | .const p n _ body =>
      let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env }
      let (r, _) ← (elabE ctx body none).run { env }
      if r.ty == .never then throw s!"{p.show}: cannot infer the type of '{n}'"
    | _ => pure ()
  -- the heap effects of a constant are those of its initialiser (#35), which
  -- runs at each use: in rounds, from none, since constants use each other
  for _ in [0:tops.length + 1] do
    let mut changed := false
    for (top, idx) in tops.zip (List.range tops.length) do
      match top with
      | .const _ _ _ body =>
        let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env }
        match (elabStmt ctx body (some sigs[idx]!.ret)).run { env } with
        | .ok (_, st) =>
          let fx := heapFx.filter fun k => st.fx.any (·.1 == k)
          if fx != sigs[idx]!.fx then
            sigs := sigs.set! idx { sigs[idx]! with fx }
            changed := true
        | .error _ => pure ()
      -- a class's `block:` clauses have the effects of their code
      | .fn _ n ps _ _ _ body =>
        if n.endsWith ".$block" then
          let s := sigs[idx]!
          let locals := (ps.zip (List.range ps.length)).zip s.params |>.map fun ((prm, i), t) =>
            ({ name := prm.name, slot := i, ty := t, mutable := false } : Local)
          let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env,
                             locals := locals.reverse, retTy := .void,
                             inBlock := true, selfClass := some (n.dropRight ".$block".length) }
          match (elabStmt ctx body (some .void)).run { env, nslots := ps.length, slotTys := s.params.toArray } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k)
            if fx != s.fx then
              sigs := sigs.set! idx { s with fx }
              changed := true
          | .error _ => pure ()
      | _ => pure ()
    -- and so do those of a parametric class, generic (#39)
    for (top, gi) in generics.zip (List.range generics.length) do
      match top with
      | .fn _ n ps _ _ _ body =>
        if n.endsWith ".$block" then
          let g := gsigs[gi]!
          let locals := (ps.zip (List.range ps.length)).zip g.params |>.map fun ((prm, i), t) =>
            ({ name := prm.name, slot := i, ty := t, mutable := false } : Local)
          let hidden := g.tparams.map fun (v, c) => Ty.param v c
          let genv := { env with tvars := g.tparams.map fun (v, c) => (v, Ty.param v c) }
          let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := genv,
                             locals := locals.reverse, retTy := .void, dictBase := ps.length,
                             dictVars := g.tparams.map (·.1),
                             selfClass := some (n.dropRight ".$block".length) }
          match (elabStmt ctx body (some .void)).run
              { env, nslots := ps.length + hidden.length, slotTys := (g.params ++ hidden).toArray } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k)
            if fx != g.fx then
              gsigs := gsigs.set! gi { g with fx }
              changed := true
          | .error _ => pure ()
      | _ => pure ()
    if !changed then break
  let sigProg := mkSigProg sigs
  let allSigs := sigs.toList ++ gsigs.toList
  -- an override has the signature of the method it overrides, and an
  -- overriding field the inherited field's type (Book of Verse ch. 10)
  -- an override may return a class below the declared one (covariant results)
  let retBelow (a b : Ty) : Bool := a == b || match a, b with
    | .struct S as, .struct T bs => env.classes.contains S && env.classes.contains T && env.isSub S T &&
        env.upArgs S as T == bs
    | _, _ => false
  -- the two methods' types as an instance of class `c` sees them: each
  -- class's type parameters at its type arguments there (#39)
  let inC (c e : String) (t : Ty) : Ty :=
    let cps := ((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k
    t.subst ((((env.sparams.lookup e).getD []).map (·.1)).zip (env.upArgs c cps e))
  let clsOf (n : String) : String := (n.splitOn ".").head!
  let sameSigIn (c : String) (a b : Sig) : Bool :=
    let ea := clsOf a.name
    let eb := clsOf b.name
    ((a.params.drop 1).map (inC c ea)) == ((b.params.drop 1).map (inC c eb)) &&
      retBelow (inC c ea a.ret) (inC c eb b.ret) && a.decides == b.decides &&
      a.named.map (·.1) == b.named.map (·.1)
  -- an implementation has no heap effect its declaration does not allow
  let fxOver (a b : Sig) : Option String := a.fx.find? (!b.fx.contains ·)
  for (mp, mine, theirs) in overridePairs do
    match allSigs.find? (·.name == mine), allSigs.find? (·.name == theirs) with
    | some a, some b =>
      if !sameSigIn (clsOf mine) a b then throw s!"{mp.show}: {mine} must have the signature of {theirs}, which it overrides"
      if let some k := fxOver a b then
        throw s!"{mp.show}: {mine} allows the effect <{k}>, which {theirs}, which it overrides, does not"
    | _, _ => pure ()
  -- the implementation a concrete class uses has the signature of every
  -- declaration of the method above it
  for (cp, c, impl, decl) in implChecks do
    match allSigs.find? (·.name == impl), allSigs.find? (·.name == decl) with
    | some a, some b =>
      if !sameSigIn c a b then
        throw s!"{cp.show}: in {c}, {impl} does not have the signature of {decl}"
      if let some k := fxOver a b then
        throw s!"{cp.show}: in {c}, {impl} allows the effect <{k}>, which {decl} does not"
    | _, _ => pure ()
  for (fp, cname, f, sty) in fieldOverrides do
    let cenv := { env with tvars := ((env.sparams.lookup cname).getD []).map fun (v, c) => (v, Ty.param v c) }
    let (t, _) ← (resolveTy cenv fp sty).run {}
    match fieldIndex (env.fields cname) f with
    | some (_, t0) =>
      if !(t == t0) then
        throw s!"{fp.show}: field '{f}' of {cname} must have the type it inherits, {t0.show}, not {t.show}"
    | none => pure ()
  if let some msg := defaultClashes[0]? then throw msg
  -- check every field default once, with its struct's type parameters opaque
  -- (a default is elaborated again, at its field's type, at each construction
  -- that omits the field)
  for t in allTops do
    match t with
    | .const p n none (.structDef _ _ _) =>
      let nps := ((env.sparams.lookup n).getD []).map fun (v, c) => Ty.param v c
      let senv := { env with tvars := (env.sparams.lookup n).getD [] |>.map fun (v, c) => (v, Ty.param v c) }
      let ctx : Ctx := { sigs := allSigs, sigProg, types := senv, canFail := true }
      for (f, ft, d) in (env.structs.lookup n).getD [] do
        if let some d := d then
          -- (an inherited default sees its home class's type parameters, #39)
          let home := (env.defaultHome.lookup (n, f)).getD n
          let hσ := (((env.sparams.lookup home).getD []).map (·.1)).zip (env.argsAt n nps home)
          let ctx := { ctx with defaults := [(n, f)], types := { senv with tvars := hσ } }
          match (do coerce d.pos (← elabE ctx d (some ft)) ft : EM Expr).run { env } with
          | .ok _ => pure ()
          | .error msg => throw s!"{msg} (in the default of field '{f}' of {n})"
    | _ => pure ()
  -- a function: its body under the type environment `env` (which binds the
  -- type parameters `tps` of a generic function to themselves), after the
  -- initialisation of every non-parameter slot (OpenVerse.Core.Typing); its
  -- frame starts with its parameters, then one hidden parameter per type
  -- parameter, holding a value of that type
  -- what each heap effect is, for messages
  let fxWhat : String → String
    | "reads" => "reads a var field"
    | "writes" => "sets a var field"
    | "allocates" => "constructs an object that has a var field or is <unique>"
    | k => k
  let fxCheck (name : String) (allowed : List String) (st : ESt) : Except String Unit := do
    -- writes first, then reads, then allocations
    let order := ["writes", "reads", "allocates"]
    for k in order do
      for (k', kp, via) in st.fx do
        if k' == k && !allowed.contains k then
          let what := match via with
            | some f => s!"{f}, which has the effect <{k}>"
            | none => fxWhat k
          let spec := if allowed.isEmpty then "<computes>" else String.intercalate "" (allowed.map (s!"<{·}>"))
          let fix := if allowed.isEmpty then "remove <computes>" else s!"add <{k}> or <transacts>"
          throw s!"{kp.show}: {name} {what}, which its effects ({spec}) do not allow: {fix}"
  let elabFn (env : TyEnv) (p : Pos) (name : String) (ps : List SParam) (ptys : List Ty) (ret : Ty)
      (decides : Bool) (allowed : List String) (tps : List (String × Bool)) (body : SExpr) :
      Except String (Fn × List VTy) := do
    let locals := (ps.zip (List.range ps.length)).zip ptys |>.map fun ((prm, i), t) =>
      ({ name := prm.name, slot := i, ty := t, mutable := false } : Local)
    for (prm, i) in ps.zip (List.range ps.length) do
      if ps.take i |>.any (·.name == prm.name) then throw s!"{p.show}: duplicate parameter '{prm.name}'"
    let ctx : Ctx := { sigs := allSigs, sigProg, locals := locals.reverse, types := env,
                       canFail := decides, retTy := ret, dictBase := ps.length,
                       dictVars := tps.map (·.1),
                       inBlock := name.endsWith ".$block",
                       selfClass := match name.splitOn "." with
                         | [c, _] => some c
                         | _ => none }
    let hidden := tps.map fun (v, c) => Ty.param v c
    let arity := ps.length + hidden.length
    let ((r, _), st) ← (elabStmt ctx body (some ret)).run
      { env, nslots := arity, slotTys := (ptys ++ hidden).toArray }
    let (e, st) ← (coerce p r ret).run st
    let e := if ret == .void then Expr.seq e (.lit .void) else e
    let inits ← match (st.slotTys.toList.drop arity).mapM (slotDefault env ps.length (ptys ++ hidden) []) with
      | .ok ds => pure ds
      | .error msg => throw s!"{p.show}: in {name}: {msg}"
    fxCheck name allowed st
    return ({ name, arity, nslots := st.nslots, decides, writes := allowed.contains "writes",
              body := initPrefixE arity inits e },
      st.slotTys.toList.map (Ty.toVTy env))
  let genvOf (g : Sig) : TyEnv := { env with tvars := g.tparams.map fun (v, c) => (v, Ty.param v c) }
  let mut fns : Array Fn := #[]
  let mut slotTys : Array (List VTy) := #[]
  for (top, idx) in tops.zip (List.range tops.length) do
    let sig := sigs[idx]!
    match top with
    | .fn p n ps _ _ _ body =>
      let (fn, tys) ← elabFn env p n ps sig.params sig.ret sig.decides sig.fx [] body
      fns := fns.push fn
      slotTys := slotTys.push tys
    | .const p n _ body =>
      -- a constant is computed at each use, so it would be a new object each
      -- time (until Verse Core has global state)
      if sig.ret.holdsMutable env then
        throw s!"{p.show}: the constant {n} would hold an object with var fields or of a <unique> class, which would be a new one at each use: make it a function"
      let ctx : Ctx := { sigs := allSigs, sigProg, types := env }
      let (r, st) ← (elabStmt ctx body (some sig.ret)).run { env }
      let (e, st) ← (coerce p r.1 sig.ret).run st
      let tys := st.slotTys.toList.map (Ty.toVTy env)
      -- slots start like a function's (a class-typed one as a placeholder)
      let inits ← match st.slotTys.toList.mapM (slotDefault env 0 [] []) with
        | .ok ds => pure ds
        | .error msg => throw s!"{p.show}: in {n}: {msg}"
      fxCheck n sig.fx st
      fns := fns.push { name := n, arity := 0, nslots := st.nslots, decides := false,
                        writes := sig.fx.contains "writes", body := initPrefixE 0 inits e }
      slotTys := slotTys.push tys
    | .classDef .. => pure ()   -- expanded above
  -- each generic function is elaborated once, with its type parameters
  -- opaque, as Verse checks it, into one Verse Core function whose types
  -- mention type variables; `Prog.checkTypes` checks it once, for every
  -- instantiation (`Typed.subst`)
  for (top, g) in generics.zip gsigs.toList do
    match top with
    | .fn p n ps _ _ _ body =>
      let (fn, tys) ← elabFn (genvOf g) p n ps g.params g.ret g.decides g.fx g.tparams body
      fns := fns.push fn
      slotTys := slotTys.push tys
    | _ => pure ()
  let mainSig ← match sigs.toList.find? (·.name == (if opts.entry.isSome then "$Do" else "Main")) with
    | some s =>
      if s.isConst || !s.params.isEmpty then throw "Main must be a function with no parameters"
      pure s
    | none => throw "the program has no Main() function"
  -- with prototypes, the program starts with a prelude that allocates them
  -- and then calls `Main` (#37)
  let protoList := env.protos.map fun (_, t, vs) => (t, vs)
  let mut main := mainSig.idx
  if !protoList.isEmpty then
    main := fns.size
    fns := fns.push { name := "$Main", arity := 0, nslots := 0, decides := mainSig.decides,
                      writes := mainSig.fx.contains "writes",
                      body := protoPrelude protoList (.call mainSig.idx []) }
    slotTys := slotTys.push []
  let P : Prog := { fns := fns.toList, main }
  if !P.check then throw "internal error: the elaborated program does not pass Prog.check"
  if !P.checkControl then throw "internal error: the elaborated program does not pass Prog.checkControl"
  let fsigs := sigs.toList.map (fun s => (s.params.map (Ty.toVTy env), s.ret.toVTy env)) ++
    gsigs.toList.map fun g =>
      let genv := genvOf g
      ((g.params ++ g.tparams.map fun (v, c) => Ty.param v c).map (Ty.toVTy genv), g.ret.toVTy genv)
  let fsigs := if protoList.isEmpty then fsigs else fsigs ++ [([], mainSig.ret.toVTy env)]
  -- the class table: the fields of each class, by tag (#34); the prototypes (#37)
  -- (a parametric class's field types mention its type parameters, #39)
  -- each field as the topmost class in the chain that has it gives it, in
  -- terms of the Verse Core type arguments the hierarchy shares: an
  -- `intbox := class(base(int))`'s inherited `Value` is `var 0`, as in `base`
  let classTable := env.classes.map fun d =>
    let chain := ((env.supers d).filter fun x => !(env.info x).isIface).reverse
    if env.isRefClass d then (env.fields d).map fun (f, t, _) =>
      match chain.find? fun D => (env.fields D).any (·.1 == f) with
      | some D =>
        let tD := (((env.fields D).find? (·.1 == f)).map (·.2.1)).getD t
        tD.toVTy { env with tvars := env.coreVars D }
      | none => t.toVTy { env with tvars := env.coreVars d }
    else []
  let S : Sigs := { fns := fsigs, classes := classTable,
                    protos := env.protos.map fun (d, t, _) => (t, (env.coreArgs d []).map (Ty.toVTy env)) }
  if !P.checkTypes S slotTys.toList then
    -- name what fails, for a bug report
    let bad := (List.range P.fns.length).find? fun f =>
      match P.fns[f]?, S.fns[f]?, slotTys[f]? with
      | some fn, some (ps, τ), some Γ => !checkFn S fn ps τ Γ
      | _, _, _ => true
    let which := match bad with
      | some f => s!" (in {((P.fns[f]?).map Fn.name).getD "?"})"
      | none => if !checkPrelude P S then " (the prototypes)" else ""
    throw s!"internal error: the elaborated program does not pass Prog.checkTypes{which}"
  return { prog := P, sigs := S, slotTys := slotTys.toList }

/-- Parse and elaborate Verse source text. -/
def compileChecked (src : String) (opts : Options := {}) : Except String Compiled := do
  elabProgram (← parseProgram src) opts

/-- Parse and elaborate Verse source text. -/
def compile (src : String) (opts : Options := {}) : Except String Prog := do
  return (← compileChecked src opts).prog

/-- Compile loaded definitions (`Front.loadProgram`) with shell arguments,
    bound to `Args` when given or mentioned, and an optional `do` expression. -/
def compileTops (tops : List STop) (args : List String) (mentionsArgs : Bool) (doExpr : Option String) :
    Except String Prog := do
  let entry ← match doExpr with
    | some t => some <$> parseExprText t
    | none => pure none
  let useArgs := !args.isEmpty || mentionsArgs
  return (← elabProgram tops { args := if useArgs then some args else none, entry }).prog

/-- Compile with shell arguments (bound to `Args` when given or used) and an
    optional `do` expression, as `openverse run FILE ARG… do EXPR` does. -/
def compileWith (src : String) (args : List String) (doExpr : Option String) : Except String Prog := do
  let entry ← match doExpr with
    | some t => some <$> parseExprText t
    | none => pure none
  let useArgs := !args.isEmpty || (src.splitOn "Args").length > 1
  compile src { args := if useArgs then some args else none, entry }

end OpenVerse.Front
