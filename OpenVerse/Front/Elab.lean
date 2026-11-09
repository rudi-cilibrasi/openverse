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
import OpenVerse.Front.Suspend
import OpenVerse.Front.Rational
import OpenVerse.Front.Modules
import OpenVerse.Front.FnValues
import OpenVerse.Front.Choice
import OpenVerse.Front.Refine
import Std.Data.HashMap

namespace OpenVerse.Front
open OpenVerse

inductive Ty where
  | int | logic | char | void
  /-- A Unicode scalar value; an `int` in Verse Core. -/
  | char32
  /-- `float` (#127): an IEEE 64-bit float, `VTy.float` in Verse Core. -/
  | float
  /-- `any` (Book of Verse ch. 11, #138): the top type. Nothing can be done
      with its values (no equality, no cast, no ToString), so in Verse Core
      it is `void`: a value becomes an `any` by being evaluated. -/
  | any
  /-- A refinement type (Book of Verse ch. 11, #136): an int or a float that
      meets its conditions; in Verse Core, its base type. -/
  | refine : String → Ty
  /-- `rational`, the type of `X / Y` on ints (Book of Verse ch. 2): in
      Verse Core the tuple of its numerator and denominator, in lowest
      terms with a positive denominator (so tuple equality is equality). -/
  | rational
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
  | .int, .int | .logic, .logic | .char, .char | .char32, .char32 | .rational, .rational | .float, .float | .void, .void | .never, .never => true
  | .any, .any => true
  | .refine a, .refine b => a == b
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
  | .int => "int" | .logic => "logic" | .char => "char" | .char32 => "char32" | .rational => "rational" | .float => "float" | .void => "void"
  | .any => "any"
  | .refine n => n
  | .never => "false"
  | .arr .char => "string"
  | .arr t => "[]" ++ t.show
  | .opt t => "?" ++ t.show
  | .tup ts => "tuple(" ++ ", ".intercalate (ts.map Ty.show) ++ ")"
  | .struct n [] => n
  | .struct n ts =>
    -- (a function type, #210)
    match FnValues.parseName n with
    | some (k, effs) => FnValues.showFn effs ((ts.take k).map Ty.show) ((ts.drop k).headD .void).show
    | none => n ++ "(" ++ ", ".intercalate (ts.map Ty.show) ++ ")"
  | .enum n => n
  | .map k v => "[" ++ k.show ++ "]" ++ v.show
  | .param n _ => n

def Ty.string : Ty := .arr .char

/-- A closed type as written (#214: a function type asked for, for the
    value classes made before elaboration). -/
partial def Ty.toSTy : Ty → STy
  | .int => .name "int" | .logic => .name "logic" | .char => .name "char" | .char32 => .name "char32"
  | .rational => .name "rational" | .float => .name "float" | .void => .name "void" | .any => .name "any"
  | .refine n | .enum n | .param n _ => .name n
  | .never => .name "false"
  | .arr .char => .name "string"
  | .arr t => .arr t.toSTy
  | .opt t => .opt t.toSTy
  | .tup ts => .tup (ts.map Ty.toSTy)
  | .map k v => .map k.toSTy v.toSTy
  | .struct n [] => .name n
  | .struct n ts => match FnValues.parseName n with
    | some (k, effs) => .fn ((ts.take k).map Ty.toSTy) effs ((ts.drop k).headD .void).toSTy
    | none => .app n (ts.map Ty.toSTy)

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
  /-- `cinfo` by name, for speed (a class missing here is looked up in
      `cinfo`: list lookups made the class queries quadratic and their
      users cubic in the number of classes). -/
  cinfoMap : Std.HashMap String ClassInfo := {}
  /-- Each class's place in `classes`, for speed (one missing here is
      looked up in `classes`). -/
  classIx : Std.HashMap String Nat := {}
  /-- The concrete classes at or below each class, in definition order,
      once the classes are known (`belowReady`): the classes added later,
      the placeholders, are never concrete. Computing them for each class
      made the class queries quadratic, and their users cubic. -/
  belowMap : Std.HashMap String (List String) := {}
  belowReady : Bool := false
  /-- `supers` of each class and interface, once the classes are known: each
      walk up a chain made the queries that walk every ancestor's ancestors
      grow with the fourth power of a chain's depth (#238). -/
  supersMap : Std.HashMap String (List String) := {}
  /-- `pinsOf` of each class, once the type arguments are known (#238). -/
  pinsMap : Std.HashMap String (List (Option Ty)) := {}
  /-- The abstract methods (class or interface, method): their functions are
      never called. -/
  abstracts : List (String × String) := []
  /-- Each overloaded function (#74): its overloads, renamed `F$ov0`, `F$ov1`, … -/
  overloads : List (String × List String) := []
  /-- Each overloaded method name (#106): its overloads, one per parameter
      list, renamed `M$ov0`, `M$ov1`, … in every class that declares it. -/
  methodOverloads : List (String × List String) := []
  /-- The type parameters of each parametric struct (name, declared comparable). -/
  sparams : List (String × List (String × Bool)) := []
  /-- Each enum: its enumerators in order. -/
  enums : List (String × List String) := []
  /-- The refinement types (#136): each one's base type (int or float) and
      conditions, `_X op bound` (op `<`, `<=`, `>` or `>=`). -/
  refines : List (String × Ty × List (String × Value)) := []
  /-- The enums declared `enum<open>` (Book of Verse ch. 9): a `case` on one
      needs `_`, as it may gain values. -/
  openEnums : List String := []
  /-- The `var` fields of each class, inherited ones included (#34). -/
  varFields : List (String × String) := []
  /-- The `<unique>` classes: compared by identity (#34). -/
  uniques : List String := []
  /-- The prototype objects `Main`'s prelude allocates, in order (#37): the
      class each one is of, with its tag and fields. A slot of class type
      starts as a reference to one. -/
  protos : List (String × Nat × List Value) := []
  /-- The classes whose fixed type arguments Verse Core records as pins
      (#142): those at or below a class whose implementation of a method
      fixes type arguments that the method's declaring class leaves open. -/
  pinned : List String := []
  /-- The hidden placeholder classes (#157): one below each generic class or
      interface whose concrete classes all fix its type arguments, so that a
      variable of its type at other type arguments has an initial value. The
      program never constructs one and no dispatch reaches one. -/
  phs : List String := []
  /-- The fields read or written through an interface, where they sit at
      different places in the classes below it, of the classes that fix the
      interface's type arguments (#157): (class, field), each reached through
      an accessor pair `get`, `set` at functions `fieldAccBase + 2i`, `+ 1`,
      dispatched under the refinement the class's pins give, as a method. -/
  fieldAcc : List (String × String) := []
  fieldAccBase : Nat := 0
  /-- The functions asked for as values at closed function types (#214). -/
  fnRequests : List (String × Ty) := []
  /-- The order of the slots holding values of the type parameters, when it
      is not that of `tvars` (a method that reads some from its receiver,
      #209, has those after the others). -/
  dictOrder : List String := []
  /-- In a method that reads some type parameters' values from its receiver
      (#209): each one's hidden field, which a slot of its type starts as. -/
  selfWitness : List (String × Nat) := []
  /-- The classes that hold an implementation overriding one above them
      (#209): they keep every pin of theirs (`pinsOf`). -/
  overriders : List String := []
  /-- The type arguments of each class's parametric superclass (#39), in
      terms of the class's own type parameters: `sub(t) := class(base(t))`
      gives `base ↦ [t]`. -/
  pargs : List (String × List Ty) := []
  /-- The type arguments each class or interface gives each interface it
      lists as a parent (#53), in terms of its own type parameters. -/
  iargs : List ((String × String) × List Ty) := []
  /-- The class whose code each field default is, by (class, field): its
      type parameters are those the default mentions (#39). -/
  defaultHome : List ((String × String) × String) := []
  /-- The type parameters in scope, in order (the j-th is `VTy.var j` in
      Verse Core), and what they stand for: themselves (`Ty.param`) in a
      generic function or struct definition, the type arguments of a struct
      construction when its field defaults are elaborated. -/
  tvars : List (String × Ty) := []
  /-- The branches of casts that refine type arguments asked for in an
      earlier elaboration (#243), each lifted into a function. -/
  castRequests : List Refine.Lift := []
  deriving Inhabited

/-- The fields of struct `n` applied to the type arguments `args`. -/
def TyEnv.fields (env : TyEnv) (n : String) (args : List Ty := []) : List (String × Ty × Option SExpr) :=
  let fs := (env.structs.lookup n).getD []
  match env.sparams.lookup n with
  | some ps =>
    let σ := (ps.map (·.1)).zip args
    fs.map fun (f, t, d) => (f, t.subst σ, d)
  | none => fs

def TyEnv.info (env : TyEnv) (c : String) : ClassInfo :=
  match env.cinfoMap[c]? with
  | some i => i
  | none => (env.cinfo.lookup c).getD {}





/-- A class or interface and everything above it: its class chain first,
    nearest first, then the interfaces of the chain, breadth first. This is
    also the order in which a method's implementation is looked up. -/
def TyEnv.supersWalk (env : TyEnv) (c : String) : List String := Id.run do
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

/-- `supersWalk`, from `supersMap` once it is filled. -/
def TyEnv.supers (env : TyEnv) (c : String) : List String :=
  match env.supersMap[c]? with
  | some s => s
  | none => env.supersWalk c

/-- `d` is `T` or below it. -/
def TyEnv.isSub (env : TyEnv) (d T : String) : Bool := (env.supers d).contains T

/-- The roots of a method above `c`, given which classes and interfaces
    declare it: the declarations that override none. Each is a separate slot
    (#70), implemented for one interface by a qualified `(r:)M`, or for every
    slot above it by a plain `M`. -/
def TyEnv.rootsOf (env : TyEnv) (declares : String → Bool) (c : String) : List String :=
  ((env.supers c).filter declares).filter fun r => !((env.supers r).drop 1).any declares

/-- The implementations of slot `r` of a method among `ups` (the classes and
    interfaces above an instance's class, most specific first), given each
    one's implementation of the slot (`impl e`: its `(r:)M`, else a plain
    `M`): the most specific of those below `r` or reached through a class of
    the chain that is not below `r` (what such a class has, its own or a
    default it inherits, implements an interface a subclass adds, as in Java;
    a default of the instance's own interfaces implements only the slots above
    it). The class chain's wins over interface defaults (no interface is below
    a class); several interface defaults are ambiguous. -/
def TyEnv.slotImpls (env : TyEnv) (impl : String → Option String) (ups : List String) (r : String) :
    List String :=
  let outside := ups.filter fun x => !(env.info x).isIface && !env.isSub x r
  let cands := ups.filter fun e => (env.isSub e r || outside.any (env.isSub · e)) && (impl e).isSome
  let best := cands.filter fun e => !cands.any fun e' => e' != e && env.isSub e' e
  (match best.find? (fun e => !(env.info e).isIface) with
   | some e => [e]
   | none => best).filterMap impl

/-- No value has both types (Book of Verse ch. 6, overloading): `void`, a
    type parameter and `never` overlap everything; two arrays, maps or options
    share the empty one (and `?t` and `logic` share `false`); a tuple overlaps
    an array, map or option; a class or interface overlaps an interface and
    the classes above and below it; otherwise different kinds, structs,
    enums and unrelated classes are disjoint. -/
partial def TyEnv.disjoint (env : TyEnv) : Ty → Ty → Bool
  | .void, _ | _, .void | .param .., _ | _, .param .. | .never, _ | _, .never => false
  -- (every value is an any, #138)
  | .any, _ | _, .any => false
  -- (a refinement overlaps what its base does, #136)
  | .refine n, b => match env.refines.lookup n with
    | some (base, _) => env.disjoint base b
    | none => false
  | a, .refine n => match env.refines.lookup n with
    | some (base, _) => env.disjoint a base
    | none => false
  -- (an int is also a rational, #116)
  | .int, .rational | .rational, .int => false
  | .tup as, .tup bs => as.length != bs.length || (as.zip bs).any fun (a, b) => env.disjoint a b
  | .arr _, .arr _ | .arr _, .map .. | .map .., .arr _ | .map .., .map .. | .opt _, .opt _ => false
  -- `false` is also an empty array, an empty option and a logic
  | .opt _, .logic | .logic, .opt _ | .arr _, .opt _ | .opt _, .arr _ | .arr _, .logic | .logic, .arr _ => false
  | .tup _, .arr _ | .arr _, .tup _ | .tup _, .map .. | .map .., .tup _ | .tup _, .opt _ | .opt _, .tup _ => false
  | .struct a as, .struct b bs =>
    let isCls (x : String) := env.classes.contains x
    let iface (x : String) := isCls x && (env.info x).isIface
    if isCls a && isCls b then
      -- one parametric class at disjoint type arguments
      if a == b && !iface a then as.length == bs.length && (as.zip bs).any fun (x, y) => env.disjoint x y
      else if iface a || iface b then
        -- a <final> class, which nothing is below, and an interface it does
        -- not implement (#100)
        let finalNot (c i : String) : Bool := !iface c && (env.info c).isFinal && !env.isSub c i
        (iface a && finalNot b a) || (iface b && finalNot a b)
      else !(env.isSub a b || env.isSub b a)
    else if isCls a || isCls b then true
    else a != b || (as.length == bs.length && (as.zip bs).any fun (x, y) => env.disjoint x y)
  | .enum a, .enum b => a != b
  | .int, .int | .logic, .logic | .char, .char | .char32, .char32 | .rational, .rational | .float, .float => false
  | _, _ => true

/-- Whether two overloads (their positional parameters, then named ones:
    name, has a default, type) are distinct: their positional parameters
    are, or a call cannot give both what they need, as some named parameter
    one of them requires is missing from the other or takes disjoint types in
    the two (Book of Verse ch. 6: order and defaults do not distinguish). -/
def TyEnv.namedDistinct (env : TyEnv) (na nb : List (String × Bool × Ty)) : Bool :=
  let req := ((na.filter (!·.2.1)).map (·.1)) ++ ((nb.filter (!·.2.1)).map (·.1))
  !(req.all fun x => match na.find? (·.1 == x), nb.find? (·.1 == x) with
    | some (_, _, ta), some (_, _, tb) => !env.disjoint ta tb
    | _, _ => false)

/-- Two overloads' parameters: no call fits both. They differ in number (a
    single tuple parameter overlaps as many parameters as it has elements),
    or some position's types are disjoint. -/
def TyEnv.paramsDistinct (env : TyEnv) (as bs : List Ty) : Bool :=
  let flat (xs ys : List Ty) : Bool := match xs with
    | [.tup ts] => ts.length == ys.length
    | _ => false
  if as.length != bs.length then !(flat as bs || flat bs as)
  else (as.zip bs).any fun (a, b) => env.disjoint a b

/-- The type arguments of the class or interface `T` above `d(args)` (along
    the parents, #39, #53), or `[]` when `T` is not above `d`. -/
partial def TyEnv.upArgs (env : TyEnv) (d : String) (args : List Ty) (T : String) : List Ty :=
  if d == T then args
  else
    let σ := (((env.sparams.lookup d).getD []).map (·.1)).zip args
    -- the parent class, then the interfaces: whichever leads to `T`
    let ups : List (String × List Ty) :=
      ((env.info d).parent.toList.map fun q => (q, ((env.pargs.lookup d).getD []).map (·.subst σ))) ++
      ((env.info d).ifaces.map fun i => (i, ((env.iargs.lookup (d, i)).getD []).map (·.subst σ)))
    match ups.find? fun (u, _) => env.isSub u T with
    | some (u, uargs) => env.upArgs u uargs T
    | none => []

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
  | none =>
    -- a root: the type arguments it gives the parametric interfaces above it
    -- (#53), then its other type parameters
    match (env.info d).ifaces.findSome? fun i => env.iargs.lookup (d, i) with
    | some ia =>
      let others := ps.filter fun p => !ia.any fun | .param v _ => v == p | _ => false
      ia.map (·.subst σ) ++ others.map fun p => (σ.lookup p).getD Ty.void
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
def TyEnv.argsBelow (env : TyEnv) (T : String) (targs : List Ty) (d : String) (ext : List Ty := []) :
    List Ty :=
  if d == T then targs else
  let cs := env.coreArgs T targs ++ ext
  let vars := env.coreVars d
  ((env.sparams.lookup d).getD []).map fun (v, _) =>
    match vars.findIdx? (·.1 == v) with
    | some j => cs.getD j Ty.void
    | none => Ty.void

/-- `d`'s Verse Core type arguments are `T`'s, up to renaming: code generic
    over `T` can treat a `d` at its own type arguments (#39, #53). -/
def TyEnv.sameCore (env : TyEnv) (d T : String) : Bool :=
  let core (c : String) := env.coreArgs c (((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k)
  let (cd, cT) := (core d, core T)
  cd.length == cT.length && ((cT.zip cd).foldlM (fun m (a, b) => Ty.alpha m a b) []).isSome

/-- The type arguments of class `D`, above or below `T`, for an instance of
    `T(targs)` (#39). -/
def TyEnv.argsAt (env : TyEnv) (T : String) (targs : List Ty) (D : String) : List Ty :=
  if env.isSub T D then env.upArgs T targs D else env.argsBelow T targs D

/-- The class or interface whose declaration of field `f` gives its type in
    class `d`'s Verse Core layout: the topmost interface above `d` that
    declares it (#53), else the topmost class in `d`'s chain that has it.
    Two unrelated interfaces may both declare it: the first `d` lists. -/
def TyEnv.fieldSrc (env : TyEnv) (d f : String) : Option String :=
  let has := (env.supers d).filter fun x => (env.info x).isIface && (env.fields x).any (·.1 == f)
  let chain := ((env.supers d).filter fun x => !(env.info x).isIface).reverse
  (has.find? fun x => !has.any fun y => y != x && env.isSub x y).orElse fun _ =>
    chain.find? fun D => (env.fields D).any (·.1 == f)

/-- The fields of class `d`, below `T`, with the types they have in an
    object that is a `T(targs)`: each as `fieldSrc` gives it, at that
    class's type arguments there. They are the types of the class table at
    the Verse Core type arguments of `T(targs)`, also for a `d` whose own
    type arguments differ (a placeholder, never read). -/
def TyEnv.fieldsSeen (env : TyEnv) (T : String) (targs : List Ty) (d : String) :
    List (String × Ty × Option SExpr) :=
  (env.fields d).map fun (f, t, dflt) =>
    match env.fieldSrc d f with
    | some D =>
      let tD := (((env.fields D).find? (·.1 == f)).map (·.2.1)).getD t
      let σ := (((env.sparams.lookup D).getD []).map (·.1)).zip (env.argsAt T targs D)
      (f, tD.subst σ, dflt)
    | none => (f, t, dflt)

/-- The concrete classes at or below `T`, in definition order: a value of
    static type `T` holds an instance of one of them. In Verse Core it is the
    tuple of one option per such class, holding that class's fields (#18). -/
def TyEnv.concreteBelow (env : TyEnv) (T : String) : List String :=
  if env.belowReady then env.belowMap[T]?.getD [] else
  env.classes.filter fun d =>
    let i := env.info d
    !i.isIface && !i.isAbstract && env.isSub d T

/-- A class represented by references to heap objects (#34): every class
    and interface, parametric ones too (#39), with a concrete class below,
    and the hidden placeholder classes (#157). -/
def TyEnv.isRefClass (env : TyEnv) (n : String) : Bool :=
  if env.belowReady then
    (env.classIx.contains n || env.classes.contains n) && (env.phs.contains n || !(env.concreteBelow n).isEmpty)
  else
  env.classes.contains n && env.phs.contains n ||
  env.classes.contains n &&
    -- with no concrete class below, `n` has no instance: it stays the (empty)
    -- value of #18, so a variable of its type needs no placeholder
    env.classes.any fun d => let i := env.info d; !i.isIface && !i.isAbstract && (env.supers d).contains n

/-- The class tag of class `d` in Verse Core: its index in definition order. -/
def TyEnv.tagOf (env : TyEnv) (d : String) : Nat :=
  match env.classIx[d]? with
  | some i => i
  | none => (env.classes.idxOf? d).getD 0

/-- The class tags of `T`'s Verse Core reference type: the concrete classes
    at or below it (a reference of static type `T` refers to an object of
    one of them), then the hidden placeholder classes below it (#157). -/
def TyEnv.refTags (env : TyEnv) (T : String) : List Nat :=
  (env.concreteBelow T).map env.tagOf ++ (env.phs.filter (env.isSub · T)).map env.tagOf

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
  -- a struct's fields, and a reference class's Verse Core type arguments
  -- (#63: `loopy := class(cell(?loopy))` would be an infinite type)
  let deps (n : String) : List String :=
    (env.repFieldTys n []).flatMap Ty.structNames ++
      (if env.isRefClass n then
        (env.coreArgs n (((env.sparams.lookup n).getD []).map fun (v, k) => Ty.param v k)).flatMap Ty.structNames
      else [])
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
  | .any => VTy.void
  | .refine n => ((env.refines.lookup n).map fun (b, _) => b.toVTy env).getD .int
  | .rational => .tup [.int, .int]
  | .float => .float
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

/-- Field `f`'s type in class `d`'s Verse Core layout, the class table's,
    over the Verse Core type arguments the hierarchy shares. -/
def TyEnv.coreFieldTy (env : TyEnv) (d f : String) : Option VTy := do
  let D ← env.fieldSrc d f
  let (_, t, _) ← (env.fields D).find? (·.1 == f)
  return t.toVTy { env with tvars := env.coreVars D }

/-- Whether field `f` has one Verse Core type in every class below `sn`,
    `sn`'s own, at the type arguments of `sn(targs)`, as a read through `sn`
    that goes straight to the field needs. A class that fixes type
    arguments can take the field from another interface than `sn` does,
    with a type that agrees with `sn`'s only at the fixed ones (#205). -/
def TyEnv.fieldTyAgrees (env : TyEnv) (sn : String) (targs : List Ty) (f : String) : Bool :=
  let cargs := match (Ty.struct sn targs).toVTy env with
    | .ref _ args => args
    | _ => []
  let τ := (env.coreFieldTy sn f).map (VTy.inst cargs)
  (env.concreteBelow sn).all fun d => (env.coreFieldTy d f).map (VTy.inst cargs) == τ

/-- The type parameters a type mentions. -/
partial def Ty.params : Ty → List String
  | .param n _ => [n]
  | .arr t | .opt t => t.params
  | .tup ts | .struct _ ts => ts.flatMap Ty.params
  | .map k v => k.params ++ v.params
  | _ => []

/-- The name that stands for the `j`-th Verse Core type argument in a pin (#209). -/
def pinArg (j : Nat) : String := s!"$pos{j}"

/-- How many of class `d`'s Verse Core type arguments its root class
    gives: those it gives a parametric interface above it (#53), else all
    of its own. The others are type parameters added below the root. -/
partial def TyEnv.rootArgCount (env : TyEnv) (d : String) : Nat :=
  match (env.info d).parent with
  | some q => env.rootArgCount q
  | none =>
    match (env.info d).ifaces.findSome? fun i => env.iargs.lookup (d, i) with
    | some ia => ia.length
    | none => (env.coreArgs d (((env.sparams.lookup d).getD []).map fun (v, k) => Ty.param v k)).length

/-- The type parameters of class `d` that are not among those its root
    class gives (#209): the ones it pins to themselves (`pinsOf`), whose
    values its objects hold in hidden fields (`$w.…`). -/
def TyEnv.addedParams (env : TyEnv) (d : String) : List String :=
  let ps := ((env.sparams.lookup d).getD []).map (·.1)
  let cs := env.coreArgs d (ps.map fun v => Ty.param v false)
  let nr := env.rootArgCount d
  ps.filter fun v => match cs.findIdx? (fun | .param w _ => w == v | _ => false) with
    | some j => nr ≤ j
    | none => false

/-- The index of the hidden field of class `d` that holds a value of its
    type parameter `v` (#209). -/
def TyEnv.witnessField? (env : TyEnv) (d v : String) : Option Nat :=
  (env.fields d).findIdx? fun (f, t, _) => f.startsWith "$w." && match t with
    | .param w _ => w == v
    | _ => false

/-- The pins of class `d` (#142, #209), by position among its Verse Core
    type arguments (`coreArgs`): `some` the type the class fixes the
    argument to, over the places where its type parameters first occur
    (`pinArg j` for the `j`-th argument), or `none`. A pin is closed
    (`intbox := class(box(int))` gives `[some int]`) or relates the
    argument to others (`dup(t) := class(pair(t, t))` gives `[none, some
    $pos0]`). Every type parameter of `d` is one of its Verse Core type
    arguments (`coreArgs` appends those that are not themselves one of
    its parent's), so arguments that agree with the pins are an instance
    of `d`'s: they determine its type arguments. The pins are on all of
    them (`pairE(a, b) := class(expr(tuple(a, b)))` gives `[some
    (tuple($pos1, $pos2)), none, none]`), so an object has every argument
    a dispatch on a receiver with fewer opens (`Typed.dispatch`). -/
partial def TyEnv.pinsOf (env : TyEnv) (d : String) : List (Option Ty) :=
  match env.pinsMap[d]? with
  | some ps => ps
  | none =>
      let cs := env.coreArgs d (((env.sparams.lookup d).getD []).map fun (v, k) => Ty.param v k)
      let first (v : String) : Option Nat := cs.findIdx? fun | .param w _ => w == v | _ => false
      let σ := (cs.flatMap Ty.params).filterMap fun v => (first v).map fun j => (v, Ty.param (pinArg j) false)
      let own := cs.zipIdx.map fun (t, i) => match t with
        | .param v _ => if first v == some i then none else some (t.subst σ)
        | _ => if t.params.all fun v => (first v).isSome then some (t.subst σ) else none
      -- (a class that only inherits implementations takes its parent's pin
      -- where its own would mention a type argument past its parent's: the
      -- implementations it uses are typed at its parent's, which they cannot
      -- relate to it, and a dispatch to them need not open it)
      match (env.info d).parent with
      | some q =>
        if env.overriders.contains d then own else
        let pq := env.pinsOf q
        let low := lowerPins env own
        own.zipIdx.map fun (o, i) =>
          if ((low.getD i none).all (·.varsBelow pq.length)) then o else pq.getD i none
      | none => own
where
  /-- Pins in Verse Core (as `TyEnv.lowerPins`): `pinArg j` is `var j`,
      also past the pins' length (on a prefix of a class's arguments). -/
  lowerPins (env : TyEnv) (ps : List (Option Ty)) : List (Option VTy) :=
    let idx (v : String) : Nat := if v.startsWith "$pos" then ((v.drop 4).toNat?.getD 0) + 1 else 0
    let n := ((ps.filterMap id).flatMap Ty.params).foldl (fun m v => max m (idx v)) ps.length
    let penv := { env with tvars := (List.range n).map fun j => (pinArg j, Ty.param (pinArg j) false) }
    ps.map (·.map (Ty.toVTy penv))

/-- Pins in Verse Core: `pinArg j` is the type variable `var j`. -/
def TyEnv.lowerPins (env : TyEnv) (ps : List (Option Ty)) : List (Option VTy) :=
  TyEnv.pinsOf.lowerPins env ps

/-- The pins Verse Core records for class `d` (#142): its fixed type
    arguments if it is `pinned`, none otherwise (so that a placeholder of a
    class that needs no refined dispatch can have any type arguments). -/
def TyEnv.corePins (env : TyEnv) (d : String) : List (Option Ty) :=
  if env.pinned.contains d then env.pinsOf d else []

/-- Code generic over `T` can treat a `d` below it under the refinement
    its pins give (#142, #209): `d`'s pins determine its Verse Core type
    arguments (`pinsOf`), and are on all of them, so an object has those
    beyond `T`'s too, which a dispatch on a `T` opens (`Typed.dispatch`). -/
def TyEnv.sameCorePinned (env : TyEnv) (d T : String) : Bool :=
  let core (c : String) := env.coreArgs c (((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k)
  (core T).length ≤ (core d).length

/-- `seq (assign t₁ v₁) (… (call f es))` as the call with each `vᵢ` (a
    literal or a slot) in place of `tᵢ` in its arguments: a call whose
    named arguments went through temporaries (#142). `typed` gives, for
    some temporaries, what to put instead of their literal. -/
partial def Expr.inlineArgTemps (e : Expr) (typed : List (Nat × Expr) := []) : Option Expr :=
  match e with
  | .call f es => some (.call f es)
  | .seq (.assign t v0) rest =>
    let simple := match v0 with
      | .lit _ | .local _ => true
      | _ => false
    if !simple then none else
    let v := (typed.lookup t).getD v0
    (Expr.inlineArgTemps rest typed).map fun
      | .call f es => .call f (es.map fun a => match a with
        | .local t' => if t' == t then v else a
        | _ => a)
      | other => other
  | _ => none

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
  -- (a tuple converts to an array: each element at the element pattern)
  | .arr p, .tup as => as.foldlM (fun σ a => Ty.matchArg env σ p a) σ
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

/-- A most general unifier of equations between types, their type
    parameters the variables (#209), extending `σ`: the refinement that
    `Typed.dispatch` gives by pins, in the front end's types, found as the
    checker's `unify` finds it (each equation in turn; a variable on the
    left is bound first). Its bindings are fully applied. `fieldsOf n ts`
    gives the field types a struct type `n(ts)` is compared by, when it is
    not compared by its type arguments: as Verse Core compares a value
    struct, the tuple of its fields, which need not mention every type
    argument (`tag(t) := struct: N:int`). -/
partial def Ty.unifyEqs (fieldsOf : String → List Ty → Option (List Ty)) (σ : List (String × Ty)) :
    List (Ty × Ty) → Option (List (String × Ty))
  | [] => some σ
  | (a, b) :: rest =>
    let bind (v : String) (t : Ty) : Option (List (String × Ty)) :=
      if t.params.contains v then none
      else
        let s := [(v, t)]
        Ty.unifyEqs fieldsOf ((v, t) :: σ.map fun (w, u) => (w, u.subst s))
          (rest.map fun (x, y) => (x.subst s, y.subst s))
    match a, b with
    | .param v _, .param w _ => if v == w then Ty.unifyEqs fieldsOf σ rest else bind v b
    | .param v _, t => bind v t
    | t, .param v _ => bind v t
    | .arr x, .arr y | .opt x, .opt y => Ty.unifyEqs fieldsOf σ ((x, y) :: rest)
    | .tup xs, .tup ys => if xs.length == ys.length then Ty.unifyEqs fieldsOf σ (xs.zip ys ++ rest) else none
    | .map k v, .map k' v' => Ty.unifyEqs fieldsOf σ ((k, k') :: (v, v') :: rest)
    | .struct n xs, .struct m ys =>
      if n != m || xs.length != ys.length then none
      else match fieldsOf n xs, fieldsOf n ys with
        | some fx, some fy => Ty.unifyEqs fieldsOf σ (fx.zip fy ++ rest)
        | _, _ => Ty.unifyEqs fieldsOf σ (xs.zip ys ++ rest)
    | x, y => if x.eqv y then Ty.unifyEqs fieldsOf σ rest else none

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
  -- (`any` is not: no equality, no map key, #138)
  | .any => false
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

/-- The heap effects (`<transacts>` allows all of them). -/

structure Sig where
  idx     : Nat
  name    : String
  params  : List Ty
  ret     : Ty
  decides : Bool
  isConst : Bool
  /-- The named parameters (the last ones of `params`): name and default. -/
  named   : List (String × Option SExpr) := []
  /-- Every parameter's name, in order: a named one's default may use those
      before it. -/
  pnames  : List String := []
  /-- A generic function's type parameters (name, declared comparable). Its
      `params` and `ret` mention them as `Ty.param`. Its Verse Core function
      takes one more hidden parameter per type parameter, after these: a
      value of that type (`witness`), from which its slots of that type are
      initialised (`slotDefault`). -/
  tparams : List (String × Bool) := []
  /-- The heap effects its specifiers allow (#35). -/
  fx : List String := heapFx
  /-- `<suspends>` (#156): lowered to a frame and a resume function. -/
  suspends : Bool := false
  /-- Of a method of a class with type parameters that its parent's type
      arguments do not give (#209): those type parameters, whose values it
      reads from its receiver's hidden fields (`$w.…`), not from hidden
      parameters, as a dispatch that opens them has none to pass. -/
  selfTps : List String := []
  deriving Inhabited

/-- How many hidden parameters (values of type arguments) a function takes. -/
def Sig.ndicts (s : Sig) : Nat := s.tparams.length - s.selfTps.length

/-- A type built from the primitive comparable types (#214). -/
partial def Ty.plainComparable : Ty → Bool
  | .int | .logic | .char | .char32 | .rational | .float => true
  | .arr t | .opt t => t.plainComparable
  | .tup ts => ts.all Ty.plainComparable
  | .map k v => k.plainComparable && v.plainComparable
  | _ => false

/-- Whether function `s` fits the closed function type `t` other than at its
    own types, as the value classes made for a type asked for do (#214, as
    `FnValues.desugar`): by variance (parameters above the type's and a
    result below, through `int` below `rational` and class subtyping), or a
    generic function at an instance, a comparable type parameter at a type
    built from the primitive comparable types; with at most the type's
    effects. -/
def fnFits (env : TyEnv) (s : Sig) (t : Ty) : Bool :=
  match t with
  | .struct m ts =>
    match FnValues.parseName m with
    | some (k, effs) =>
      -- (the effects only: a tuple parameter may be flattened, #231)
      let sh : FnValues.Shape := ⟨k, s.decides, s.suspends, s.fx⟩
      let qs0 := ts.take k
      let u := (ts.drop k).headD .void
      let subAt (a b : Ty) : Bool := a == b || (a == .int && b == .rational) || match a, b with
        | .struct x [], .struct y [] => x != y && env.isSub x y
        | _, _ => false
      -- (#231) the parameters as the type wants them: as they are, a single
      -- tuple parameter unflattened into the type's, or the parameters
      -- flattened into the type's single tuple parameter
      let reshaped : Option (List Ty × List Ty) :=
        if k == s.params.length then some (s.params, qs0)
        else match s.params, qs0 with
          | [.tup es], _ => if es.length == k then some (es, qs0) else none
          | _, [.tup es] => if es.length == s.params.length then some (s.params, es) else none
          -- (a single parameter, a type parameter say, at the tuple of the
          -- type's parameters: matching decides)
          | [_], _ => if k ≥ 2 then some (s.params, [.tup qs0]) else none
          | _, _ => none
      match reshaped with
      | none => false
      | some (ps, qs) =>
      sh.within (FnValues.shapeOf k effs) &&
        if s.tparams.isEmpty then
          (qs.zip ps).all (fun (q, p) => subAt q p) && subAt s.ret u
        else
          match ((ps ++ [s.ret]).zip (qs ++ [u])).foldlM (fun σ (a, b) => a.matchArg env σ b) [] with
          | some σ => s.tparams.all fun (v, cmp) => match σ.lookup v with
            | some x => !cmp || x.plainComparable
            | none => false
          | none => false
    | none => false
  | _ => false

/-- A value of function type `own` (a shape's interface at its arguments)
    fits function type `t` by variance (#231): the same arity, effects among
    `t`'s, contravariant parameters and a covariant result. -/
def fnTyFits (env : TyEnv) (own t : Ty) : Bool :=
  match own, t with
  | .struct om ots, .struct tm tts =>
    match FnValues.parseName om, FnValues.parseName tm with
    | some (k, oe), some (k', te) =>
      let subAt (a b : Ty) : Bool := a == b || (a == .int && b == .rational) || match a, b with
        | .struct x [], .struct y [] => x != y && env.isSub x y
        | _, _ => false
      k == k' && (FnValues.shapeOf k oe).within (FnValues.shapeOf k te) &&
        ((tts.take k).zip (ots.take k)).all (fun (q, p) => subAt q p) &&
        subAt ((ots.drop k).headD .void) ((tts.drop k).headD .void)
    | _, _ => false
  | _, _ => false

structure Ctx where
  /-- How many retries without an expected type enclose this point: a later
      branch is elaborated against the first's type, else on its own (to
      join), at most a few levels deep (so nested ones stay linear). -/
  retries : Nat := 0
  sigs    : List Sig
  /-- The functions' `<decides>` flags, as a program, for `Expr.mayFail`. -/
  sigProg : Prog
  locals  : List Local := []
  canFail : Bool := false
  inLoop  : Bool := false
  /-- In a named parameter's default, elaborated at a call: no `return`. -/
  inParamDefault : Bool := false
  /-- The `defer:` bodies of the function's enclosing scopes, innermost first
      (#80): a `return` runs them all, a `break` those registered inside its
      loop (all but the first `loopDefers`). -/
  defers  : List (SExpr × List Local) := []
  loopDefers : Nat := 0
  /-- In a `defer:` body, which cannot `return`. -/
  inDefer : Bool := false
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
  /-- In a method `c.M` (or `c.(r:)M`): `M` (or `(r:)M`), for `(super:)`. -/
  selfMethod : Option String := none
  /-- In a constructor's items (the function `K$init`, #72): no `return`. -/
  inCtor : Bool := false
  /-- In a `<suspends>` function (#156): calls of suspends functions allowed. -/
  suspends : Bool := false
  /-- In an arm of `sync`, `race` or `rush` (#156): a `return` returns from
      the function, cancelling the other arms. -/
  inArm : Bool := false
  /-- In a `branch` body (#156): no `return` (the Book's rule). -/
  inBranch : Bool := false
  /-- Checking a field's default once, as a failure context: the default is
      elaborated again at each construction that omits the field, in that
      construction's context (#156). -/
  inDefaultCheck : Bool := false
  /-- In the body of a `loop` or `for`, also through arms (#156): a
      `branch` there would start again before the last one ended. -/
  inRepeat : Bool := false
  /-- In the clauses of an `if` condition or `first{…}` that bind a choice
      (#208), inside a `loop`: a `break` there would leave the loop they are
      compiled to, not that one. -/
  inChoice : Bool := false
  /-- In the clauses of a failure context that takes a choice's values
      (#208): a choice that reaches the elaborator here is in a place it
      cannot be lifted from. -/
  inTaking : Bool := false

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
  /-- The type of each argument of an overloaded call elaborated alone, by
      its position and text (#74): computed once, so nested overloaded calls
      take polynomial time (it survives the trials' state being restored). -/
  natTys : Std.HashMap String (Option Ty) := {}
  /-- Functions wanted as values at closed function types no class of
      theirs gives (#214). -/
  fnNeeds : List (String × Ty) := []
  /-- Where the function calls `Err()` first, if it does: a function whose
      values are all computed at a call (#235) may reach none. -/
  errAt : Option Pos := none
  /-- Branches of casts that refine type arguments, to lift into functions
      (#243): the program is elaborated again, with them. -/
  castNeeds : List Refine.Lift := []
  deriving Inhabited

abbrev EM := StateT ESt (Except String)

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
    if (FnValues.parseName n).isSome then
      s!"{what} must be comparable, and {t.show} is a function type (Book of Verse ch. 4: functions are not comparable)"
    else if env.classes.contains n then
      s!"{what} must be comparable, and {t.show} is a class (only <unique> classes are comparable, by identity)"
    else notComparable.params t what
  | _ => notComparable.params t what
where
  params (t : Ty) (what : String) : String :=
  match t.params with
  | v :: _ => s!"{what} must be comparable, and {t.show} is not: declare {v}:subtype(comparable)"
  | [] => s!"{what} must be comparable, and {t.show} is not"

/-- A method's name as written: `M` for an overload `M$ovN` (#106). -/
def methodBase (x : String) : String := (x.splitOn "$ov").headD x

def builtins : List String :=
  ["Print", "ToString", "Floor", "Ceil", "Abs", "Min", "Max", "Quotient", "Mod", "Err", "ConcatenateMaps"]

/-- Built-in functions a program may also define (#127, #132): its own
    definition, if any, is the one a call means. -/
def softBuiltins : List String :=
  ["Round", "Int", "Sqrt", "Exp", "Ln", "Log", "Pow", "Sin", "Cos", "Tan", "ArcSin", "ArcCos", "ArcTan",
   "IsFinite", "Concatenate"]

partial def resolveTy (env : TyEnv) (p : Pos) : STy → EM Ty
  | .name "int" => pure .int
  | .name "logic" => pure .logic
  | .name "char" => pure .char
  | .name "char32" => pure .char32
  | .name "rational" => pure .rational
  | .name "string" => pure Ty.string
  | .name "void" => pure .void
  | .name "float" => pure .float
  | .name "any" => pure .any
  | .name n =>
    if let some t := env.tvars.lookup n then pure t
    else if (env.structs.lookup n).isSome then
      match env.sparams.lookup n with
      | some ps => eerr p s!"{n} is parametric: write {n}(…) with {ps.length} type argument(s)"
      | none => pure (.struct n [])
    else if (env.enums.lookup n).isSome then pure (.enum n)
    else if (env.refines.lookup n).isSome then pure (.refine n)
    else eerr p s!"unknown type '{n}' (supported: int, logic, char, string, void, []t, ?t, tuple(…), and structs and enums)"
  | .arr t => return .arr (← resolveTy env p t)
  | .opt t => return .opt (← resolveTy env p t)
  | .tup [] => pure .void
  | .tup ts => return .tup (← ts.mapM (resolveTy env p))
  -- a function type: its shape's interface (#210)
  | .fn ps es r => do
    if es.contains "decides" && es.contains "suspends" then
      eerr p "a function type cannot be both <suspends> and <decides>, which exclude each other"
    resolveTy env p (.app (FnValues.shapeOf ps.length es).name (ps ++ [r]))
  | .map k v => do
    let kt ← resolveTy env p k
    if !kt.comparable env then eerr p (notComparable env kt "a map key")
    return .map kt (← resolveTy env p v)
  | .app n args => do
    let ts ← args.mapM (resolveTy env p)
    -- (#220: its handlers take the value, so an event without one has none)
    if n == "subscribable_event" && ts == [.void] && env.classes.contains "$subscription" then
      eerr p "subscribable_event(void), an event without a value, is not supported: give it a type, subscribable_event(t)"
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

/-- How `e` implements slot `r` of method `m`: its `(r:)m`, else its plain
    `m` when not abstract. -/
def Ctx.implAt (ctx : Ctx) (r m e : String) : Option String :=
  if (ctx.sig? s!"{e}.({r}:){m}").isSome then some s!"{e}.({r}:){m}"
  else if (ctx.sig? s!"{e}.{m}").isSome && !ctx.types.abstracts.contains (e, m) then some s!"{e}.{m}"
  else none

/-- The slots of method `m` above `c` (`TyEnv.rootsOf`). -/
def Ctx.rootsOf (ctx : Ctx) (c m : String) : List String :=
  ctx.types.rootsOf (fun e => (ctx.sig? s!"{e}.{m}").isSome) c

/-- The function that implements slot `r` of method `m` for an instance of
    class `d` (#70). -/
def Ctx.implFor? (ctx : Ctx) (d r m : String) : Option String :=
  (ctx.types.slotImpls (ctx.implAt r m) (ctx.types.supers d) r).head?

def p2 (op : Prim) (a b : Expr) : Expr := .prim op [a, b]

/-- The slot of the hidden parameter for type parameter `n`. -/
def TyEnv.dictSlot? (env : TyEnv) (dictBase : Nat) (n : String) : Option Nat :=
  if env.dictOrder.isEmpty then (env.tvars.findIdx? (·.1 == n)).map (dictBase + ·)
  else (env.dictOrder.idxOf? n).map (dictBase + ·)

/-- A value of type `t`, built by an expression whose Verse Core type the
    checker infers exactly (`tc e none`): the hidden argument a call of a
    generic function passes for a type argument `t`. It is only ever used to
    initialise slots, so which value it is does not matter. A class
    reference is a fresh slot of exactly its type (`new` would infer only
    the class constructed), which starts as a placeholder. -/
partial def witness (env : TyEnv) (dictBase : Nat) (dictVars : List String) : Ty → EM Expr
  | .int | .char32 | .enum _ => pure (.lit (.int 0))
  | .rational => pure (.lit (.tup [.int 0, .int 1]))
  | .refine n => match env.refines.lookup n with
    | some (.float, _) => pure (.lit (.float 0))
    | _ => pure (.lit (.int 0))
  | .float => pure (.lit (.float 0))
  | .any => pure (.lit .void)
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

/-- Whether a Verse Core type mentions a type variable, also as a type
    argument of a reference type (a task's result, #204). -/
partial def _root_.OpenVerse.VTy.mentionsVar : VTy → Bool
  | .var _ => true
  | .arr t | .opt t => t.mentionsVar
  | .tup ts | .ref _ ts => ts.any VTy.mentionsVar
  | _ => false

/-- The value of a prototype's field of type `t`: its type's default, or a
    reference to a prototype already allocated (`done`: class, address). -/
partial def protoValue (env : TyEnv) (done : List (String × Nat)) : Ty → Option Value
  | .int | .char32 | .enum _ => some (.int 0)
  | .rational => some (.tup [.int 0, .int 1])
  | .float => some (.float 0)
  | .any => some .void
  | .refine n => match env.refines.lookup n with
    | some (.float, _) => some (.float 0)
    | _ => some (.int 0)
  | .logic => some (.logic false)
  | .char => some (.char 0)
  | .void | .never => some .void
  | .arr _ | .map _ _ => some (.arr #[])
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
  -- (a class whose fields cannot all be literals has none, and the classes
  -- whose fields refer to it then have none either: the addresses are the
  -- positions among those that do, so keep dropping until none is dropped)
  let canMake (cs : List String) (d : String) : Bool :=
    ((env.fields d).mapM fun (f : String × Ty × Option SExpr) => protoValue env cs.zipIdx f.2.1).isSome
  let rec stable : Nat → List String → List String
    | 0, cs => cs
    | n + 1, cs =>
      let ok := cs.filter (canMake cs)
      if ok.length == cs.length then cs else stable n ok
  let cs := stable (concrete.length + 1) concrete
  let addrs := cs.zipIdx
  cs.filterMap fun d =>
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
  if !vt.mentionsVar && !vt.hasRef then return .lit vt.default
  -- a parameter of a subtype: no allocation
  if vt.hasRef then
    if let some i := params.findIdx? (fun pt => (pt.toVTy env).sub vt) then return .local i
  match t with
  | .param n _ =>
    if let some k := env.selfWitness.lookup n then return .heap (.get k) [.local 0]
    match env.dictSlot? dictBase n with
    | some d => return .local d
    | none => return .lit vt.default
  | .tup ts => return .prim .mkTup (← ts.mapM (slotDefault env dictBase params visiting))
  | .struct n ts =>
    -- a prototype of a class below `n` (#37): no allocation
    if env.isRefClass n then
      -- (the classes below and the type arguments once, not per prototype:
      -- a dispatch over n classes makes n such slots)
      let below := env.concreteBelow n
      let args := env.coreArgs n ts
      if let some (_, a) := env.protos.zipIdx.find? fun (x : (String × Nat × List Value) × Nat) =>
          below.contains x.1.1 && env.coreArgs x.1.1 [] == args then
        return .lit (.ref a)
    if env.isRefClass n then
      -- the first class below `n` whose placeholder needs no instance of a
      -- class whose placeholder is being built
      let selfErr := s!"no class at or below {n} can be constructed without an instance of itself, so a variable or temporary of type {(Ty.struct n ts).show} has no initial value"
      let mut lastErr := selfErr
      -- (a failure for want of an instance of itself deeper down is this
      -- one, at the type the slot has: other failures are passed on)
      let keep (msg : String) : String := if msg.startsWith "no class at or below " then selfErr else msg
      -- (instantiations that grow without end are cut off)
      let key := (Ty.struct n ts).show
      if visiting.length > 16 || key.length > 400 then throw lastErr
      let args := (env.coreArgs n ts).map (Ty.toVTy env)
      let mut pinnedOut : List String := []
      for d in env.concreteBelow n do
        let dkey := s!"{d} as {key}"
        if visiting.contains dkey then continue
        -- (an object agrees with its class's pins, #142)
        if !VTy.pinsOK (env.lowerPins (env.corePins d)) args then
          pinnedOut := pinnedOut ++ [d]
          continue
        -- (its fields at the slot's type arguments, #39)
        match (env.fieldsSeen n ts d).mapM fun (_, ft, _) =>
            slotDefault env dictBase params (dkey :: visiting) ft with
        | .ok fs => return .heap (.new (env.tagOf d)) fs
        | .error msg => lastErr := keep msg
      -- (no class can be built: one that some pins ruled out, or that
      -- needs more type arguments than the slot's, #209)
      if !pinnedOut.isEmpty then
        -- (its hidden placeholder class, or another's below it, which fix
        -- no more than it does, #157)
        let h0 := s!"{n}$placeholder"
        let hs := (if env.phs.contains h0 then [h0] else []) ++ env.phs.filter fun h => h != h0 && env.isSub h n
        for h in hs do
          -- (again only at a part of each type it is being built at: a
          -- placeholder at others is another object, `slot(slot(u))`'s
          -- holds `slot(u)`'s, and the types shrink, so this ends; one at
          -- types that grow, `n(t)`'s holding `n([]t)`'s, never would)
          let hpre := s!"{h} as "
          let hkey := hpre ++ key
          let shrinks := visiting.all fun v =>
            !v.startsWith hpre ||
              (let k0 := String.ofList (v.toList.drop hpre.length)
               key.length < k0.length && (k0.splitOn key).length > 1)
          if shrinks then
            match (env.fieldsSeen n ts h).mapM fun (_, ft, _) => slotDefault env dictBase params (hkey :: visiting) ft with
            | .ok fs => return .heap (.new (env.tagOf h)) fs
            | .error msg => lastErr := keep msg
        if !hs.isEmpty then throw lastErr
        throw s!"a variable or temporary of type {key} needs an initial value, and every class below {n} ({", ".intercalate pinnedOut}) fixes type arguments that {key} does not have, so none can be it (#142)"
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
  -- `false` (no value) is below every type, also inside a container
  | .never, _ => true
  | .struct S as, .struct T bs =>
    env.isRefClass S && env.isRefClass T && env.isSub S T && env.upArgs S as T == bs
  | .arr a, .arr b | .opt a, .opt b => refUp env a b
  -- tuples pointwise, maps in their values (Core subtyping is covariant there)
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).all fun (a, b) => a == b || refUp env a b
  | .map k a, .map k' b => k == k' && (a == b || refUp env a b)
  | _, _ => false

/-- The value of a literal expression: a number, or a negated one. -/
def litValue? : Expr → Option Value
  | .lit (.int n) => some (.int n)
  | .lit (.float b) => some (.float b)
  | .prim .neg [.lit (.int n)] => some (.int (-n))
  | .prim .fneg [.lit (.float b)] => some (.float (VFloat.canon (-(VFloat.ofBits b))))
  | _ => none

/-- `a x` or `an x`. -/
def withArticle (x : String) : String :=
  if ["a", "e", "i", "o", "u"].any (x.startsWith ·) then s!"an {x}" else s!"a {x}"

def showLit (e : Expr) : String :=
  match litValue? e with
  | some v => v.render
  | none => "the value"

/-- `v` meets the conditions `_X op bound` of a refinement (#136). -/
def refineHolds (conds : List (String × Value)) (v : Value) : Bool :=
  conds.all fun (op, bound) =>
    match v, bound with
    | .int x, .int y => match op with
      | "<" => x < y | "<=" => x ≤ y | ">" => x > y | _ => x ≥ y
    | .float x, .float y =>
      let (fx, fy) := (VFloat.ofBits x, VFloat.ofBits y)
      match op with
      | "<" => fx < fy | "<=" => fx ≤ fy | ">" => fy < fx | _ => fy ≤ fx
    | _, _ => false

/-- A literal where a refinement is expected (#136): of that refinement
    when it meets its conditions (so that `if (C?) then 5 else 6`,
    `option{5}` and `(5, 1)` take it from their context). -/
def litAt (env : TyEnv) (exp : Option Ty) (r : R) : R :=
  match exp with
  | some (.refine n) =>
    match env.refines.lookup n, litValue? r.e with
    | some (base, conds), some v => if base == r.ty && refineHolds conds v then ⟨r.e, .refine n⟩ else r
    | _, _ => r
  | _ => r

/-- `v < w` on numbers of one base. -/
def numLt : Value → Value → Bool
  | .int x, .int y => x < y
  | .float x, .float y => VFloat.ofBits x < VFloat.ofBits y
  | _, _ => false

def numNeg : Value → Value
  | .int x => .int (-x)
  | .float x => .float (VFloat.canon (-(VFloat.ofBits x)))
  | v => v

/-- A refinement's interval: its tightest lower and upper bounds, each with
    whether it is strict (#143). -/
def refineInterval (conds : List (String × Value)) : Option (Value × Bool) × Option (Value × Bool) :=
  conds.foldl (fun (lo, hi) (op0, b0) =>
    -- (an int's strict bound is the next one, not strict: `< 10` is `<= 9`)
    let (op, b) : String × Value := match op0, b0 with
      | "<", .int x => ("<=", .int (x - 1))
      | ">", .int x => (">=", .int (x + 1))
      | o, v => (o, v)
    let strict := op == "<" || op == ">"
    if op == ">" || op == ">=" then
      let lo' := match lo with
        | none => some (b, strict)
        | some (l, ls) => if numLt l b || (l == b && strict && !ls) then some (b, strict) else some (l, ls)
      (lo', hi)
    else
      let hi' := match hi with
        | none => some (b, strict)
        | some (h, hs) => if numLt b h || (h == b && strict && !hs) then some (b, strict) else some (h, hs)
      (lo, hi')) (none, none)

/-- Interval `a` lies within `b`. -/
def intervalWithin (a b : Option (Value × Bool) × Option (Value × Bool)) : Bool :=
  let lowOk := match a.1, b.1 with
    | _, none => true
    | none, some _ => false
    | some (al, as), some (bl, bs) => numLt bl al || (al == bl && (as || !bs))
  let highOk := match a.2, b.2 with
    | _, none => true
    | none, some _ => false
    | some (ah, as), some (bh, bs) => numLt ah bh || (ah == bh && (as || !bs))
  lowOk && highOk

/-- The interval of `-X` for `X` in `i`. -/
def intervalNeg (i : Option (Value × Bool) × Option (Value × Bool)) : Option (Value × Bool) × Option (Value × Bool) :=
  (i.2.map fun (v, s) => (numNeg v, s), i.1.map fun (v, s) => (numNeg v, s))

/-- A refinement's value as its base (#136): operators, comparisons and
    ToString see the base type. -/
def widenR (env : TyEnv) (r : R) : R :=
  match r.ty with
  | .refine n => match env.refines.lookup n with
    | some (base, _) => ⟨r.e, base⟩
    | none => r
  | _ => r

/-- The conditions of `type{_X:base where c, …}` as `_X op bound`: each
    compares the variable with a literal number (Book of Verse ch. 11). -/
def refineConds (p : Pos) (v : String) (base : Ty) (conds : List SExpr) :
    Except String (List (String × Value)) := do
  if !(base == .int || base == .float) then
    throw s!"{p.show}: a refinement type refines an int or a float, not {base.show}"
  let intBound (n : Int) : Except String Value :=
    if Int64.inRange n then pure (.int n)
    else throw s!"{p.show}: the bound {n} does not fit in 64 bits"
  let bound : SExpr → Except String Value := fun
    | .int _ n => if base == .int then intBound n
      else throw s!"{p.show}: a float refinement's bound is a float literal (write {n}.0)"
    | .neg _ (.int _ n) => if base == .int then intBound (-n)
      else throw s!"{p.show}: a float refinement's bound is a float literal (write -{n}.0)"
    | .float _ b => if base == .float then pure (.float b)
      else throw s!"{p.show}: an int refinement's bound is an int literal"
    | .neg _ (.float _ b) => if base == .float then pure (.float (VFloat.canon (-(VFloat.ofBits b))))
      else throw s!"{p.show}: an int refinement's bound is an int literal"
    | .ident _ "Inf" => if base == .float then pure (.float 0x7FF0000000000000)
      else throw s!"{p.show}: an int refinement's bound is an int literal"
    | .neg _ (.ident _ "Inf") => if base == .float then pure (.float 0xFFF0000000000000)
      else throw s!"{p.show}: an int refinement's bound is an int literal"
    | .ident _ "NaN" => throw s!"{p.show}: NaN cannot bound a refinement"
    | _ => throw s!"{p.show}: a refinement's bound is a literal number, not a variable or an expression"
  let flip : String → String := fun | "<" => ">" | "<=" => ">=" | ">" => "<" | _ => "<="
  conds.mapM fun c => do
    match c with
    | .cmp _ a [(op, b)] =>
      if !["<", "<=", ">", ">="].contains op then
        throw s!"{p.show}: a refinement's condition is <, <=, > or >=, not {op}"
      match a, b with
      | .ident _ x, rhs => if x == v then return (op, ← bound rhs) else
          match rhs with
          | .ident _ y => if y == v then return (flip op, ← bound a) else
              throw s!"{p.show}: a refinement's condition compares {v} with a literal number"
          | _ => throw s!"{p.show}: a refinement's condition compares {v} with a literal number"
      | lhs, .ident _ y => if y == v then return (flip op, ← bound lhs) else
          throw s!"{p.show}: a refinement's condition compares {v} with a literal number"
      | _, _ => throw s!"{p.show}: a refinement's condition compares {v} with a literal number"
    | _ => throw s!"{p.show}: a refinement's condition is a comparison of {v} with a literal number"

/-- Convert a value `e` of type `a` to the supertype `b`, when `a` is a class
    below the class or interface `b`, or an array or option of such (arrays
    and options are covariant): the options of the classes below `a` move to
    their places among those below `b`. -/
partial def convert (env : TyEnv) (e : Expr) (a b : Ty) : EM (Option Expr) := do
  -- references: the same value has both types (Verse Core subtyping, #32)
  if refUp env a b then return some e
  -- no value has a class type with no concrete class below it (an interface
  -- nothing implements, an abstract class with no subclass): the conversion
  -- to a type above it is unreachable (#98)
  if let (.struct S _, .struct T _) := (a, b) then
    if env.classes.contains S && env.classes.contains T && S != T && env.isSub S T &&
        (env.concreteBelow S).isEmpty then
      return some (.seq e (.prim .userErr []))
  match a, b with
  -- `int` is a subtype of `rational` (#116): `X` is `X / 1`
  | .int, .rational => return some (.prim .mkTup [e, .lit (.int 1)])
  -- every value is an `any`, evaluated (#138)
  | _, .any => return some (.seq e (.lit .void))
  -- a refinement is its base (#136); the base is the refinement only for a
  -- literal that meets its conditions (else a cast, `age[X]`)
  -- (a refinement within another's interval is one of it, #143)
  | .refine n, .refine m =>
    match env.refines.lookup n, env.refines.lookup m with
    | some (bn, cn), some (bm, cm) =>
      if bn == bm && intervalWithin (refineInterval cn) (refineInterval cm) then return some e else return none
    | _, _ => return none
  | .refine n, b =>
    match env.refines.lookup n with
    | some (base, _) => if base == b then return some e else convert env e base b
    | none => return none
  | a, .refine n =>
    match env.refines.lookup n, litValue? e with
    | some (base, conds), some v => if base == a && refineHolds conds v then return some e else return none
    | _, _ => return none
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
    | some c =>
      -- (the option first, so that its code is not in the condition: it may
      -- suspend, #156)
      let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a })
      return some (.seq (.assign x e) (.ite (.assign i (.prim .query [.local x])) (.prim .mkSome [c]) (.lit .none)))
    | none => return none
  -- a tuple of convertible elements is a tuple of the converted ones
  | .tup ts, .tup us =>
    if ts.length != us.length then return none
    let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a })
    let mut es : Array Expr := #[]
    for ((ti, ui), i) in (ts.zip us).zip (List.range ts.length) do
      let ei := Expr.prim (.tupGet i) [.local x]
      if ti == ui || ti == .never then es := es.push ei
      else match ← convert env ei ti ui with
        | some c => es := es.push c
        | none => return none
    return some (.seq (.assign x e) (.prim .mkTup es.toList))
  -- a tuple is an array of its elements (Book of Verse ch. 3), each at the
  -- element type
  | .tup ts, .arr t =>
    let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a })
    let mut es : Array Expr := #[]
    for (ti, i) in ts.zip (List.range ts.length) do
      let ei := Expr.prim (.tupGet i) [.local x]
      if ti == t || ti == .never then es := es.push ei
      else match ← convert env ei ti t with
        | some c => es := es.push c
        | none => return none
    return some (.seq (.assign x e) (.prim .mkArr es.toList))
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
  | none =>
    if let .refine n := target then
      if let some (base, _) := (← get).env.refines.lookup n then
        if r.ty == base then
          if (litValue? r.e).isSome then eerr p s!"{showLit r.e} is not {withArticle n}: it does not meet its conditions"
          eerr p s!"{withArticle base.show} is {withArticle n} only after a cast: write {n}[X], which fails when X is not one"
    eerr p s!"expected {target.show}, found {r.ty.show}"

/-- A type above both `a` and `b` (the expected one when it is, #32): two
    classes join at their nearest common supertype, and arrays, options,
    tuples and maps' values join covariantly. -/
partial def joinTy (env : TyEnv) (a b : Ty) (exp : Option Ty) (inner : Bool := false) : Option Ty :=
  if a == .never then some b
  else if b == .never then some a
  else if a == b then some a
  else match a, b with
  | .int, .rational | .rational, .int => if inner then none else some .rational
  -- (refinements join at an expected refinement holding both, or at the
  -- wider of the two, #143)
  | .refine n, .refine m =>
    let within (x y : String) : Bool := match env.refines.lookup x, env.refines.lookup y with
      | some (bx, cx), some (by_, cy) => bx == by_ && intervalWithin (refineInterval cx) (refineInterval cy)
      | _, _ => false
    match exp with
    | some (.refine e) => if within n e && within m e then some (.refine e)
      else if within n m then some (.refine m) else if within m n then some (.refine n)
      else (env.refines.lookup n).map (·.1)
    | _ => if within n m then some (.refine m) else if within m n then some (.refine n)
      else match env.refines.lookup n, env.refines.lookup m with
        | some (bn, _), some (bm, _) => if bn == bm then some bn else none
        | _, _ => none
  | .refine n, b | b, .refine n =>
    match env.refines.lookup n, b with
    | some (base, _), .refine m => if (env.refines.lookup m).map (·.1) == some base then some base else none
    | some (base, _), b => if base == b then some base else none
    | none, _ => none
  | .struct S as, .struct T bs =>
    -- (inside a container, only references convert for free)
    if env.classes.contains S && env.classes.contains T &&
        (!inner || (env.isRefClass S && env.isRefClass T)) then
      -- the expected type, when both are below it, else the nearest common
      -- class above both, else the one interface above both that no other
      -- common one is below (at the same type arguments, #39)
      let up (U : String) (us : List Ty) : Bool :=
        env.isSub S U && env.isSub T U && env.upArgs S as U == us && env.upArgs T bs U == us
      let atU (U : String) : Ty := .struct U (env.upArgs S as U)
      let cands := (env.supers S).filter fun U => up U (env.upArgs S as U)
      let common : Option Ty :=
        match cands.find? fun U => !(env.info U).isIface with
        | some U => some (atU U)
        | none =>
          match cands.filter (fun U => !cands.any fun U' => U' != U && env.isSub U' U) with
          | [U] => some (atU U)
          | _ => none
      match exp with
      | some (.struct U us) => if env.classes.contains U && up U us then some (.struct U us) else common
      | _ => common
    else none
  | .arr x, .arr y => (joinTy env x y (match exp with | some (.arr e) => some e | _ => none) true).map .arr
  | .opt x, .opt y => (joinTy env x y (match exp with | some (.opt e) => some e | _ => none) true).map .opt
  -- (a tuple and an array join as an array, as do tuples of different
  -- lengths where an array is expected: a tuple converts to one)
  | .tup xs, .arr y | .arr y, .tup xs =>
    let e := match exp with | some (.arr e) => some e | _ => none
    (xs.foldlM (fun acc x => joinTy env acc x e true) y).map .arr
  | .tup xs, .tup ys =>
    if xs.length != ys.length then
      match exp with
      | some (.arr e) => ((xs ++ ys).foldlM (fun acc x => joinTy env acc x (some e) true) e).map .arr
      | _ => none
    else
      let es : List (Option Ty) := match exp with
        | some (.tup ets) => if ets.length == xs.length then ets.map some else xs.map fun _ => none
        | _ => xs.map fun _ => none
      ((xs.zip ys).zip es).mapM (fun ((x, y), e) => joinTy env x y e true) |>.map .tup
  | .map k x, .map k' y =>
    if k == k' then (joinTy env x y (match exp with | some (.map _ e) => some e | _ => none) true).map (.map k) else none
  | _, _ => none

/-- A class or interface type. -/
def isClassTy (env : TyEnv) : Ty → Bool
  | .struct n _ => env.classes.contains n
  | _ => false

/-- Two classes or interfaces with a supertype in common, whose failed join
    is an ambiguity (two of them), not unrelated types joining at `any`. -/
def ambiguousJoin (env : TyEnv) : Ty → Ty → Bool
  | .struct a _, .struct b _ =>
    env.classes.contains a && env.classes.contains b && (env.supers a).any (env.supers b).contains
  | _, _ => false

/-- The type of a two-branch construct (`joinTy`; a void branch makes it void). -/
def join (p : Pos) (a b : Ty) (exp : Option Ty) : EM Ty := do
  match exp with
  | some .void => return .void
  | _ =>
    -- void accepts any value (Book of Verse), so a void branch makes the
    -- construct void: `if{X := e} else {Print("none")}`
    if a != .never && b != .never && !(a == b) && (a == .void || b == .void) then return .void
    match joinTy (← get).env a b exp with
    | some t => return t
    | none =>
      -- (types with nothing in common join at `any`, when nothing else is
      -- expected, #138; classes with two common supertypes stay ambiguous)
      if (exp.isNone || exp == some .any) && !ambiguousJoin (← get).env a b then return .any
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

/-- Write `v` to field `f` (of type `t`, at position `k` in `sn`) of the
    object in slot `obj`, of static type `sn(targs)`: in place when the field
    has one position in every class below (`k`, or another for an interface
    listed after a class or interface with fields), otherwise after a test of
    the object's class, as a read does (an interface's field can sit at
    different positions in the classes implementing it). The value is `v`. -/
def setFieldAt (env : TyEnv) (p : Pos) (sn : String) (targs : List Ty) (obj : Nat) (f : String) (k : Nat) (t : Ty)
    (v : Expr) : EM Expr := do
  let ds := env.concreteBelow sn
  let pos := ds.map fun d => ((fieldIndex (env.fields d []) f).map (·.1)).getD k
  -- (where every class below has it, so does every placeholder below, #157,
  -- and with one type in all of them, #205)
  let p0 := pos.headD k
  let tyOK := env.fieldTyAgrees sn targs f
  if tyOK && pos.all (· == p0) then return .heap (.set p0) [.local obj, v]
  if let some d := ds.find? fun d => !env.sameCore d sn && (env.fieldAcc.idxOf? (d, f)).isNone then
    if !tyOK then
      eerr p s!"field '{f}' of {sn} has another type in {d}, which takes it from another interface, and {d} has type parameters that {sn} does not have: setting it through {sn} is not supported yet (#205)"
    eerr p s!"field '{f}' of {sn} sits at different places in the classes below it, and {d} has type parameters that {sn} does not have: setting it is not supported yet (#53, #157)"
  let tv ← fresh t
  let mut acc : Expr := .prim .userErr []   -- no class: unreachable
  let mut refined := false
  for (d, kd) in (ds.zip pos).reverse do
    match env.fieldAcc.idxOf? (d, f) with
    | some i =>
      -- (a class that fixes the type arguments: its setter, under the
      -- refinement, #157)
      acc := .ite (.heap (.isTag [env.tagOf d]) [.local obj]) (.call (env.fieldAccBase + 2 * i + 1) [.local obj, .local tv]) acc
      refined := true
    | none =>
      let yd ← fresh (.struct d (env.argsAt sn targs d))
      acc := .ite (.assign yd (.heap (.isTag [env.tagOf d]) [.local obj])) (.heap (.set kd) [.local yd, .local tv]) acc
  if refined then
    -- (checked against the field's type, as the refined calls need one)
    let y ← fresh t
    return .seq (.assign tv v) (.assign y acc)
  return .seq (.assign tv v) acc

/-- The UTF-8 encoding of the char32 in slot `tc`, a Unicode scalar value:
    its one to four bytes as chars, each looked up in the table of the 256
    byte values (Verse Core has no conversion from int to char; the lookups
    and the divisions cannot fail, but are guarded so that the checker sees
    no failure). -/
def utf8Of (tc : Nat) : EM Expr := do
  let table : Expr := .lit (.arr ((List.range 256).map Value.char).toArray)
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
def toStringOf (p : Pos) (r0 : R) : EM Expr := do
  let r := widenR (← get).env r0
  match r.ty with
  | .char32 => do
    let tc ← fresh .int
    return .seq (.assign tc r.e) (← utf8Of tc)
  | .int | .char | .float => pure (.prim .toStr [r.e])
  | .arr .char => pure r.e
  | t => eerr p s!"no ToString for {t.show} (Verse defines it for int, float, char, char32 and string)"

/-- The names that are values here, for lifting choices (#208): variables
    in scope, `Self` and its fields. -/
def choiceValues (ctx : Ctx) (n : String) : Bool :=
  (ctx.lookup n).isSome || n == "Self" ||
    (match ctx.selfClass with | some c => (ctx.types.fields c).any (·.1 == n) | none => false)

/-- `n.m` reads a field here (a variable or `Self` of a class or struct
    type that has one), for lifting choices: the field is read whole before
    the choice, while a method call's receiver only is (#208). -/
def choiceField (ctx : Ctx) (n m : String) : Bool :=
  let ty? : Option Ty := if n == "Self" then ctx.selfClass.map (fun c => .struct c []) else (ctx.lookup n).map (·.ty)
  match ty? with
  | some (.struct c _) => (ctx.types.fields c).any (·.1 == m)
  | _ => false

/-- A local named `n` may be declared here: Verse has no shadowing. -/
def checkNewLocal (ctx : Ctx) (p : Pos) (n : String) : EM Unit := do
  if ctx.lookup n |>.isSome then
    eerr p s!"'{n}' is already defined; Verse does not allow shadowing (use set {n} = … for a var)"
  -- (nor a soft built-in's: a local cannot hide one, #132)
  if (ctx.sig? n).isSome || builtins.contains n || softBuiltins.contains n then
    eerr p s!"'{n}' is already the name of a function or constant"
  if let some c := ctx.selfClass then
    if (ctx.types.fields c).any (·.1 == n) || ctx.hasMethod c n ||
        ((ctx.types.methodOverloads.lookup n).map (·.any (ctx.hasMethod c ·))).getD false then
      eerr p s!"'{n}' is already a field or method of {c}; Verse does not allow shadowing"

/-- The type parameters a type mentions, with whether each is comparable. -/
partial def Ty.paramsC : Ty → List (String × Bool)
  | .param n c => [(n, c)]
  | .arr t | .opt t => t.paramsC
  | .tup ts | .struct _ ts => ts.flatMap Ty.paramsC
  | .map k v => k.paramsC ++ v.paramsC
  | _ => []

/-- A cast `T[X]`, `X` of type `xty`, that holds only under a refinement of
    the code's type parameters (#243): `T` fixes or repeats type arguments
    of `X`'s class, which agree with `X`'s only when they are unified (as
    `elabCast` refuses). `X`'s class and type arguments, `T`'s type
    arguments, the classes the cast tests for, and the equations of the
    refinement; `none` for any other cast. -/
def refiningCast? (env : TyEnv) (T : String) (xty : Ty) :
    Option (String × List Ty × List Ty × List String × List (Ty × Ty)) := do
  let .struct S sargs := xty | none
  if !env.classes.contains S || !env.classes.contains T then none
  if (env.sparams.lookup T).isNone && (env.coreArgs T []).isEmpty then none
  if !(env.isSub S T || env.isSub T S) then none
  let targs := if env.isSub S T then env.upArgs S sargs T else env.argsBelow S sargs T
  let rargs := env.coreArgs S sargs
  let cargs := env.coreArgs T targs
  if cargs.length > rargs.length || cargs == rargs then none
  let common := (env.concreteBelow S).filter (env.isSub · T)
  if common.isEmpty then none
  let eqs := rargs.zip cargs
  if (Ty.unifyEqs (fun _ _ => none) [] eqs).isNone then none
  some (S, sargs, targs, common, eqs)

/-- What, in the branch of a cast that refines type arguments, would not
    mean the same once the branch is a function of its own (#243): its
    position and what it is. `muts` are the `var`s it uses from outside. -/
def refineBranchWhy? (ctx : Ctx) (p : Pos) (body : SExpr) (muts : List String) : Option (Pos × String) :=
  if ctx.selfClass.isSome then some (p, "it cannot be in a method yet, where it would lose Self")
  else if ctx.inDefer || ctx.inCtor || ctx.inBlock || ctx.inParamDefault || ctx.inArm || ctx.inBranch ||
      !ctx.defaults.isEmpty || ctx.inDefaultCheck then
    some (p, "it cannot be here yet: in a defer:, a constructor's items, a class's block: clause, a field's or parameter's default, or an arm of sync, race, rush or branch")
  else if let some e := Refine.findPart (fun | .ret .. => true | _ => false) false body then
    some (e.pos, "it cannot have a return yet")
  else if let some e := Refine.findPart (fun | .brk _ => true | _ => false) true body then
    some (e.pos, "it cannot have a break that leaves it yet")
  else if let some e := Refine.findPart (fun
      | .set _ l _ _ => (Choice.rootName? l).any muts.contains
      | _ => false) false body then
    some (e.pos, "it cannot set a var from outside it yet")
  else none

mutual
partial def elabE (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  match se with
  | .int p n =>
    if !Int64.inRange n then eerr p s!"integer literal {n} does not fit in 64 bits"
    return litAt ctx.types exp ⟨.lit (.int n), .int⟩
  | .char _ c => return ⟨.lit (.char c), .char⟩
  | .char32 _ c => return ⟨.lit (.int c), .char32⟩
  | .float _ b => return litAt ctx.types exp ⟨.lit (.float b), .float⟩
  | .str p parts =>
    let pieces ← parts.mapM fun part => match part with
      | .text s => pure (Expr.lit (Value.ofString s))
      | .code e => do toStringOf e.pos (← elabE ctx e none)
    let _ := p
    match pieces with
    | [] => return ⟨.lit (Value.ofString ""), Ty.string⟩
    | e :: es => return ⟨es.foldl (fun a b => p2 .concat a b) e, Ty.string⟩
  -- (#209) a hidden field's default: a value of its type
  | .ident p "$witness" =>
    match exp with
    | some t => return ⟨← witness ctx.types ctx.dictBase ctx.dictVars t, t⟩
    | none => eerr p "internal error: a witness without a type"
  | .ident p n =>
    match n with
    | "true" => return ⟨.lit (.logic true), .logic⟩
    | "false" =>
      match exp with
      | some (.opt t) => return ⟨.lit .none, .opt t⟩
      | some (.arr t) => return ⟨.lit (.arr #[]), .arr t⟩
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
          if ctx.hasMethod c n ||
              ((ctx.types.methodOverloads.lookup n).map (·.any (ctx.hasMethod c ·))).getD false then
            -- (a method of `Self` as a value, #210, also an overloaded one,
            -- which the member says is no value)
            return ← elabE ctx (.member p (.ident p "Self") n) exp
        match ctx.sig? n with
        | some s =>
          -- (#214) a function wanted at a closed function type of its arity
          -- that no class of its gives, not asked for yet: asked for, as a
          -- placeholder, the program is elaborated again with a class made
          -- for it (if the function fits the type)
          let askFor : Option Ty := match exp with
            | some t@(.struct m ts) =>
              match FnValues.parseName m with
              | some (k, _) =>
                let _ := k
                if (ts.all fun u => u.params.isEmpty) &&
                    !ctx.types.fnRequests.contains (n, t) && fnFits ctx.types s t then some t else none
              | none => none
            | _ => none
          if s.isConst then
            noteFx p s.fx (some s!"uses the constant {n}")
            return ⟨.call s.idx [], s.ret⟩
          else if let some (cls, ty) := (do
              -- (#214) a value class made for the function type expected,
              -- a written closed one the function fits other than at its
              -- own types (by variance, or a generic one at an instance)
              let t@(.struct m _) ← exp | none
              if (FnValues.parseName m).isNone then none
              let env := ctx.types
              let c ← env.classes.find? fun (c : String) => c.startsWith s!"{n}$fn$" &&
                let i := (env.info c).ifaces.headD ""
                Ty.struct i ((env.iargs.lookup (c, i)).getD []) == t
              some (c, t) : Option (String × Ty)) then
            let r ← elabE ctx (.construct p cls [] []) none
            return ⟨← coerce p r ty, ty⟩
          else if ctx.types.classes.contains s!"{n}$fn" then
            -- a function as a value (#210): its class's object, of the
            -- function type expected, else of its own
            let sh : FnValues.Shape := ⟨s.params.length, s.decides, s.suspends, s.fx⟩
            let own : Ty := .struct sh.name (s.params ++ [s.ret])
            let ty := match exp with
              | some t@(.struct m _) => if (FnValues.parseName m).isSome then t else own
              | _ => own
            -- (through its own type; when the expected one does not fit, as
            -- its own, which the caller then joins or names in a mismatch)
            let r ← elabE ctx (.construct p s!"{n}$fn" [] []) none
            let r : R := ⟨← coerce p r own, own⟩
            if ty == own then return r
            match ← tryCatch (some <$> coerce p r ty) (fun _ => pure none) with
            | some e => return ⟨e, ty⟩
            | none =>
              if let some t := askFor then
                modify fun st => { st with fnNeeds := st.fnNeeds ++ [(n, t)] }
                return ⟨.prim .userErr [], t⟩
              return r
          else if let some t := askFor then
            modify fun st => { st with fnNeeds := st.fnNeeds ++ [(n, t)] }
            return ⟨.prim .userErr [], t⟩
          else if !s.tparams.isEmpty then
            eerr p s!"'{n}' is generic: a generic function is a value only where a closed function type that is an instance of its type is expected (X:type\{…} = {n}, or as an argument of such a parameter), not at a type over type parameters, #214"
          else if !s.named.isEmpty then
            eerr p s!"'{n}' has named parameters: such a function cannot be used as a value (a function type has no named parameters)"
          else eerr p s!"'{n}' is a function: call it with {n}(…)"
        | none =>
          if (ctx.types.overloads.lookup n).isSome then
            eerr p s!"{n} is overloaded: an overloaded function cannot be used as a value (Book of Verse ch. 6)"
          -- the float constants (#132), unless the program defines them
          match n with
          | "PiFloat" => return ⟨.lit (.float (VFloat.canon 3.141592653589793)), .float⟩
          | "Inf" => return ⟨.lit (.float 0x7FF0000000000000), .float⟩
          | "NaN" => return ⟨.lit (.float VFloat.nanBits), .float⟩
          | _ => eerr p s!"unknown identifier '{n}'"
  -- a constructor's `block:` (#11): it cannot fail, as a class's cannot
  | .app _ (.ident _ "$nofail") [e] false => elabE { ctx with canFail := false, inBlock := true } e exp
  | .app p (.ident _ "$defer") _ _ => eerr p "defer: is a statement: it has no value"
  | .app p (.ident _ "$sync") arms false => elabConc ctx p true arms exp
  | .app p (.ident _ "$race") arms false => elabConc ctx p false arms exp
  | .app p (.ident _ "$rush") arms false => elabConc ctx p false arms exp true
  | .app p (.ident _ "$spawn") [body] false => elabSpawn ctx p body
  | .app p (.ident _ "$branch") [body] false => elabBranch ctx p body
  | .app _ (.ident _ "$witness") [.ident _ n] false =>
    -- (a value of type parameter `n`, as the hidden argument of a generic
    -- call for it: the type argument of a lifted branch (#243) that only its
    -- written types mention)
    let t := (ctx.types.tvars.lookup n).getD (.param n false)
    return ⟨← witness ctx.types ctx.dictBase ctx.dictVars t, t⟩
  | .app p (.ident _ "$fxOf") [.ident _ f] false =>
    -- (an inlined call of a function with several values: its declared
    -- effects, as at a call, #235)
    if let some s := ctx.sig? f then noteFx p s.fx (some s!"calls {f}")
    return ⟨.lit .void, .void⟩
  | .app p (.ident _ "$inline") (.ident _ f :: _) false =>
    if ctx.inTaking then
      eerr p s!"a call of {f}, which has several values, cannot be lifted from here, for now (#235)"
    eerr p (s!"{f} has several values, so a call of it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#235)")
  | .app p (.ident _ "$each") (.app _ (.ident _ fa) _ _ :: _) false =>
    -- (a call of a recursive function with several values, #235)
    let f := if fa.endsWith "$all" then String.ofList (fa.toList.take (fa.length - 4)) else fa
    if ctx.inTaking then
      eerr p (s!"a call of {f}, which has several values, cannot be lifted from here, for now (#235): " ++
        "not from a block, a struct construction, a named argument, a choice's alternative, the right of " ++
        "and or or, a range, a set's path, nor from the branch of an if")
    eerr p (s!"{f} has several values, so a call of it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#235)")
  | .app p (.ident _ "$choice") _ false =>
    if ctx.inTaking then
      eerr p ("a choice (a | b) cannot be lifted from here, for now (#208): not from a block, a struct " ++
        "construction, a named argument, another choice's alternative, the right of and or or, a range, " ++
        "nor from the branch of an if without else or one that is more than a choice or a value")
    eerr p ("a choice (a | b) has several values, so it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#208)")
  | .app p (.ident _ "$first") [.block bp items] false =>
    -- `first{…}` and `first(…){…}`: without a choice, a block
    if !Choice.hasChoice items.dropLast then return ← elabE ctx (.block bp items) exp
    -- with one (#208): the first success of the clauses, then the value (or
    -- body), which sees their names
    if !ctx.canFail then
      eerr p "first{…} with a choice can fail, but it is not in a failure context (#208)"
    let (rc, c1) ← elabOneClauses ctx items.dropLast
    let rv ← elabE c1 (items.getLastD (.tuple p [])) exp
    return ⟨.seq rc.e rv.e, rv.ty⟩
  | .app p f args bracket => elabApp ctx p f args bracket exp
  | .member p (.ident _ n) m =>
    if n == "(super:)" then
      eerr p s!"(super:){m} cannot be used as a value: call it with (super:){m}(…), or name a method that calls it"
    match ctx.lookup n, ctx.types.enums.lookup n with
    | none, some vals =>
      -- `color.Red`: an enumerator
      match vals.idxOf? m with
      | some k => return ⟨.lit (.int k), .enum n⟩
      | none => eerr p s!"enum {n} has no value '{m}'"
    | _, _ => elabMember ctx p (← elabE ctx (.ident p n) none) m exp
  | .member p e m => elabMember ctx p (← elabE ctx e none) m exp
  | .construct p name targs args => elabConstruct ctx p name targs args exp
  | .mapLit p entries => elabMapLit ctx p entries exp
  | .structDef p _ _ | .enumDef p _ _ | .refineDef p _ _ _ => eerr p "struct, enum and type definitions must be at the top level"
  | .query p e =>
    let r ← elabE ctx e none
    match r.ty with
    | .opt t => return ⟨.prim .query [r.e], t⟩
    | .logic => return ⟨.prim .query [r.e], .logic⟩
    | t => eerr p s!"'?' needs an option or logic, found {t.show}"
  | .neg p e =>
    -- (the expected type, a float or an int, as a hint: `-Id(2.5)`)
    let hint : Option Ty := match exp with
      | some .float => some .float
      | _ => none
    let r0 ← elabE ctx e hint
    let r := widenR ctx.types r0
    -- (the negation of a refined value is of an expected refinement whose
    -- interval holds the flipped one, #143)
    if let (.refine n, some (.refine m)) := (r0.ty, exp) then
      if let (some (bn, cn), some (bm, cm)) := (ctx.types.refines.lookup n, ctx.types.refines.lookup m) then
        if bn == bm && intervalWithin (intervalNeg (refineInterval cn)) (refineInterval cm) then
          return ⟨.prim (if bn == .float then .fneg else .neg) [r.e], .refine m⟩
    if r.ty == .float then return litAt ctx.types exp ⟨.prim .fneg [r.e], .float⟩
    if r.ty != .int then eerr p s!"unary '-' needs an int or a float, found {r.ty.show}"
    return litAt ctx.types exp ⟨.prim .neg [r.e], .int⟩
  | .notE _ e =>
    -- (with a choice, its first success, #208)
    let e := (Choice.takeFirst? e).getD e
    let r ← elabE { ctx with canFail := true, inTaking := true } e none
    return ⟨Expr.notE r.e, .void⟩
  | .bin p "/" a b =>
    -- `X / Y` on ints: a rational, failing when `Y = 0` (#116)
    let ra := widenR ctx.types (← elabE ctx a none)
    let rb := widenR ctx.types (← elabE ctx b (if ra.ty == .float then some .float else none))
    -- (on floats, IEEE division: by zero an infinity or NaN, #127)
    if ra.ty == .float && rb.ty == .float then return ⟨p2 .fdiv ra.e rb.e, .float⟩
    if ra.ty == .float || rb.ty == .float then
      eerr p s!"no operator '/' for {ra.ty.show} and {rb.ty.show} (an int is not a float: write X * 1.0)"
    if ra.ty == .rational || rb.ty == .rational then
      eerr p "'/' divides ints: openverse has no arithmetic on rationals (only Floor, Ceil and comparisons)"
    let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
    return ⟨← ratCall ctx p "$ratMake" es, .rational⟩
  | .bin p op a b =>
    let ra := widenR ctx.types (← elabE ctx a none)
    let rb ← match op, ra.ty with
      | "+", .arr _ =>
        -- (an array of other classes, to join, #67)
        if ctx.retries ≥ 3 then elabE ctx b (some ra.ty)
        else
          let c2 := { ctx with retries := ctx.retries + 1 }
          tryCatch (elabE c2 b (some ra.ty)) fun _ => elabE c2 b none
      | "*", .int | "*", .float =>
        -- (an int times a float, either way round: `2 * Id(1.5)`)
        if ctx.retries ≥ 3 then elabE ctx b (some ra.ty)
        else
          let c2 := { ctx with retries := ctx.retries + 1 }
          tryCatch (elabE c2 b (some ra.ty)) fun _ => elabE c2 b none
      | _, _ => elabE ctx b (some ra.ty)
    let rb := widenR ctx.types rb
    match op, ra.ty, rb.ty with
    | "+", .int, .int => return ⟨p2 .add ra.e rb.e, .int⟩
    | "-", .int, .int => return ⟨p2 .sub ra.e rb.e, .int⟩
    | "*", .int, .int => return ⟨p2 .mul ra.e rb.e, .int⟩
    -- floats (#127): no implicit int to float, except in `*` (`Count * 1.0`)
    | "+", .float, .float => return ⟨p2 .fadd ra.e rb.e, .float⟩
    | "-", .float, .float => return ⟨p2 .fsub ra.e rb.e, .float⟩
    | "*", .float, .float => return ⟨p2 .fmul ra.e rb.e, .float⟩
    | "*", .int, .float => return ⟨p2 .fmul (.prim .fofInt [ra.e]) rb.e, .float⟩
    | "*", .float, .int => return ⟨p2 .fmul ra.e (.prim .fofInt [rb.e]), .float⟩
    | "+", .arr t, .arr u =>
      if t == u then return ⟨p2 .concat ra.e rb.e, .arr t⟩
      -- arrays of classes concatenate at a common supertype (#32)
      match joinTy (← get).env (.arr t) (.arr u) exp with
      | some jt => return ⟨p2 .concat (← coerce p ra jt) (← coerce p rb jt), jt⟩
      | none => eerr p s!"cannot concatenate {ra.ty.show} and {rb.ty.show}"
    | _, ta, tb => eerr p s!"no operator '{op}' for {ta.show} and {tb.show}"
  | .cmp p a rest => elabCmp ctx p a rest
  | .andE _ a b =>
    -- each operand is its own scope: names defined in `a` are not visible in
    -- `b`, and names from either side do not escape the `and`
    let (ra, _) ← elabStmt ctx a none
    let (rb, _) ← elabStmt ctx b exp
    return ⟨Expr.andE ra.e rb.e, rb.ty⟩
  | .orE p a b =>
    let a := (Choice.takeFirst? a).getD a
    let ra ← elabE { ctx with canFail := true, inTaking := true } a exp
    let rb ← match exp with
      | some _ => elabE ctx b exp
      | none =>
        if ctx.retries ≥ 3 then elabE ctx b (some ra.ty)
        else
          let c2 := { ctx with retries := ctx.retries + 1 }
          tryCatch (elabE c2 b (some ra.ty)) fun _ => elabE c2 b none
    let ty ← join p ra.ty rb.ty exp
    let t ← fresh ty
    return ⟨Expr.orE t (← coerce p ra ty) (← coerce p rb ty), ty⟩
  | .range p _ _ => eerr p "a range a..b can only be the source of a for clause"
  | .tuple _ [] => return ⟨.lit .void, .void⟩
  | .tuple _ es =>
    let exps : List (Option Ty) := match exp with
      | some (.tup ts) => if ts.length == es.length then ts.map some else es.map fun _ => none
      -- (a tuple where an array is expected becomes one: its elements at
      -- the element type)
      | some (.arr t) => es.map fun _ => some t
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
      | some t => return ⟨.lit (.arr #[]), .arr t⟩
      | none => eerr p "the type of an empty array{} must be given (e.g. X:[]int = array{})"
    | e :: rest =>
      let r ← elabE ctx e elemExp
      let t := elemExp.getD r.ty
      let rs ← rest.mapM fun e' => elabE ctx e' (some t)
      let all := (e :: rest).zip (r :: rs)
      -- the expected element type (or the first's), when every element
      -- converts to it; else the join of their types (classes at a common
      -- supertype, #67), with no element elaborated again
      match ← tryCatch (some <$> all.mapM fun (e', x) => coerce e'.pos x t) (fun _ => pure none) with
      | some es => return ⟨.prim .mkArr es, .arr t⟩
      | none =>
        let jt ← (rest.zip rs).foldlM (fun acc ((e', x) : SExpr × R) => do
            match joinTy (← get).env acc x.ty elemExp with
            | some j => pure j
            | none =>
              if (elemExp.isNone || elemExp == some .any) && !ambiguousJoin (← get).env acc x.ty then
                pure .any
              else eerr e'.pos s!"the elements of this array have different types: {acc.show} and {x.ty.show}") r.ty
        let es ← all.mapM fun (e', x) => coerce e'.pos x jt
        return ⟨.prim .mkArr es, .arr jt⟩
  | .optionLit _ e =>
    let e := (Choice.takeFirst? e).getD e
    let inner : Option Ty := match exp with
      | some (.opt t) => some t
      | _ => none
    let r ← elabE { ctx with canFail := true, inTaking := true } e inner
    -- an expression that cannot fail needs no failure context (and no
    -- saved state to roll back to: the interpreter's heap is not copied)
    if !(r.e.mayFail ctx.sigProg) then return ⟨.prim .mkSome [r.e], .opt r.ty⟩
    let t ← fresh r.ty
    return ⟨Expr.optionE t r.e, .opt r.ty⟩
  | .logicLit p e =>
    let e := (Choice.takeFirst? e).getD e
    let r ← elabE { ctx with canFail := true, inTaking := true } e none
    if !(r.e.mayFail ctx.sigProg) && (← get).fnNeeds.isEmpty then eerr p "logic{…} needs an expression that can fail"
    return ⟨Expr.logicE r.e, .logic⟩
  | .ite p conds thenE elseE =>
    -- (a cast that refines type arguments, as the whole condition, #243)
    if let [.decl dp d none false (.app _ (.ident _ T) [x] true)] := conds then
      match ← elabRefinedIf ctx p dp d T x thenE elseE exp with
      | some r => return r
      | none => pure ()
    let (rc, ctxT) ← if Choice.hasChoice conds then elabOneClauses { ctx with canFail := true } conds
      else elabSeq { ctx with canFail := true, inTaking := true } conds none
    -- (not while a function value is asked for, #214, #231: a call through
    -- it may fail once its class is made, in the elaboration that follows)
    if !(rc.e.mayFail ctx.sigProg) && (← get).fnNeeds.isEmpty then
      eerr p "the condition of this if cannot fail (Verse requires a failable condition)"
    let thenCtx := { ctxT with canFail := ctx.canFail, inTaking := ctx.inTaking }
    match elseE with
    | none =>
      let rt ← elabE thenCtx thenE (some .void)
      return ⟨.ite rc.e (← coerce p rt .void) (.lit .void), .void⟩
    | some ee =>
      let rt ← elabE thenCtx thenE exp
      -- the else branch against the then branch's type (for `array{}`,
      -- `false`), else on its own, to join with it (#32)
      let re ← match exp with
        | some _ => elabE ctx ee exp
        | none =>
          if ctx.retries ≥ 3 then elabE ctx ee (some rt.ty)
          else
            let c2 := { ctx with retries := ctx.retries + 1 }
            tryCatch (elabE c2 ee (some rt.ty)) fun _ => elabE c2 ee none
      let ty ← join p rt.ty re.ty exp
      return ⟨.ite rc.e (← coerce p rt ty) (← coerce p re ty), ty⟩
  | .forE p clauses body => elabFor ctx p clauses body
  | .gen p _ _ _ => eerr p "a generator X : source can only appear in a for clause"
  | .loop _ body =>
    let lctx := { ctx with inLoop := true, inRepeat := true, loopDefers := ctx.defers.length, inChoice := false }
    let r ← elabE lctx body none
    return ⟨.loop r.e, .void⟩
  | .brk p =>
    if ctx.inChoice then
      eerr p "break cannot leave the clauses of a failure context that has a choice (an if condition, first{…}, option{…}, …) (#208)"
    if !ctx.inLoop then
      eerr p (if ctx.inDefer then "break is only allowed inside loop (not for), and cannot leave a defer: block"
              else "break is only allowed inside loop (not for)")
    -- the defers of the scopes it leaves, inside its loop
    let ds ← elabDefers ctx (ctx.defers.take (ctx.defers.length - ctx.loopDefers))
    return ⟨.seq ds .brk, .never⟩
  | .ret p none =>
    if ctx.inParamDefault then eerr p "return is not allowed in a parameter's default"
    if ctx.inDefer then eerr p "return is not allowed in a defer: block"
    if ctx.inCtor then eerr p "return is not allowed in a constructor (it would skip the items after it)"
    if ctx.inBlock then eerr p "return is not allowed in a block: clause (it would skip the clauses after it)"
    if ctx.inBranch then eerr p "return is not allowed in a branch (Book of Verse ch. 14)"
    if ctx.retTy != .void then eerr p s!"return needs a value of type {ctx.retTy.show}"
    return ⟨.seq (← elabDefers ctx ctx.defers) (.ret (.lit .void)), .never⟩
  | .ret p (some e) =>
    if ctx.inParamDefault then eerr p "return is not allowed in a parameter's default"
    if ctx.inDefer then eerr p "return is not allowed in a defer: block"
    if ctx.inCtor then eerr p "return is not allowed in a constructor (it would skip the items after it)"
    if ctx.inBlock then eerr p "return is not allowed in a block: clause (it would skip the clauses after it)"
    if ctx.inBranch then eerr p "return is not allowed in a branch (Book of Verse ch. 14)"
    let r ← elabE ctx e (some ctx.retTy)
    let v ← coerce p r ctx.retTy
    if ctx.defers.isEmpty then return ⟨.ret v, .never⟩
    -- the value first, then the defers of every scope it leaves
    let t ← fresh ctx.retTy
    return ⟨.seq (.assign t v) (.seq (← elabDefers ctx ctx.defers) (.ret (.local t))), .never⟩
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
      if let .app dp (.ident _ "$defer") _ _ := rhs then eerr dp "defer: is a statement: it has no value"
      checkNewLocal ctx p n
      let ty? ← sty.mapM (resolveTy ctx.types p)
      let r ← elabE ctx rhs ty?
      let ty := ty?.getD r.ty
      if ty == .never then
        eerr p (if n.startsWith "$" then "cannot infer the type of this clause's value" else s!"cannot infer the type of '{n}'")
      let e ← coerce p r ty
      let slot ← fresh ty
      pure (⟨.assign slot e, ty⟩,
        { ctx with locals := { name := n, slot, ty, mutable := isVar } :: ctx.locals })
    | _ => do pure (← elabE ctx se exp, ctx)
  if !ctx.canFail && (r.e.mayFail ctx.sigProg) then
    eerr se.pos ("this expression can fail, but it is not in a failure context (an if " ++
      "condition, a for clause, option{…}, logic{…}, not, the left of or, or a <decides> function)")
  return (r, ctx')

/-- `defer:` bodies, run in order (innermost first): each cannot fail, return
    or break out of itself, and sees the locals in scope where it is
    registered (Verse has no shadowing, so those at an exit include them). -/
partial def elabDefers (ctx : Ctx) (ds : List (SExpr × List Local)) : EM Expr := do
  elabDefersCore ctx ds

/-- A suspension point with the code of the `defer:` blocks active there, in
    a branch that never runs (`if (false) …`), for the lowering's
    cancellation (#156): the defers run when a cancelled task unwinds. -/
partial def withDeferMark (ctx : Ctx) (e : Expr) : EM Expr := do
  if ctx.defers.isEmpty then return e
  return .seq (.ite (.prim .fail []) (← elabDefersCore ctx ctx.defers) (.lit .void)) e

/-- `sync:` (`isSync`) or `race:` with arms `arms` (#156): each arm's value
    goes to a slot (`race`: one slot of the arms' join type, written by the
    winner), and the arms to the marker `$syncMark(array{…})` (or
    `$raceMark`), which the lowering (`Suspend.lean`) runs concurrently. -/
partial def elabConc (ctx : Ctx) (p : Pos) (isSync : Bool) (arms : List SExpr) (exp : Option Ty)
    (isRush : Bool := false) : EM R := do
  let kw := if isSync then "sync" else if isRush then "rush" else "race"
  if !ctx.suspends then eerr p s!"{kw} suspends: it can only be used in a <suspends> function (#156)"
  if ctx.inDefer then eerr p s!"{kw} suspends, and a defer cannot suspend (#156)"
  if ctx.canFail then eerr p s!"{kw} suspends, and a failure context (a condition, a filter, or a <decides> call's arguments) cannot (#156)"
  if isRush && ctx.inRepeat then
    eerr p "rush cannot be in a loop or for body (Book of Verse ch. 14): call a function that rushes"
  let some mark := ctx.sig? (if isSync then "$syncMark" else if isRush then "$rushMark" else "$raceMark")
    | eerr p s!"internal error: no {kw} helper"
  -- (an arm is a scope of its own: its defers are its own, and break and
  -- return cannot leave it)
  let armCtx := { ctx with defers := [], loopDefers := 0, inLoop := false, inArm := true }
  let isS : Nat → Bool := fun f => ctx.sigs.any fun s => s.idx == f && s.suspends
  if isSync then
    let mut stmts : Array Expr := #[]
    let mut slots : Array Nat := #[]
    let mut tys : Array Ty := #[]
    let mut async := 0
    -- (an expected tuple type gives each arm its expected type)
    let armExp : List (Option Ty) := match exp with
      | some (.tup ts) => if ts.length == arms.length then ts.map some else arms.map fun _ => none
      | _ => arms.map fun _ => none
    for (a, ae) in arms.zip armExp do
      let r ← elabE armCtx a ae
      let r ← match ae with
        | some t => pure ⟨← coerce a.pos r t, t⟩
        | none => pure r
      -- (a spawn or a branch in an arm does not make it wait)
      let skip : Nat → Bool := fun f => ctx.sigs.any fun s => s.idx == f && (s.name == "$spawnMark" || s.name == "$branchMark")
      if Suspend.countSusp isS (fun _ => false) false skip r.e > 0 then async := async + 1
      let ty := if r.ty == .never then Ty.void else r.ty
      let t ← fresh ty
      stmts := stmts.push (.seq (.assign t r.e) (.lit .void))
      slots := slots.push t
      tys := tys.push ty
    if async < 2 then
      eerr p "sync needs at least two arms that can suspend (Book of Verse ch. 14): write the others in sequence"
    let e := Expr.seq (.call mark.idx [.prim .mkArr stmts.toList]) (.prim .mkTup (slots.toList.map Expr.local))
    return ⟨← withDeferMark ctx e, .tup tys.toList⟩
  else
    if arms.length < 2 then eerr p s!"{kw} needs at least two arms"
    -- the arms' join, as an `if`'s branches (or the expected type)
    let mut rs : Array (Pos × R) := #[]
    for a in arms do
      rs := rs.push (a.pos, ← elabE armCtx a exp)
    -- (as an `if`'s branches: void when one is, `any` when nothing else is
    -- common)
    let mut ty : Ty := .never
    for (_, r) in rs.toList do
      ty ← join p ty r.ty exp
    let rty := match exp with
      | some t => t
      | none => ty
    let t ← fresh rty
    let mut stmts : Array Expr := #[]
    for (ap, r) in rs do
      stmts := stmts.push (.seq (.assign t (← coerce ap r rty)) (.lit .void))
    let e := Expr.seq (.call mark.idx [.prim .mkArr stmts.toList]) (.local t)
    return ⟨← withDeferMark ctx e, rty⟩

/-- `spawn{F(…)}` (#156): a new task running the call, which must be of a
    `<suspends>` function; its arguments are evaluated now. The value is
    the task, a `task(t)`. The lowering (`Suspend.lean`) turns the marker
    `$spawnMark(array{F(…), T})` into a new task root. -/
partial def elabSpawn (ctx : Ctx) (p : Pos) (body : SExpr) : EM R := do
  if ctx.inDefer then eerr p "spawn in a defer is not supported (#156)"
  if ctx.canFail && !ctx.inDefaultCheck then
    eerr p "spawn cannot be in a failure context (a condition, a filter, or a <decides> call's arguments) (#156)"
  let some mark := ctx.sig? "$spawnMark" | eerr p "internal error: no spawn helper"
  let call := match body with
    | .block _ [e] => e
    | e => e
  -- (the call runs in the new task, which may wait, also when spawned from
  -- an immediate function; its arguments may not)
  let r ← elabE { ctx with defers := [], suspends := true, canFail := false } call none
  let isS : Nat → Bool := fun f => ctx.sigs.any fun s => s.idx == f && s.suspends
  let e := match r.e with
    | .seq (.ite (.prim .fail []) _ (.lit .void)) e => e
    | e => e
  -- (statements before the call, such as a method call's receiver, run
  -- now, as the arguments are evaluated)
  -- (a method with several implementations: the dispatch on the
  -- receiver's class, a chain of tests that the lowering makes a function
  -- of the slots it uses, #173)
  let rec peel : Expr → Option (List Expr × Expr)
    | .call g es => some ([], .call g es)
    | .seq a b => (peel b).map fun (ps, c) => (a :: ps, c)
    | e@(.ite ..) => if Suspend.isDispatchChain e then some ([], e) else none
    -- (one refined by #142, through a temporary of the result type)
    | .assign _ e@(.ite ..) => if Suspend.isDispatchChain e then some ([], e) else none
    | _ => none
  let some (pre, callE) := peel e
    | eerr p "spawn{…} takes one call of a <suspends> function or method, with its arguments (#156)"
  let (ok, es) := match callE with
    | .call g es => (isS g, es)
    -- (each implementation the dispatch runs, with its own defaults)
    | ch => ((Suspend.chainArms ch).all fun a => (Suspend.callsOf a).any (isS ·.1), [])
  if !ok then eerr p "spawn{…} takes a call of a <suspends> function (#156)"
  -- (a spawn among them does not wait)
  if (pre ++ es).any (fun x => Suspend.countSusp isS (fun _ => false) false (· == mark.idx) x > 0) then
    eerr p "the arguments of a spawned call cannot suspend (#156)"
  let ty : Ty := .struct "task" [r.ty]
  let tagT := ctx.types.tagOf "task"
  let t ← fresh ty
  -- (its fields: the done flag `false`, the others empty options)
  let fieldVals := (ctx.types.fields "task" [r.ty]).map fun (_, ft, _) =>
    if ft == .logic then Expr.lit (.logic false) else Expr.lit .none
  let spawnE : Expr := .seq (.assign t (.heap (.new tagT) fieldVals))
    (.seq (.call mark.idx [.prim .mkArr [.seq callE (.lit .void), .seq (.local t) (.lit .void)]]) (.local t))
  return ⟨pre.foldr Expr.seq spawnE, ty⟩

/-- `branch:` (#156): its body runs as a background task over the enclosing
    function's frame, at once up to its first wait, and is cancelled when
    the function exits. The lowering (`Suspend.lean`) turns the marker
    `$branchMark(array{body})` into an arm run as a task root. -/
partial def elabBranch (ctx : Ctx) (p : Pos) (body : SExpr) : EM R := do
  if !ctx.suspends then eerr p "branch suspends: it can only be used in a <suspends> function (#156)"
  if ctx.inDefer then eerr p "branch in a defer is not supported (#156)"
  if ctx.canFail then eerr p "branch cannot be in a failure context (a condition, a filter, or a <decides> call's arguments) (#156)"
  if ctx.inRepeat then eerr p "branch cannot be in a loop or for body (Book of Verse ch. 14): call a function that branches"
  let some mark := ctx.sig? "$branchMark" | eerr p "internal error: no branch helper"
  let armCtx := { ctx with defers := [], loopDefers := 0, inLoop := false, inArm := true, inBranch := true }
  let r ← elabE armCtx body none
  return ⟨.call mark.idx [.prim .mkArr [.seq r.e (.lit .void)]], .void⟩

partial def elabDefersCore (ctx : Ctx) (ds : List (SExpr × List Local)) : EM Expr := do
  let mut acc : Expr := .lit .void
  for (d, locs) in ds.reverse do
    -- (with the locals where it was registered: their slots still hold them)
    let dctx := { ctx with canFail := false, inDefer := true, inLoop := false, defers := [], loopDefers := 0,
                           locals := locs }
    let r ← elabE dctx d none
    acc := .seq r.e acc
  return acc

/-- A call of an overloaded function or method (#74): the one overload
    (`ovs`, each with its signature `sigOf`, a method's without `Self`) the
    call's shape and arguments fit, then `call` it. -/
partial def resolveOverload (ctx : Ctx) (p : Pos) (name : String) (ovs : List String)
    (sigOf : String → Option Sig) (call : String → EM R) (args : List SExpr) : EM R := do
  -- an overloaded function (#74): the one overload whose parameters the
  -- arguments fit (each elaborated at the parameter's type, in a trial)
  -- the overloads the call's shape fits: as many positional arguments, and
  -- named ones the overload has, every one it needs given
  let isNamedArg : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  let posArgs := args.filter (!isNamedArg ·)
  let namedArgs : List (String × SExpr) := args.filterMap fun
    | .decl _ n _ _ rhs => if n.startsWith "?" then some ((n.drop 1).toString, rhs) else none
    | _ => none
  let fitsShape (s : Sig) : Bool :=
    posArgs.length == s.params.length - s.named.length &&
    namedArgs.all (fun (g, _) => s.named.any (·.1 == g)) &&
    s.named.all fun (n, d) => d.isSome || namedArgs.any (·.1 == n)
  -- each argument expression with the type of its parameter in `s`
  let argTys (s : Sig) : List (SExpr × Ty) :=
    let npos := s.params.length - s.named.length
    (posArgs.zip (s.params.take npos)) ++ namedArgs.filterMap fun (n, rhs) =>
      (s.named.findIdx? (·.1 == n)).map fun j => (rhs, (s.params.drop npos).getD j .void)
  let cands := ovs.filter fun o => ((sigOf o).map fitsShape).getD false
  -- each argument's type alone, once (none: it needs an expected type)
  let natTy (a : SExpr) : EM (Option Ty) := do
    -- (by position and shallow shape: a wrong hit could only make the
    -- call below fail to elaborate, never take an overload the arguments
    -- do not fit, as no call fits two)
    let shape : String := match a with
      | .app _ (.ident _ f) as b => s!"app {f} {as.length} {b}"
      | .ident _ n => s!"id {n}"
      | .int _ v => s!"int {v}"
      | .member _ _ m => s!"mem {m}"
      | .construct _ n _ fs => s!"new {n} {fs.length}"
      | .tuple _ es => s!"tup {es.length}"
      | .arrayLit _ es => s!"arr {es.length}"
      | .bin _ o _ _ => s!"bin {o}"
      | _ => "_"
    let key := s!"{a.pos.line}:{a.pos.col}:{a.pos.file}:{shape}"
    if let some r := (← get).natTys[key]? then return r
    let st ← get
    let r ← tryCatch (do return some (← elabE ctx a none).ty) (fun _ => pure none)
    let cache := (← get).natTys
    set { st with natTys := cache.insert key r }
    return r
  let coercible (t u : Ty) : EM Bool := do
    let st ← get
    let ok ← tryCatch (do discard <| coerce p ⟨.lit .void, t⟩ u; pure true) (fun _ => pure false)
    set { st with natTys := (← get).natTys }
    return ok
  let mut byNat : List String := []
  for o in cands do
    let some so := sigOf o | continue
    let mut ok := true
    if cands.length > 1 then
      -- (a generic one's patterns, by the matching that infers its type
      -- arguments: no whole-call trial at every level of a nested call)
      let mut σ : List (String × Ty) := []
      for (a, u) in argTys so do
        if let some t ← natTy a then
          if so.tparams.isEmpty then
            if !(← coercible t u) then ok := false
          else match u.matchArg ctx.types σ t with
            | some σ' => σ := σ'
            | none =>
              -- (against nothing bound: the pattern cannot take it; a
              -- conflict with earlier bindings only may be a subtype the
              -- call reconciles, so the candidate stays for the trial)
              if (u.matchArg ctx.types [] t).isNone && !(← coercible t u) then ok := false
    if ok then byNat := byNat ++ [o]
  let fits (o : String) : EM Bool := do
    let s := (sigOf o).get!
    let st ← get
    if !s.tparams.isEmpty then
      let ok ← tryCatch (do discard <| call o; pure true) (fun _ => pure false)
      set { st with natTys := (← get).natTys }
      return ok
    let ok ← tryCatch (do
        for (a, t) in argTys s do
          let r ← elabE ctx a (some t)
          discard <| coerce a.pos r t
        pure true) (fun _ => pure false)
    set { st with natTys := (← get).natTys }
    return ok
  -- the overloads the arguments' own types fit, then those the arguments
  -- elaborated at each one's parameter types fit
  let mut ok : List String := []
  if byNat.length == 1 then ok := byNat
  else
    -- (none: an argument's own type can differ from its type at a
    -- parameter, `false` is a logic and also fits `?t`)
    for o in (if byNat.isEmpty then cands else byNat) do
      if ← fits o then ok := ok ++ [o]
  let call' (o : String) : EM R :=
    tryCatch (call o) fun msg => throw (msg.replace o name)
  match ok, cands with
  | [o], _ => call' o
  | [], [o] => call' o   -- its error
  | [], [] =>
    let nm := if namedArgs.isEmpty then "" else s!" and {", ".intercalate (namedArgs.map fun (n, _) => s!"?{n}")}"
    let shown := ovs.filterMap fun o => (sigOf o).map fun so =>
      let npos := so.params.length - so.named.length
      "(" ++ ", ".intercalate ((so.params.take npos).map Ty.show ++
        (so.named.zip (so.params.drop npos)).map fun ((n, d), t) =>
          s!"?{n}:{t.show}" ++ (if d.isSome then " = …" else "")) ++ ")"
    eerr p s!"no overload of {name} fits a call with {posArgs.length} positional argument(s){nm}; its overloads take {" and ".intercalate shown}"
  | [], _ =>
    let st ← get
    let tys ← posArgs.mapM fun a => do return (← elabE ctx a none).ty.show
    let ntys ← namedArgs.mapM fun (n, a) => do return s!"?{n}:{(← elabE ctx a none).ty.show}"
    let tys := tys ++ ntys
    set st
    eerr p s!"no overload of {name} takes ({", ".intercalate tys})"
  | _ :: _ :: _, _ =>
    let shown := ok.map fun o => s!"({", ".intercalate (((sigOf o).map (·.params)).getD [] |>.map Ty.show)})"
    eerr p s!"this call of {name} fits more than one overload: {" and ".intercalate shown}"

/-- A sequence of statements, threading the scope; the value is the last one's. -/
partial def elabSeq (ctx : Ctx) (ss : List SExpr) (exp : Option Ty) : EM (R × Ctx) := do
  match ss with
  | [] => return (⟨.lit .void, .void⟩, ctx)
  | .app p (.ident _ "$defer") [body] false :: rest =>
    -- `defer: D` then the rest of the scope (Book of Verse ch. 7): the rest,
    -- with D pending for its returns and breaks, then D, then the rest's value
    if let .block _ [] := body then eerr p "a defer: block cannot be empty"
    let (r2, ctx2) ← elabSeq { ctx with defers := (body, ctx.locals) :: ctx.defers } rest exp
    let d ← elabDefers ctx [(body, ctx.locals)]
    let ctx2 := { ctx2 with defers := ctx.defers, loopDefers := ctx.loopDefers }
    match r2.ty with
    | .never => return (r2, ctx2)
    | .void => return (⟨.seq r2.e (.seq d (.lit .void)), .void⟩, ctx2)
    | ty =>
      let t ← fresh ty
      return (⟨.seq (.assign t r2.e) (.seq d (.local t)), ty⟩, ctx2)
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

/-- A call. One tuple argument that a call cannot take as it is is expanded
    into several (Book of Verse ch. 3, #140): of a method, an overloaded or a
    generic function as of any other (`elabAppBase` does plain calls). -/
partial def elabApp (ctx : Ctx) (p : Pos) (f : SExpr) (args : List SExpr) (bracket : Bool)
    (exp : Option Ty) : EM R := do
  match args with
  | [a] =>
    -- (nested retries are bounded: each level elaborates its argument again)
    if ctx.retries ≥ 8 then return ← elabAppBase ctx p f args bracket exp
    let saved ← get
    -- (the state is restored between attempts, but not the overload cache)
    let restore : EM Unit := do set { saved with natTys := (← get).natTys }
    tryCatch (elabAppBase ctx p f args bracket exp) fun err => do
      -- (only a call refused for its arguments' shape is tried again: an
      -- error from inside the argument is the argument's)
      let shapeErr := ["argument(s)", "overload", "expected tuple"].any fun k => (err.splitOn k).length > 1
      if !shapeErr then throw err
      restore
      let c2 := { ctx with retries := ctx.retries + 1 }
      -- a method's receiver is evaluated first, then the tuple
      let (pre, c2, f') ← match f with
        | .member mp obj m =>
          if (match obj with | .ident _ "(super:)" => true | _ => false) then pure ([], c2, f) else
          match ← tryCatch (some <$> elabE c2 obj none) (fun _ => pure none) with
          | some ro =>
            let to ← fresh ro.ty
            let nm := s!"$receiver{to}"
            pure ([Expr.assign to ro.e],
              { c2 with locals := { name := nm, slot := to, ty := ro.ty, mutable := false } :: c2.locals },
              SExpr.member mp (.ident mp nm) m)
          | none => pure ([], c2, f)
        | _ => pure ([], c2, f)
      match ← tryCatch (some <$> elabE c2 a none) (fun _ => pure none) with
      | some ⟨e, .tup ts⟩ =>
        if ts.length < 2 then restore; throw err
        let tt ← fresh (.tup ts)
        let nm := s!"$tuple{tt}"
        let c3 := { c2 with locals := { name := nm, slot := tt, ty := .tup ts, mutable := false } :: c2.locals }
        let parts := (List.range ts.length).map fun (i : Nat) => SExpr.app a.pos (.ident a.pos nm) [.int a.pos (i : Int)] false
        match ← tryCatch (some <$> elabAppBase c3 p f' parts bracket exp) (fun _ => pure none) with
        | some r => return ⟨(pre ++ [Expr.assign tt e]).foldr Expr.seq r.e, r.ty⟩
        | none => restore; throw err
      | _ => restore; throw err
  | _ => elabAppBase ctx p f args bracket exp

partial def elabAppBase (ctx : Ctx) (p : Pos) (f : SExpr) (args : List SExpr) (bracket : Bool)
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
          ((ctx.types.methodOverloads.lookup name).map (·.any (ctx.hasMethod c ·))).getD false ||
          ((ctx.types.fields c).any (·.1 == name) && !builtins.contains name && !softBuiltins.contains name)
      | none => false
    if selfMember? then elabApp ctx p (.member p (.ident p "Self") name) args bracket exp else
    -- `T[X]`, `T(X)`: a cast to class or interface `T`
    if ctx.types.classes.contains name && (ctx.sig? name).isNone then elabCast ctx p name args bracket else
    if let some (base, conds) := ctx.types.refines.lookup name then
      -- `age[X]` (#136): `X`, if it meets the conditions; failing otherwise
      if !bracket then eerr p s!"a cast to {name} can fail: write {name}[X]"
      let [a] := args | eerr p s!"a cast to {name} takes one value"
      let r ← elabE ctx a (some base)
      let r := widenR ctx.types r
      if r.ty != base then eerr p s!"a cast to {name} takes {withArticle base.show}, found {r.ty.show}"
      let tv ← fresh base
      let isF := base == .float
      let test (c : String × Value) : Expr :=
        let op : Prim := match c.1, isF with
          | "<", false => .lt | "<=", false => .le | ">", false => .gt | _, false => .ge
          | "<", true => .flt | "<=", true => .fle | ">", true => .fgt | _, true => .fge
        p2 op (.local tv) (.lit c.2)
      let checks := conds.foldr (fun c acc => Expr.seq (test c) acc) (.local tv)
      return ⟨.seq (.assign tv r.e) checks, .refine name⟩
    else
    if let some ovs := ctx.types.overloads.lookup name then
      resolveOverload ctx p name ovs ctx.sig? (fun o => elabApp ctx p (.ident p o) args bracket exp) args
    else
    -- (a soft built-in the program defines is the program's)
    let builtinName := if (softBuiltins.contains name || name == "any") && (ctx.sig? name).isSome then "$program" else name
    match builtinName with
    | "Concatenate" =>
      -- (#150) an array of arrays flattened, or several arrays one after
      -- the other (as a tuple of them converts to an array of arrays)
      match args with
      | [] => match exp with
        | some (.arr t) => return ⟨.lit (.arr #[]), .arr t⟩
        | _ => eerr p "Concatenate() needs an expected array type"
      | [a] =>
        let r ← elabE ctx a (match exp with | some t => some (.arr t) | none => none)
        match r.ty with
        | .arr (.arr t) =>
          -- (through a typed temporary: an empty literal has no type of its own)
          let tv ← fresh r.ty
          return ⟨.seq (.assign tv r.e) (.prim .flatten [.local tv]), .arr t⟩
        | t => eerr p s!"Concatenate takes arrays, or an array of arrays, found {t.show}"
      | a :: rest =>
        let r0 ← elabE ctx a exp
        let .arr t := r0.ty | eerr a.pos s!"Concatenate takes arrays, found {r0.ty.show}"
        let mut acc := r0.e
        for b in rest do
          let rb ← elabE ctx b (some (.arr t))
          acc := p2 .concat acc (← coerce b.pos rb (.arr t))
        return ⟨acc, .arr t⟩
    | "any" =>
      -- `any(X)`: X as an `any` (#138), evaluated
      let [a] := args | eerr p "any(…) takes one value"
      let r ← elabE ctx a none
      return ⟨← coerce a.pos r .any, .any⟩
    | "Print" =>
      let es ← elabArgs ctx p args [Ty.string]
      return ⟨.print es.head!, .void⟩
    | "ConcatenateMaps" =>
      -- the entries of every map, a later map's value winning for a key (Book
      -- of Verse ch. 9): the first copied, then each other's pairs put in turn
      let some a0 := args.head? | eerr p "ConcatenateMaps takes at least one map"
      -- the maps' type: the expected one, else the first argument's that has
      -- one alone (an empty map{} has none)
      let mapExp : Option Ty ← match exp with
        | some t@(.map ..) => pure (some t)
        | _ =>
          let st ← get
          let mut found : Option Ty := none
          for a in args do
            if found.isNone then
              found ← tryCatch (do let r ← elabE ctx a none; pure (match r.ty with | t@(.map ..) => some t | _ => none))
                (fun _ => pure none)
          set st
          pure found
      let mut rs : Array R := #[]
      let mut jt? : Option Ty := none
      for a in args do
        let r ← elabE ctx a mapExp
        let .map _ _ := r.ty | eerr a.pos s!"ConcatenateMaps takes maps, not {r.ty.show}"
        match jt? with
        | none => jt? := some r.ty
        | some j =>
          let j' ← tryCatch (join a.pos j r.ty mapExp) (fun _ =>
            eerr a.pos s!"ConcatenateMaps takes maps of one type, not {j.show} and {r.ty.show}")
          jt? := some j'
        rs := rs.push r
      let some jt := jt? | eerr p "ConcatenateMaps takes at least one map"
      let .map kt vt := jt | eerr p s!"ConcatenateMaps takes maps, not {jt.show}"
      let tm ← fresh jt
      let some r0 := rs[0]? | eerr p "ConcatenateMaps takes at least one map"
      let mut code : Expr := .assign tm (← coerce a0.pos r0 jt)
      for (r, a) in rs.toList.tail.zip args.tail do
        let ts ← fresh jt
        let tpair ← fresh (.tup [kt, vt])
        let tk ← fresh kt
        let tv ← fresh vt
        let ti ← fresh .int
        let tidx ← fresh .int
        let put := Expr.seq (.assign tk (.prim (.tupGet 0) [.local tpair]))
          (.seq (.assign tv (.prim (.tupGet 1) [.local tpair])) (mapPut tm tk tv ti tidx))
        code := .seq code (.seq (.assign ts (← coerce a.pos r jt)) (.forE tpair (.local ts) (.lit (.logic true)) put))
      return ⟨.seq code (.local tm), jt⟩
    | "ToString" =>
      match args with
      | [a] => return ⟨← toStringOf p (← elabE ctx a none), Ty.string⟩
      | _ => eerr p "ToString takes one argument"
    | "Abs" =>
      -- (of a float, #127; each argument elaborated once)
      match args with
      | [a] =>
        let r ← elabE ctx a none
        if r.ty == .float then return ⟨.prim .fabs [r.e], .float⟩
        return ⟨.prim .abs [← coerce a.pos r .int], .int⟩
      | _ => eerr p "Abs takes one argument"
    | "Sqrt" | "Exp" | "Ln" | "Log" | "Pow" | "Sin" | "Cos" | "Tan" | "ArcSin" | "ArcCos" | "ArcTan"
    | "IsFinite" =>
      -- the mathematical functions of floats (#132); only IsFinite fails
      if name == "IsFinite" then needBracket name
      else if bracket then eerr p s!"{name} cannot fail: call it with {name}(…)"
      let fl (a : SExpr) : EM Expr := do
        let r := widenR ctx.types (← elabE ctx a (some .float))
        if r.ty != .float then eerr a.pos s!"{name} takes floats, found {r.ty.show}"
        return r.e
      let unary : String → Option Prim
        | "Sqrt" => some .fsqrt | "Exp" => some .fexp | "Ln" => some .fln | "Sin" => some .fsin
        | "Cos" => some .fcos | "Tan" => some .ftan | "ArcSin" => some .fasin | "ArcCos" => some .facos
        | "ArcTan" => some .fatan | "IsFinite" => some .fisFinite
        | _ => none
      match name, args with
      | "Pow", [a, b] => return ⟨p2 .fpow (← fl a) (← fl b), .float⟩
      | "ArcTan", [y, x] => return ⟨p2 .fatan2 (← fl y) (← fl x), .float⟩
      | "Log", [b, x] =>
        -- (`Log(Base, X)` is `Ln(X) / Ln(Base)`, the base evaluated first)
        let tb ← fresh .float
        let eb ← fl b
        let ex ← fl x
        return ⟨.seq (.assign tb eb) (p2 .fdiv (.prim .fln [ex]) (.prim .fln [.local tb])), .float⟩
      | n, [a] =>
        match unary n with
        | some op => return ⟨.prim op [← fl a], .float⟩
        | none => eerr p s!"{name} takes two floats"
      | _, _ => eerr p s!"{name} takes {if name == "Pow" || name == "Log" then "two floats" else if name == "ArcTan" then "one or two floats" else "one float"}"
    | "Round" | "Int" =>
      -- a float to an int (#127): `Round` ties to even, `Int` towards zero;
      -- failing on NaN, an infinity or out of range
      needBracket name
      match args with
      | [a] =>
        let r := widenR ctx.types (← elabE ctx a (some .float))
        if r.ty != .float then eerr p s!"{name} takes a float, found {r.ty.show}"
        return ⟨.prim (if name == "Round" then .fround else .ftrunc) [r.e], .int⟩
      | _ => eerr p s!"{name} takes one argument"
    | "Floor" | "Ceil" =>
      -- (of a float, #127: failable, so with brackets; of a rational or
      -- an int, with either, as the Book writes both)
      let ofFloat (r : R) : EM R := do
        if !bracket then eerr p s!"{name} of a float can fail: call it with {name}[…]"
        return ⟨.prim (if name == "Floor" then .ffloor else .fceil) [r.e], .int⟩
      match args with
      | [.bin bp "/" a b] =>
        let ra ← elabE ctx a none
        let rb ← elabE ctx b (if ra.ty == .float then some .float else none)
        if ra.ty == .float && rb.ty == .float then return ← ofFloat ⟨p2 .fdiv ra.e rb.e, .float⟩
        if ra.ty == .float || rb.ty == .float then
          eerr bp s!"no operator '/' for {ra.ty.show} and {rb.ty.show} (an int is not a float: write X * 1.0)"
        if ra.ty == .rational || rb.ty == .rational then
          eerr bp "'/' divides ints: openverse has no arithmetic on rationals (only Floor, Ceil and comparisons)"
        let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
        return ⟨.prim (if name == "Floor" then .floorDiv else .ceilDiv) es, .int⟩
      | [e] =>
        -- (of a rational, #116: its denominator is positive, so this never
        -- fails; of an int, the int)
        let r := widenR ctx.types (← elabE ctx e none)
        match r.ty with
        | .int => return r
        | .float => ofFloat r
        | .rational =>
          let tr ← fresh .rational
          let tz ← fresh .int
          let op := if name == "Floor" then Prim.floorDiv else .ceilDiv
          let parts := [Expr.prim (.tupGet 0) [.local tr], .prim (.tupGet 1) [.local tr]]
          return ⟨.seq (.assign tr r.e) (Expr.orE tz (.prim op parts) (.lit (.int 0))), .int⟩
        | t => eerr p s!"{name} takes a rational or an int, found {t.show}"
      | _ => eerr p s!"{name} takes one argument"
    | "Quotient" => needBracket name; return ⟨.prim .quotient (← elabInts ctx p args), .int⟩
    | "Mod" => needBracket name; return ⟨.prim .modulo (← elabInts ctx p args), .int⟩
    | "Min" | "Max" =>
      -- (of floats, #127: NaN when either is)
      -- (each argument elaborated once)
      let [a, b] := args | eerr p s!"{name} takes two arguments"
      let ra ← elabE ctx a none
      let rb ← elabE ctx b (if ra.ty == .float || ra.ty == .int then some ra.ty else none)
      if ra.ty == .float then
        if rb.ty != .float then eerr p s!"{name} takes two floats or two ints, found float and {rb.ty.show}"
        return ⟨p2 (if name == "Min" then .fmin else .fmax) ra.e rb.e, .float⟩
      let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
      let ta ← fresh .int
      let tb ← fresh .int
      let op := if name == "Min" then Prim.le else Prim.ge
      return ⟨.seq (.assign ta es[0]!) (.seq (.assign tb es[1]!)
        (.ite (p2 op (.local ta) (.local tb)) (.local ta) (.local tb))), .int⟩
    | "Err" =>
      modify fun st => if st.errAt.isNone then { st with errAt := some p } else st
      return ⟨.prim .userErr [], .never⟩
    | "$Show" =>
      -- the entry of `openverse run FILE do EXPR`: print the value when it
      -- has a ToString, else just evaluate it
      match args with
      | [a] =>
        let r ← elabE ctx a none
        match r.ty with
        | .int | .char | .float | .arr .char => return ⟨.print (← toStringOf p r), .void⟩
        | _ => return ⟨.seq r.e (.lit .void), .void⟩
      | _ => eerr p "internal: $Show"
    | _ =>
      -- `Sleep` (#156): the concurrency helpers' unless the program has its own
      let name := if name == "Sleep" && (ctx.sig? "Sleep").isNone then "$Sleep" else name
      if name == "$Sleep" && (ctx.sig? name).isNone then
        eerr p "Sleep suspends: it can only be called in a <suspends> function (#156)"
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
          if s.suspends then
            let shown := if name == "$EvAwait" then "Await"
              else if name.startsWith "$" then (name.drop 1).toString else name
            if !ctx.suspends then eerr p s!"{shown} suspends: it can only be called in a <suspends> function (#156)"
            if ctx.inDefer then eerr p s!"{shown} suspends, and a defer cannot suspend (#156)"
            if ctx.canFail then eerr p s!"{shown} suspends, and a failure context (a condition, a filter, or a <decides> call's arguments) cannot (#156)"
          if !s.tparams.isEmpty then
            let r ← elabGenericCall ctx p s args exp
            if s.suspends then return ⟨← withDeferMark ctx r.e, r.ty⟩ else return r
          let isNamed : SExpr → Bool
            | .decl _ n _ _ _ => n.startsWith "?"
            | _ => false
          -- (a suspension point records the defers active there, #156)
          let mark (e : Expr) : EM Expr := if s.suspends then withDeferMark ctx e else pure e
          if s.named.isEmpty && !args.any isNamed then
            -- a tuple for several parameters is expanded into them (Book of
            -- Verse ch. 3: `Describe(MyTuple)` is `Describe(1, "two")`)
            if let [a] := args then
              if s.params.length > 1 then
                let r ← elabE ctx a (some (.tup s.params))
                if let .tup ts := r.ty then
                  if ts.length == s.params.length then
                    let tt ← fresh r.ty
                    let parts ← ((s.params.zip ts).zip (List.range ts.length)).mapM fun ((pt, et), i) =>
                      coerce a.pos ⟨.prim (.tupGet i) [.local tt], et⟩ pt
                    return ⟨← mark (.seq (.assign tt r.e) (.call s.idx parts)), s.ret⟩
                let (shown, off) := match name.splitOn "." with
                  | [_, m] => if s.pnames.head? == some "Self" then (m, 1) else (name, 0)
                  | _ => (name, 0)
                eerr p s!"{shown} takes {s.params.length - off} argument(s), found 1 (of type {r.ty.show})"
            -- several arguments for one array parameter make the array
            -- (`Sum(1, 2, 3, 4)`, as a tuple converts to an array)
            if let [.arr et] := s.params then
              if args.length > 1 then
                let es ← elabArgs ctx p args (args.map fun _ => et)
                return ⟨← mark (.call s.idx [.prim .mkArr es]), s.ret⟩
            let es ← elabArgs ctx p args s.params
            return ⟨← mark (.call s.idx es), s.ret⟩
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
          for ((ap, n, _), i) in named.zip (List.range named.length) do
            if (s.named.find? (·.1 == n)).isNone then eerr ap s!"{name} has no parameter ?{n}"
            if (named.take i).any (·.2.1 == n) then eerr ap s!"?{n} is given twice"
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
              -- (the default sees the parameters before it, in their temporaries)
              let earlier : List Local := ((s.pnames.zip (List.range k)).filterMap fun (pn, j) =>
                (slots[j]!).map fun sl => ({ name := pn, slot := sl, ty := ptys[j]!, mutable := false } : Local)).reverse
              -- (a method's: its receiver's fields too, through `Self`)
              let selfC : Option String :=
                if s.pnames.head? == some "Self" then (s.name.splitOn ".").head? else none
              -- (its own context: no return or break into the caller, failure
              -- only for a <decides> callee, and not its own default again)
              let key := (s.name, s!"?{n}")
              if ctx.defaults.contains key then
                eerr p s!"the default of ?{n} of {name} uses itself (a call of {name} that omits ?{n})"
              let dctx := { ctx with locals := earlier, selfClass := selfC, inParamDefault := true,
                                     inLoop := false, canFail := ctx.canFail && s.decides,
                                     suspends := ctx.suspends && s.suspends,
                                     defaults := key :: ctx.defaults }
              let rd ← fxAt p (do coerce p (← elabE dctx d (some t)) t)
              if !s.decides && rd.mayFail ctx.sigProg then
                eerr p s!"the default of ?{n} of {name} can fail, but {name} is not <decides>"
              steps := steps.push (.assign ta rd)
              slots := slots.set! k (some ta)
          let call := Expr.call s.idx (slots.toList.map fun o => Expr.local o.get!)
          let e := steps.toList.foldr Expr.seq call
          return ⟨← mark e, s.ret⟩
      | none =>
        if (ctx.sig? s!"{name}$init").isSome || (ctx.types.overloads.lookup s!"{name}$init").isSome then
          eerr p s!"{name} constructs an abstract class: it can only be delegated to, as {name}<constructor>(…) in a constructor of a class below it"
        eerr p s!"unknown function '{name}'"
  | .member mp (.ident _ "(super:)") m =>
    -- `(super:)M(…)`: the implementation the current method's class inherits
    let some c := ctx.selfClass | eerr p "(super:) can only be used in a method"
    if let some ms := (if (ctx.methodDecl? c m).isNone then ctx.types.methodOverloads.lookup m else none) then
      -- (the overloads above `c`)
      let above := (ctx.types.supers c).drop 1
      let declAbove (o : String) : Option String := above.find? fun e => (ctx.sig? s!"{e}.{o}").isSome
      let sigOf (o : String) : Option Sig := (declAbove o).bind fun owner =>
        (ctx.sig? s!"{owner}.{o}").map fun sg => { sg with params := sg.params.drop 1 }
      let vis := ms.filter fun o => (declAbove o).isSome
      if !vis.isEmpty then
        return ← resolveOverload ctx p m vis sigOf
          (fun o => elabApp ctx p (.member mp (.ident mp "(super:)") o) args bracket exp) args
    -- in `(r:)m`, slot r; otherwise every slot of `m` (#70): what is above `c`
    -- implements them alike, or the class chain's implementation is the one
    let slots := match ctx.selfMethod with
      | some cur => match (cur.drop 1).toString.splitOn ":)" with
        | [r, m'] => if cur.startsWith "(" && m' == m then [r] else ctx.rootsOf c m
        | _ => ctx.rootsOf c m
      | none => ctx.rootsOf c m
    let ups := (ctx.types.supers c).drop 1
    let found := (slots.filterMap fun r => (ctx.types.slotImpls (ctx.implAt r m) ups r).head?).eraseDups
    let inClass := found.filter fun f => !(ctx.types.info ((f.splitOn ".").head!)).isIface
    let impl ← match found, inClass with
      | [f], _ => pure f
      | [], _ => eerr p s!"nothing above {c} implements '{m}'"
      | _, [f] => pure f
      | f :: g :: _, _ =>
        eerr p s!"(super:){m} is ambiguous here: {f} and {g} implement it for different interfaces above {c}; call it from a qualified (i:){m}"
    elabApp ctx p (.ident mp impl) (.ident mp "Self" :: args) bracket exp
  | .member mp obj m0 =>
    -- `T.Await()` of a task (#156): the helper `$Await(T)`
    -- `T.Cancel()` of a task (#156): the mark `$cancelMark(T)`, which the
    -- lowering turns into the cancellation of the task's root
    if m0 == "Cancel" && args.isEmpty then
      let rt ← elabE ctx obj none
      if let .struct "task" [_] := rt.ty then
        if !ctx.suspends then eerr p "Cancel suspends: it can only be called in a <suspends> function (#156)"
        if ctx.inDefer then eerr p "Cancel suspends, and a defer cannot suspend (#156)"
        if ctx.canFail then eerr p "Cancel suspends, and a failure context (a condition, a filter, or a <decides> call's arguments) cannot (#156)"
        let some mark := ctx.sig? "$cancelMark" | eerr p "internal error: no Cancel helper"
        let t ← fresh rt.ty
        return ⟨.seq (.assign t rt.e) (.call mark.idx [.local t]), .void⟩
    -- `E.Signal()` of an `event()` (#156): with the value `void`
    if m0 == "Signal" && args.isEmpty then
      match (← elabE ctx obj none).ty with
      | .struct "event" [.void] | .struct "sticky_event" [.void] =>
        return ← elabApp ctx p (.member mp obj "Signal") [.tuple p []] bracket exp
      | _ => pure ()
    if m0 == "Await" && args.isEmpty then
      match (← elabE ctx obj none).ty with
      | .struct "task" [_] => return ← elabApp ctx p (.ident mp "$Await") [obj] false exp
      | .struct "event" [_] | .struct "subscribable_event" [_] =>
        return ← elabApp ctx p (.ident mp "$EvAwait") [obj] false exp
      | .struct "sticky_event" [_] => return ← elabApp ctx p (.ident mp "$StickyAwait") [obj] false exp
      | _ => pure ()
    let r0 ← elabE ctx obj none
    -- `X.(i:)M(…)`: `X` as an `i`, so `i`'s `M` (a qualified call)
    let (r, m) ← match r0.ty, m0.startsWith "(", (m0.drop 1).toString.splitOn ":)" with
      | .struct c ts, true, [q, mq] =>
        if !(ctx.types.isSub c q) then eerr p s!"{c} is not below {q}"
        -- (converted: a receiver of a type with no instance is unreachable)
        let qt : Ty := .struct q (ctx.types.upArgs c ts q)
        pure (⟨← coerce p r0 qt, qt⟩, mq)
      | _, _, _ => pure (r0, m0)
    match r.ty with
    | .struct c targs =>
      let env := ctx.types
      -- an overloaded method (#106): the overload visible at `c` the call
      -- fits, then that method
      if let some ms := (if env.classes.contains c && (ctx.methodDecl? c m).isNone then
          env.methodOverloads.lookup m else none) then
        let sigOf (o : String) : Option Sig := (ctx.methodDecl? c o).bind fun owner =>
          (ctx.sig? s!"{owner}.{o}").map fun sg => { sg with params := sg.params.drop 1 }
        let vis := ms.filter fun o => (ctx.methodDecl? c o).isSome
        -- (a qualified call stays qualified: `X.(q:)M$ovK(…)`, #125)
        let qualOf (o : String) : String :=
          if m0.startsWith "(" then
            match (m0.drop 1).toString.splitOn ":)" with
            | [q, _] => s!"({q}:){o}"
            | _ => o
          else o
        if !vis.isEmpty then
          return ← resolveOverload ctx p m vis sigOf (fun o => elabApp ctx p (.member mp obj (qualOf o)) args bracket exp) args
      if let (true, some owner) := (env.classes.contains c, ctx.methodDecl? c m) then
        -- the slots the call covers (#70): every class below `c` must implement
        -- them alike, or the call must say which
        let roots := ctx.rootsOf c m
        let root := roots.headD owner
        for d in env.concreteBelow c do
          for o in roots do
            if ctx.implFor? d o m != ctx.implFor? d root m then
              eerr p s!"{d} implements {m} separately for {root} and {o}: call it as X.({root}:){m}(…) or X.({o}:){m}(…)"
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
        let clsOf (fname : String) : String := (fname.splitOn ".").head!
        let direct : Option String := match (ds.map (ctx.implFor? · root m)).eraseDups with
          | [some fname] => if env.isSub c (clsOf fname) then some fname else none
          | _ => none
        -- the receiver as an instance of class `e`, above or below `c` (#39)
        let argsAt (e : String) : List Ty :=
          if env.isSub c e then env.upArgs c targs e else env.argsBelow c targs e
        if let some fname := direct then
          let e := clsOf fname
          let ctx' := { ctx with locals := { name := recv, slot, ty := .struct e (argsAt e), mutable := false } :: ctx.locals }
          let rc ← elabApp ctx' p (.ident mp fname) (.ident mp recv :: args) bracket exp
          return ⟨.seq (.assign slot r.e) rc.e, rc.ty⟩
        -- otherwise dispatch on the class of the receiver's value: the
        -- receiver, then the arguments, once each, then the implementation of
        -- the class whose option is set
        let ownerTps := ((env.sparams.lookup owner).getD []).map (·.1)
        -- the declaration's types at the receiver's type arguments, its own
        -- type parameters renamed apart (they are inferred from the
        -- arguments below, as for a generic call)
        let ownTps := ms.tparams.drop ownerTps.length
        let ownσ : List (String × Ty) := (ownTps.zip (List.range ownTps.length)).map fun ((v, k), i) =>
          (v, Ty.param s!"$own{i}" k)
        let ownNames := (List.range ownTps.length).map fun i => s!"$own{i}"
        let σ := ownerTps.zip (argsAt owner)
        let declTy (t : Ty) : Ty := (t.subst ownσ).subst σ
        let mut σu : List (String × Ty) := []
        -- the arguments, once each: positional ones left to right, then named
        -- ones as written (Book of Verse §2.5), passed to every implementation;
        -- those omitted take the default of the implementation that runs, as
        -- in a call without named arguments
        let isNamed : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
        let posArgs := args.filter (!isNamed ·)
        let namedArgs := args.filterMap fun a => match a with
          | .decl ap n _ _ rhs => if n.startsWith "?" then some (ap, (n.drop 1).toString, rhs) else none
          | _ => none
        let npos := ms.params.length - ms.named.length
        if posArgs.length + 1 != npos then
          eerr p s!"{m} takes {npos - 1} positional argument(s), found {posArgs.length}"
        for (ap, n, _) in namedArgs do
          if (ms.named.find? (·.1 == n)).isNone then eerr ap s!"{m} has no parameter ?{n}"
        let mut pre : Array Expr := #[.assign slot r.e]
        let mut locs : List Local := [{ name := recv, slot, ty := r.ty, mutable := false }]
        let mut argIds : Array SExpr := #[]
        -- the method's own type parameters, from the expected result type
        -- (unless void), then from the arguments, as for a generic call: an
        -- argument is checked against its parameter's type once the own type
        -- parameters it mentions are bound, else inferred from; `false`,
        -- `array{}` and `map{}` take their type from context, so they wait
        -- for the others (they are still evaluated in order)
        let showT (t : Ty) : String :=
          (t.subst ((ownNames.zip ownTps).map fun (n, (v, k)) => (n, Ty.param v k))).show
        let own? (σ' : List (String × Ty)) := σ'.filter fun (v, _) => ownNames.contains v
        if let some et := exp then
          if !(et == .void) then
            if let some σ' := (declTy ms.ret).matchArg ctx.types σu et then σu := own? σ'
        let fromContext : SExpr → Bool
          | .ident _ "false" | .arrayLit _ [] | .mapLit _ [] => true
          | _ => false
        let posPs := (ms.params.drop 1).take (npos - 1)
        let mut done : Array (Option (Expr × Ty)) := Array.replicate posArgs.length none
        let mut deferred : Array Bool := (posArgs.map fromContext).toArray
        for pass in [0, 1] do
          for ((a, t0), i) in (posArgs.zip posPs).zip (List.range posArgs.length) do
            if (pass == 0) == deferred[i]! then continue
            let t := (declTy t0).subst σu
            if t.params.any ownNames.contains then
              if fromContext a then
                eerr a.pos s!"cannot infer the type parameters of {m} from the arguments of this call"
              let r ← elabE ctx a none
              match t.matchArg ctx.types σu r.ty with
              | some σ' =>
                σu := own? σ'
                let t' := t.subst σu
                if t'.params.any ownNames.contains then
                  if pass == 0 then deferred := deferred.set! i true
                  else eerr a.pos s!"cannot infer the type parameters of {m} from this argument"
                else done := done.set! i (some (← coerce a.pos r t', t'))
              | none => eerr a.pos s!"expected {showT t}, found {r.ty.show} (in a call of {m})"
            else
              done := done.set! i (some (← coerce a.pos (← elabE ctx a (some t)) t, t))
        for d in done do
          let some (e, t) := d | eerr p s!"cannot infer the type parameters of {m} from the arguments of this call"
          let ta ← fresh t
          pre := pre.push (.assign ta e)
          locs := { name := s!"$arg{ta}", slot := ta, ty := t, mutable := false } :: locs
          argIds := argIds.push (.ident mp s!"$arg{ta}")
        let mut namedSlots : List (String × Nat) := []
        for (ap, n, rhs) in namedArgs do
          -- (at the own type parameters inferred so far; one it mentions
          -- that is not yet bound is inferred from it, #119)
          let t0 := (declTy (ms.params[npos + (ms.named.findIdx? (·.1 == n)).get!]!)).subst σu
          let mut t := t0
          let mut e : Expr := .lit .void
          if t0.params.any ownNames.contains then
            if fromContext rhs then
              eerr ap s!"cannot infer the type parameters of {m} from the arguments of this call"
            let r ← elabE ctx rhs none
            match t0.matchArg ctx.types σu r.ty with
            | some σ' =>
              σu := own? σ'
              t := t0.subst σu
              if t.params.any ownNames.contains then
                eerr ap s!"cannot infer the type parameters of {m} from this argument"
              e ← coerce ap r t
            | none => eerr ap s!"expected {showT t0}, found {r.ty.show} (in a call of {m})"
          else
            e ← coerce ap (← elabE ctx rhs (some t0)) t0
          let ta ← fresh t
          pre := pre.push (.assign ta e)
          locs := { name := s!"$arg{ta}", slot := ta, ty := t, mutable := false } :: locs
          namedSlots := namedSlots ++ [(n, ta)]
        for (n, ta) in namedSlots do
          argIds := argIds.push (.decl mp s!"?{n}" none false (.ident mp s!"$arg{ta}"))
        let msRet := (declTy ms.ret).subst σu
        if msRet.params.any ownNames.contains then
          eerr p s!"cannot infer the type parameters of {m} from the arguments of this call"
        let mut acc : Expr := .prim .userErr []   -- no option set: unreachable
        if env.isRefClass c then
          -- a reference: one test of the object's class per implementation (#34)
          let mut groups : Array (String × Array String) := #[]
          for d in ds do
            let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
            match groups.findIdx? (·.1 == fname) with
            | some gi => groups := groups.modify gi fun (e', cls) => (e', cls.push d)
            | none => groups := groups.push (fname, #[d])
          let mut pinned := false
          let mut emitted := false
          for (fname, cls) in groups.toList.reverse do
            let e := clsOf fname
            -- (#142) the type arguments the classes fix that the receiver's
            -- may not have: matched against the receiver's, they refine the
            -- call, which `Typed.dispatch` types under that refinement
            let rargs := env.coreArgs c targs
            -- (#209) the type arguments that the tested classes have pins
            -- on beyond the receiver's are opened as fresh parameters, which
            -- the refinement binds (as the checker opens them, `openCount`:
            -- a test is of classes with the same pins)
            let eLen := (env.pinsOf e).length
            let extOf (pins : List (Option Ty)) : List Ty :=
              (List.range (pins.length - rargs.length)).map fun i => Ty.param s!"$ext{i}" true
            let needOf (pins : List (Option Ty)) :=
              let rx := rargs ++ extOf pins
              let atR := rx.zipIdx.map fun (r, j) => (pinArg j, r)
              (rx.zip pins).filterMap fun (a, pin) => match pin with
                | some pt => let pt := pt.subst atR; if a == pt then none else some (a, pt)
                | none => none
            -- (a generic <suspends> implementation at or above the receiver's
            -- class is called at the receiver's own type arguments, without
            -- the refinement: its frame is made by a call typed without it)
            let plainSusp := ms.suspends && env.isSub c e && !((ctx.sig? fname).map (·.tparams.isEmpty)).getD true
            -- (an implementation at or above the receiver's class is called
            -- at the receiver's type arguments, which it takes as they are)
            if !plainSusp && !env.isSub c e && cls.any fun d =>
                !(needOf (env.corePins d)).isEmpty || eLen > rargs.length then
              -- one test per set of pins among the classes using `e`'s
              -- implementation: `Typed.dispatch` refines by the pins all the
              -- tested classes share, which may fix more than `e`'s (and it
              -- takes the receiver as narrowed by the test, so no temporary
              -- of `e`'s type, which might have no initial value)
              let mut parts : Array (List (Option Ty) × Array String) := #[]
              for d in cls do
                let key := env.corePins d
                match parts.findIdx? (·.1 == key) with
                | some pi => parts := parts.modify pi fun (k, ds') => (k, ds'.push d)
                | none => parts := parts.push (key, #[d])
              for (pins, part) in parts.toList.reverse do
                -- (whether an object of `part` can be the receiver, by
                -- Verse's types)
                if (Ty.unifyEqs (fun _ _ => none) [] (needOf pins)).isNone then continue
                -- (pins that relate the receiver's type arguments to ones
                -- past those of `e`, whose implementation is called: they
                -- would instantiate `e`'s type parameters with what the
                -- dispatch opens, which it has no values of; so no
                -- refinement, and `e`'s implementation must take the
                -- receiver as it is)
                -- (unless the implementation takes no values of type arguments,
                -- reading them from its receiver, `Sig.selfTps`)
                let calleeDicts := ((ctx.sig? fname).map (·.ndicts)).getD 0
                if calleeDicts != 0 &&
                    !VTy.pinsBelow (env.lowerPins (pins.take (max eLen rargs.length))) (max eLen rargs.length) then
                  if !(needOf (env.corePins e)).isEmpty || eLen > rargs.length then
                    eerr p s!"cannot dispatch {m} on {withArticle (Ty.struct c targs).show} to class {part[0]!} yet: its type arguments there relate to ones that {e} does not have (#209)"
                  let sd ← fresh (.struct e (argsAt e))
                  let ctx' := { ctx with locals := { name := s!"$self{sd}", slot := sd, ty := .struct e (argsAt e), mutable := false } :: (locs ++ ctx.locals) }
                  let rc ← elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
                  acc := .ite (.assign sd (.heap (.isTag (part.toList.map env.tagOf)) [.local slot]))
                    (← coerce p rc msRet) acc
                  emitted := true
                  continue
                -- (no instance of the receiver's type arguments agrees with
                -- the pins: no object of `part` is the receiver)
                -- (whether an object of `part` can be the receiver, by
                -- Verse's types; the refinement, as Verse Core has it: a
                -- value struct by its fields, #209)
                if (Ty.unifyEqs (fun _ _ => none) [] (needOf pins)).isNone then continue
                let coreFields (n : String) (ts : List Ty) : Option (List Ty) :=
                  if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
                let some μF := Ty.unifyEqs coreFields [] (needOf pins) | continue
                let selfName := s!"$self{slot}"
                let locsF := locs.map fun l => { l with ty := l.ty.subst μF }
                let argsE := if env.isSub c e then argsAt e else env.argsBelow c targs e (extOf pins)
                let selfL : Local := { name := selfName, slot, ty := .struct e (argsE.map (·.subst μF)), mutable := false }
                let ctx' := { ctx with locals := selfL :: (locsF ++ ctx.locals) }
                let rc ← elabApp ctx' p (.ident mp fname) (.ident mp selfName :: argIds.toList) bracket
                  (some (msRet.subst μF))
                -- (named arguments go through temporaries: put their values
                -- in the call, which must have the rule's shape)
                -- (a suspends call carries the defers active at it, which
                -- go around the whole dispatch instead)
                let rcE : Expr := match rc.e with
                  | .seq (.ite (.prim .fail []) _ (.lit .void)) b => b
                  | e => e
                -- (an omitted named argument's default with no type of its
                -- own, `false`, `array{}` or `map{}`, goes in as `if (fail)
                -- then T else false`, with `T` its temporary, whose type is
                -- the parameter's, so that the checker infers it, as the rule
                -- infers the other arguments' types, #175)
                let rec untyped : Expr → List Nat
                  | .seq (.assign t (.lit .none)) rest => t :: untyped rest
                  | .seq (.assign t (.lit (.arr a))) rest => if a.isEmpty then t :: untyped rest else untyped rest
                  | .seq _ rest => untyped rest
                  | _ => []
                let rec litOf (t : Nat) : Expr → Expr
                  | .seq (.assign t' v) rest => if t' == t then v else litOf t rest
                  | _ => .lit .none
                let typed : List (Nat × Expr) := (untyped rcE).map fun t =>
                  (t, .ite (.prim .fail []) (.local t) (litOf t rcE))
                if pins.length > rargs.length && !typed.isEmpty then
                  eerr p s!"cannot dispatch {m} to class {e} yet when a named argument's default has no type of its own: its temporary would need the type arguments the dispatch opens (#209)"
                let some (.call fi (.local s0 :: es)) := Expr.inlineArgTemps rcE typed
                  | eerr p s!"cannot dispatch {m} to class {e}, which fixes type arguments of {c}, when a named argument's default is computed (#142)"
                if s0 != slot then eerr p s!"cannot dispatch {m} to class {e}, which fixes type arguments of {c} (#142)"
                acc := .ite (.heap (.isTag (part.toList.map env.tagOf)) [.local slot]) (.call fi (.local slot :: es)) acc
                pinned := true
                emitted := true
              continue
            let sd ← fresh (.struct e (argsAt e))
            let ctx' := { ctx with locals := { name := s!"$self{sd}", slot := sd, ty := .struct e (argsAt e), mutable := false } :: (locs ++ ctx.locals) }
            let rc ← elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
            acc := .ite (.assign sd (.heap (.isTag (cls.toList.map env.tagOf)) [.local slot]))
              (← coerce p rc msRet) acc
            emitted := true
          -- (no class can be the receiver: the call cannot run; a failable
          -- one still fails, for the failure checks)
          if !emitted && ms.decides then acc := .prim .fail []
          if pinned then
            -- (checked against the method's result type, as the refined
            -- calls need an expected type)
            let y ← fresh msRet
            let body ← if ms.suspends then withDeferMark ctx (.assign y acc) else pure (.assign y acc)
            return ⟨pre.toList.foldr Expr.seq body, msRet⟩
          return ⟨pre.toList.foldr Expr.seq acc, msRet⟩
        for (d, j) in (ds.zip (List.range ds.length)).reverse do
          let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
          let td ← fresh (classRepTy env d)
          let sd ← fresh (.struct d [])
          let ctx' := { ctx with locals := { name := s!"$self{sd}", slot := sd, ty := .struct d [], mutable := false } :: (locs ++ ctx.locals) }
          let rc ← elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
          acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local slot]]))
            (.seq (.assign sd (classWrap env d d (.local td))) (← coerce p rc msRet)) acc
        let y ← fresh msRet
        return ⟨pre.toList.foldr Expr.seq (.assign y acc), msRet⟩
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
    | .struct S sargs => if env.classes.contains S then pure (S, sargs) else eerr p s!"cannot cast {withArticle S} to {T}"
    | t => eerr p s!"cannot cast {withArticle t.show} to {T}"
  -- a parametric class's type arguments are those of the value (#39), in the
  -- same hierarchy
  let parametric := (env.sparams.lookup T).isSome || !(env.coreArgs T []).isEmpty
  if (env.concreteBelow S).all (fun d => !env.isSub d T) then
    eerr p s!"no class is below both {r.ty.show} and {T}, so {T}[…] would always fail"
  if parametric && !(env.isSub S T || env.isSub T S) then
    eerr p s!"cannot cast {withArticle S} to {T}: {T}'s type arguments would be unknown (they are not {S}'s)"
  let targs := if env.isSub S T then env.upArgs S sargs T else env.argsBelow S sargs T
  if parametric && (env.coreArgs T targs).length > (env.coreArgs S sargs).length then
    eerr p s!"cannot cast {withArticle r.ty.show} to {T}: {T} has type parameters that {S} does not have, which would be unknown"
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
    if (Ty.unifyEqs (fun _ _ => none) [] ((env.coreArgs S sargs).zip (env.coreArgs T targs))).isSome then
      eerr p s!"cannot cast {withArticle r.ty.show} to {(Ty.struct T targs).show} here: their type arguments agree only under a refinement, which a cast gives only as the whole condition of an if, D := {T}[X], whose branch is then typed under it (#209, #243)"
    eerr p s!"{withArticle r.ty.show} is never {withArticle T}: their type arguments differ, so {T}[…] would always fail"
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

/-- `if (D := T[X]) then Body else Else`, where the cast holds only under a
    refinement of the code's type parameters (#243). `Body` is lifted into
    a generic function (`Refine.functions`), asked for in a first
    elaboration, which elaborates `Body` in the refined world to find its
    type, effects and the locals it uses. Then the `if` is a dispatch to
    it, one test per set of pins among the classes tested, as a refined
    method call is: `Typed.dispatch` types the call under the refinement,
    with the object (as `D`) and those locals passed at their refined
    types. `none` when the cast does not refine: the plain path. -/
partial def elabRefinedIf (ctx : Ctx) (p _dp : Pos) (D T : String) (x : SExpr) (body : SExpr)
    (elseE : Option SExpr) (exp : Option Ty) : EM (Option R) := do
  let env := ctx.types
  if !env.classes.contains T then return none
  let st0 ← get
  let rx ← elabE { ctx with canFail := true, inTaking := true } x none
  let some (S, sargs, targs, common, eqs) := refiningCast? env T rx.ty | do set st0; return none
  if !env.isRefClass S then set st0; return none
  let coreFields (n : String) (ts : List Ty) : Option (List Ty) :=
    if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
  let some μT := Ty.unifyEqs coreFields [] eqs | do set st0; return none
  let shown := (Ty.struct T targs).show
  -- (the locals the branch uses, in order of first use)
  let caps : List Local := (Choice.namesUsed body).filterMap fun n =>
    if n == D then none else ctx.locals.find? (·.name == n)
  if let some (q, what) := refineBranchWhy? ctx p body ((caps.filter (·.mutable)).map (·.name)) then
    eerr q s!"the branch of the cast to {shown}, which holds only under a refinement of the type arguments, is compiled as a function of its own, so {what} (#243)"
  -- (a suspension in the branch or in the `else`, which the dispatch to the
  -- branch's function would have to carry, is refused for now)
  let isS (f : Nat) : Bool := ctx.sigs.any fun s => s.idx == f && s.suspends
  let elseOf : EM R := match elseE with
    | none => pure ⟨.lit .void, .void⟩
    | some ee => do
      let re ← elabE ctx ee exp
      if ctx.suspends && Suspend.hasSusp isS re.e then
        eerr ee.pos s!"the else of the cast to {shown}, which holds only under a refinement of the type arguments, cannot suspend yet: the if is a dispatch to its branch's function (#243)"
      pure re
  let key := Refine.keyOf p D
  match env.castRequests.find? (·.key == key) with
  | none =>
    -- (first: the branch in the refined world)
    let refine (t : Ty) : Ty := t.subst μT
    let dTy := refine (.struct T targs)
    let dslot ← fresh dTy
    let ctxB : Ctx := { ctx with
      locals := { name := D, slot := dslot, ty := dTy, mutable := false } ::
        ctx.locals.map fun l => { l with ty := refine l.ty },
      types := { env with tvars := env.tvars.map fun (n, t) => (n, refine t) } }
    -- (its own effects, which its function declares; the enclosing one's too)
    let fx0 := (← get).fx
    modify fun st => { st with fx := [] }
    let rb ← elabE ctxB body (if elseE.isNone then some .void else exp.map refine)
    if ctx.suspends && Suspend.hasSusp isS rb.e then
      eerr body.pos s!"the branch of the cast to {shown}, which holds only under a refinement of the type arguments, is compiled as a function of its own, so it cannot suspend yet (#243)"
    let fxB := (← get).fx
    modify fun st => { st with fx := fx0 }
    for (k, q, via) in fxB do noteFx q [k] via
    let re ← elseOf
    let τ' : Ty := if elseE.isNone then .void else exp.getD re.ty
    let ret := refine τ'
    discard <| coerce p rb ret
    let decides := rb.e.mayFail ctx.sigProg
    let sig := caps.map fun l => (l.name, refine l.ty)
    let tps := ((dTy :: ret :: sig.map (·.2)).flatMap Ty.paramsC).foldl
      (fun acc (n, c) => if acc.any (·.1 == n) then acc else acc ++ [(n, c)]) []
    -- (the type parameters only the types written in the branch mention:
    -- each through a parameter of its own, passed a value of it, so that
    -- the call determines it)
    let written := ((Refine.typeNames body).filterMap fun w =>
      (env.tvars.lookup w).map refine).flatMap Ty.paramsC
    let extra := written.foldl (fun acc (n, c) =>
      if tps.any (·.1 == n) || acc.any (·.1 == n) then acc else acc ++ [(n, c)]) []
    let tps := tps ++ extra
    if let some (n, _) := tps.find? fun (n, _) => !ctx.dictVars.contains n then
      eerr p s!"cannot lift the branch of the cast to {shown} yet: its types mention {n}, which this function has no value of (#243)"
    -- (from the enclosing function's own names, also through the
    -- refinements of the casts this one is in, as the branch is taken from
    -- the source)
    let σ := env.tvars.filterMap fun (n, t) =>
      let t' := refine t
      match t' with
      | .param m _ => if m == n then none else some (n, t'.toSTy)
      | _ => some (n, t'.toSTy)
    let heap := ["reads", "writes", "allocates"].filter fun k => fxB.any (·.1 == k)
    let specs := (if heap.isEmpty then ["computes"] else heap) ++ (if decides then ["decides"] else [])
    let lift : Refine.Lift := {
      pos := p, bound := D, target := T,
      name := s!"$refine{p.line}_{p.col}_{D}" ++ (if p.file.isEmpty then "" else s!"_{p.file}"),
      params := ((D, dTy) :: sig).map (fun (n, t) => { name := n, ty := t.toSTy }) ++
        extra.map fun (n, _) => { name := s!"$type{n}", ty := .name n },
      tparams := tps.map fun (n, c) => { pos := p, name := n, constraint := if c then "comparable" else "type" },
      specs, ret := ret.toSTy, subst := σ }
    modify fun st => if st.castNeeds.any (·.key == key) then st else { st with castNeeds := st.castNeeds ++ [lift] }
    -- (a placeholder: this elaboration goes no further)
    return some ⟨if decides then .prim .fail [] else .prim .userErr [], τ'⟩
  | some l =>
    -- (then: the object in a slot, and one dispatch per set of pins)
    let (pre, y) ← match rx.e with
      | .local y => pure ([], y)
      | e => do
        let y ← fresh rx.ty
        pure ([Expr.assign y e], y)
    let re ← elseOf
    let τ' : Ty := if elseE.isNone then .void else exp.getD re.ty
    let eE ← coerce p re τ'
    let rargs := env.coreArgs S sargs
    let atR := rargs.zipIdx.map fun (r, j) => (pinArg j, r)
    let needOf (pins : List (Option Ty)) := (rargs.zip pins).filterMap fun (a, pin) => match pin with
      | some pt => let pt := pt.subst atR; if a == pt then none else some (a, pt)
      | none => none
    let mut parts : Array (List (Option Ty) × Array String) := #[]
    -- (keyed by each class's pins on the object's type arguments: the
    -- branch needs none of those a class below adds, so a test of classes
    -- that share those pins opens what the fewest of them add, as the
    -- checker's `openCount` does: none when one of them adds none)
    for d in common do
      let k := (env.corePins d).take rargs.length
      match parts.findIdx? (·.1 == k) with
      | some pi => parts := parts.modify pi fun (k', ds) => (k', ds.push d)
      | none => parts := parts.push (k, #[d])
    -- (an object that is no local: evaluated with a test of all the
    -- classes tested, in one condition, so that its effects roll back and
    -- its failure takes the else when the cast fails; the dispatch then
    -- tests each part, its end unreachable)
    let mut acc := if pre.isEmpty then eE else .prim .userErr []
    let mut tested : Array String := #[]
    for (pins, part) in parts.toList.reverse do
      if !VTy.pinsBelow (env.lowerPins pins) rargs.length then
        eerr p s!"cannot cast {withArticle rx.ty.show} to {shown} yet: class {part[0]!} relates its type arguments to ones that {S} does not have (#209, #243)"
      -- (no object of `part` can be this one: no test)
      let some μF := Ty.unifyEqs coreFields [] (needOf pins) | continue
      let dL : Local := { name := D, slot := y, ty := (Ty.struct T targs).subst μF, mutable := false }
      let ctx' := { ctx with
        locals := dL :: ctx.locals.map fun loc => { loc with ty := loc.ty.subst μF },
        types := { env with tvars := env.tvars.map fun (m, t) => (m, t.subst μF) } }
      let argOf (sp : SParam) : SExpr :=
        if sp.name.startsWith "$type" then .app p (.ident p "$witness") [.ident p (sp.name.drop 5).toString] false
        else .ident p sp.name
      let rc ← elabApp ctx' p (.ident p l.name) (l.params.map argOf)
        (l.specs.contains "decides") (some (τ'.subst μF))
      let .call fi (.local s0 :: es) := rc.e
        | eerr p s!"cannot lift the branch of the cast to {shown} yet: its call is not a plain one (#243)"
      if s0 != y then eerr p s!"cannot lift the branch of the cast to {shown} yet (#243)"
      acc := .ite (.heap (.isTag (part.toList.map env.tagOf)) [.local y]) (.call fi (.local y :: es)) acc
      tested := part ++ tested
    let t ← fresh τ'
    if pre.isEmpty then return some ⟨.assign t acc, τ'⟩
    let cond := pre.foldr Expr.seq (.heap (.isTag (tested.toList.map env.tagOf)) [.local y])
    return some ⟨.assign t (.ite cond acc eE), τ'⟩

/-- A call of a generic function. Its type arguments are inferred by matching
    its signature: the result type against the expected type (unless that is
    `void`, which accepts anything), then each parameter type against its
    argument's, left to right. An argument whose parameter type is already
    determined is elaborated against it, so `array{}` and `false` work. -/
partial def elabGenericCall (ctx : Ctx) (p : Pos) (s : Sig) (args : List SExpr) (exp : Option Ty) :
    EM R := do
  -- named arguments (#119): positional ones, then named ones as written,
  -- then the defaults of those omitted, as for other functions
  let isNamed : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  let npos := s.params.length - s.named.length
  let pos := args.filter (!isNamed ·)
  let named : List (Pos × String × SExpr) := args.filterMap fun
    | .decl ap n _ _ rhs => if n.startsWith "?" then some (ap, (n.drop 1).toString, rhs) else none
    | _ => none
  let plain := s.named.isEmpty && named.isEmpty
  if plain then
    if args.length != s.params.length then
      eerr p s!"{s.name} takes {s.params.length} argument(s), found {args.length}"
  else
    if pos.length != npos then
      -- (a method's receiver is its first positional argument)
      let (shown, off) := match s.name.splitOn "." with
        | [_, m] => if s.pnames.head? == some "Self" then (m, 1) else (s.name, 0)
        | _ => (s.name, 0)
      eerr p s!"{shown} takes {npos - off} positional argument(s), found {pos.length - off}"
    for ((ap, n, _), i) in named.zip (List.range named.length) do
      if (s.named.find? (·.1 == n)).isNone then eerr ap s!"{s.name} has no parameter ?{n}"
      if (named.take i).any (·.2.1 == n) then eerr ap s!"?{n} is given twice"
  -- the arguments given, in the order they are evaluated, each with the
  -- index of its parameter
  let given : List (SExpr × Nat) := (pos.zip (List.range npos)) ++ named.map fun (_, n, rhs) =>
    (rhs, npos + (s.named.findIdx? (·.1 == n)).getD 0)
  let ptys := s.params.toArray
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
  let mut es : Array Expr := Array.replicate given.length (.lit .void)
  -- arguments left for the second pass; an argument whose type contains
  -- `false` (like `array{Err()}`) binds nothing, so it joins them
  let mut deferred : Array Bool := (given.map (fromContext ·.1)).toArray
  for pass in [0, 1] do
    for ((a, k), i) in given.zip (List.range given.length) do
      let pt := ptys[k]!
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
  -- the arguments, in their temporaries, then the defaults
  let mut steps : Array Expr := #[]
  let mut slots : Array (Option Nat) := Array.replicate s.params.length none
  if !plain then
    for ((_, k), i) in given.zip (List.range given.length) do
      let ta ← fresh (ptys[k]!.subst σ)
      steps := steps.push (.assign ta es[i]!)
      slots := slots.set! k (some ta)
    for ((n, dflt), j) in s.named.zip (List.range s.named.length) do
      let k := npos + j
      if slots[k]!.isNone then
        let some d := dflt | eerr p s!"{s.name} needs the argument ?{n}, which has no default"
        let pt := ptys[k]!
        -- (the default sees the parameters before it, in their temporaries)
        let earlier : List Local := ((s.pnames.zip (List.range k)).filterMap fun (pn, j) =>
          (slots[j]!).map fun sl => ({ name := pn, slot := sl, ty := ptys[j]!.subst σ, mutable := false } : Local)).reverse
        let key := (s.name, s!"?{n}")
        if ctx.defaults.contains key then
          eerr p s!"the default of ?{n} of {s.name} uses itself (a call of {s.name} that omits ?{n})"
        -- (a method's: its receiver's fields too, through `Self`)
        let selfC : Option String :=
          if s.pnames.head? == some "Self" then (s.name.splitOn ".").head? else none
        let dctx := { ctx with locals := earlier, selfClass := selfC, inParamDefault := true,
                               inLoop := false, canFail := ctx.canFail && s.decides,
                               suspends := ctx.suspends && s.suspends,
                               defaults := key :: ctx.defaults }
        -- (its type: the parameter's, or what the default gives a type
        -- parameter nothing else determined)
        let σ0 := σ
        if !bound σ0 pt && fromContext d then
          let v := (pt.params.filter fun v => (σ0.lookup v).isNone).headD "t"
          eerr p s!"cannot infer type parameter {v} of {s.name} from the arguments of this call"
        let (rd, σ1) ← fxAt p (do
          let r ← elabE dctx d (if bound σ0 pt then some (pt.subst σ0) else none)
          let σ1 ← if bound σ0 pt then pure σ0 else
            match pt.matchArg ctx.types σ0 r.ty with
            | some σ' => pure σ'
            | none => eerr p s!"the default of ?{n} of {s.name} is a {r.ty.show}, not a {(pt.subst σ0).show}"
          return (← coerce p r (pt.subst σ1), σ1))
        σ := σ1
        if !s.decides && rd.mayFail ctx.sigProg then
          eerr p s!"the default of ?{n} of {s.name} can fail, but {s.name} is not <decides>"
        let ta ← fresh (pt.subst σ)
        steps := steps.push (.assign ta rd)
        slots := slots.set! k (some ta)
  let mut targs : Array Ty := #[]
  for (v, cmp) in s.tparams do
    let some t := σ.lookup v
      | eerr p s!"cannot infer type parameter {v} of {s.name} from the arguments of this call"
    -- (not of a value class's `$call…`, #218: the class's type arguments
    -- are its receiver's, fixed, and checked, when the value was made; a
    -- call through a function type only dispatches to it)
    let valueCall := !(s.name.splitOn ".$call").tail.isEmpty
    if cmp && !valueCall && !t.comparable ctx.types then
      eerr p (notComparable ctx.types t s!"type parameter {v} of {s.name}")
    targs := targs.push t
  -- the hidden arguments: a value of each type argument (but those a
  -- method reads from its receiver, #209)
  let dicts ← ((targs.toList.zip s.tparams).filter fun (_, (v, _)) => !s.selfTps.contains v).mapM
    fun (t, _) => witness ctx.types ctx.dictBase ctx.dictVars t
  if plain then return ⟨.call s.idx (es.toList ++ dicts), s.ret.subst σ⟩
  let call := Expr.call s.idx (slots.toList.map (fun o => Expr.local o.get!) ++ dicts)
  return ⟨steps.toList.foldr Expr.seq call, s.ret.subst σ⟩

/-- The failable array methods of the Book of Verse (§9.1):
    `A.Slice[i, j]`, `A.Slice[i]`, `A.Find[x]`, `A.RemoveElement[i]`,
    `A.ReplaceElement[i, x]`, `A.Insert[i, B]`, `A.Last[]`, `A.Last[n]`. Each fails when an index is
    out of range (or, for `Find`, when there is no such element). -/
partial def elabMethod (ctx : Ctx) (p : Pos) (r : R) (m : String) (args : List SExpr) (bracket : Bool) :
    EM R := do
  let .arr t := r.ty | eerr p s!"{r.ty.show} has no method '{m}'"
  -- (the methods that cannot fail take parentheses, #150)
  let total := ["RemoveAllElements", "ReplaceAllElements", "ReplaceAll"].contains m
  if total && bracket then eerr p s!"{m} cannot fail: call it with A.{m}(…)"
  if !total && !bracket then eerr p s!"{m} can fail: call it with A.{m}[…]"
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
  -- `A.Last[]` is the last element, `A.Last[N]` the one N before it (Book of
  -- Verse ch. 3): failing when there is none
  | "Last", [] => return ⟨.seq start (p2 .index (.local ta) (p2 .sub len (int 1))), t⟩
  | "Last", [n] =>
    let es ← elabInts ctx p [n]
    return ⟨.seq start (p2 .index (.local ta) (p2 .sub (p2 .sub len (int 1)) es[0]!)), t⟩
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
  -- (#150) the first occurrence of `x`, removed or replaced: failing when
  -- there is none
  | "RemoveFirstElement", [x] | "ReplaceFirstElement", [x, _] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t s!"the element type of {m}")
    let rx ← elabE ctx x (some t)
    let tx ← fresh t
    let ti ← fresh .int
    let found := Expr.forE ti (.prim .range [int 0, p2 .sub len (int 1)])
      (p2 .eq (p2 .index (.local ta) (.local ti)) (.local tx)) (.local ti)
    let tk ← fresh .int
    let first := Expr.seq (.assign tx (← coerce p rx t)) (.assign tk (p2 .index found (int 0)))
    match m, args with
    | "ReplaceFirstElement", [_, y] =>
      let ry ← elabE ctx y (some t)
      return ⟨.seq start (.seq first (.prim .arrSet [.local ta, .local tk, ← coerce p ry t])), r.ty⟩
    | _, _ =>
      return ⟨.seq start (.seq first
        (p2 .concat (← slice (int 0) (.local tk)) (← slice (p2 .add (.local tk) (int 1)) len))), r.ty⟩
  -- `A.Remove[i, j]`: without the elements i…j-1 (0 ≤ i ≤ j ≤ the length)
  | "Remove", [a, b] =>
    let es ← elabInts ctx p [a, b]
    let tlo ← fresh .int
    let thi ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (.seq (p2 .le (.local tlo) (.local thi))
      (p2 .le (.local thi) len))
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq (.assign thi es[1]!) (.seq chk
      (p2 .concat (← slice (int 0) (.local tlo)) (← slice (.local thi) len))))), r.ty⟩
  -- every occurrence of `x`, removed or replaced: never failing
  | "RemoveAllElements", [x] | "ReplaceAllElements", [x, _] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t s!"the element type of {m}")
    let rx ← elabE ctx x (some t)
    let tx ← fresh t
    let te ← fresh t
    let setX := Expr.assign tx (← coerce p rx t)
    match m, args with
    | "ReplaceAllElements", [_, y] =>
      let ry ← elabE ctx y (some t)
      let ty ← fresh t
      return ⟨.seq start (.seq setX (.seq (.assign ty (← coerce p ry t))
        (.forE te (.local ta) (.lit .void)
          (.ite (p2 .eq (.local te) (.local tx)) (.local ty) (.local te))))), r.ty⟩
    | _, _ =>
      return ⟨.seq start (.seq setX (.forE te (.local ta) (p2 .ne (.local te) (.local tx)) (.local te))), r.ty⟩
  -- `A.ReplaceAll(Pattern, Replacement)`: a helper written in Verse
  | "ReplaceAll", [pat, rep] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t "the element type of ReplaceAll")
    let nm := s!"$receiver{ta}"
    let c2 := { ctx with locals := { name := nm, slot := ta, ty := r.ty, mutable := false } :: ctx.locals }
    let rc ← elabApp c2 p (.ident p "$replaceAll") [.ident p nm, pat, rep] false (some r.ty)
    return ⟨.seq start rc.e, r.ty⟩
  | _, _ => eerr p s!"unknown array method '{m}' with {args.length} argument(s) (openverse supports Slice, Find, RemoveFirstElement, RemoveElement, Remove, RemoveAllElements, ReplaceFirstElement, ReplaceElement, ReplaceAllElements, ReplaceAll, Insert, Last)"

/-- `A[i]` on an array (failable) or `T(k)` on a tuple. -/
partial def elabIndexLike (ctx : Ctx) (p : Pos) (r : R) (args : List SExpr) (bracket : Bool) : EM R := do
  -- a call of a function value (#210): of its shape's method
  if let .struct n _ := r.ty then
    if let some (_, effs) := FnValues.parseName n then
      if effs.contains "decides" && !bracket then
        eerr p s!"a value of type {r.ty.show} can fail: call it with […]"
      if !effs.contains "decides" && bracket then
        eerr p s!"a value of type {r.ty.show} cannot fail: call it with (…)"
      if effs.contains "suspends" && !ctx.suspends then
        eerr p s!"a value of type {r.ty.show} suspends: it can only be called in a <suspends> function (#156)"
      -- (one tuple argument flattens into several parameters)
      let k := (FnValues.parseName n).elim 0 (·.1)
      if args.length != k && !(args.length == 1 && k > 1) then
        eerr p s!"a value of type {r.ty.show} takes {k} argument(s), found {args.length}"
      let t ← fresh r.ty
      let nm := s!"$fnval{t}"
      let ctx' := { ctx with locals := { name := nm, slot := t, ty := r.ty, mutable := false } :: ctx.locals }
      let rc ← elabApp ctx' p (.member p (.ident p nm) (FnValues.callOf n)) args bracket none
      return ⟨.seq (.assign t r.e) rc.e, rc.ty⟩
  match r.ty, args, bracket with
  | .arr t, [i], true =>
    let ri := widenR ctx.types (← elabE ctx i (some .int))
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

/-- Two types with an int in one where the other has a rational, at the
    same place inside them (#116). -/
partial def ratMismatch : Ty → Ty → Bool
  | .int, .rational | .rational, .int => true
  | .arr a, .arr b | .opt a, .opt b => ratMismatch a b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).any fun (a, b) => ratMismatch a b
  | .tup as, .arr b | .arr b, .tup as => as.any (ratMismatch · b)
  | .map k v, .map k' v' => ratMismatch k k' || ratMismatch v v'
  | .struct a as, .struct b bs => a == b && as.length == bs.length && (as.zip bs).any fun (x, y) => ratMismatch x y
  | _, _ => false

/-- Two different scalar types at the same place inside two types (#127):
    `1 = 1.0` or `array{1} = array{'a'}` would compare values Verse Core
    holds differently, always unequal. -/
partial def scalarMismatch : Ty → Ty → Bool
  | .arr a, .arr b | .opt a, .opt b => scalarMismatch a b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).any fun (a, b) => scalarMismatch a b
  | .tup as, .arr b | .arr b, .tup as => as.any (scalarMismatch · b)
  | .map k v, .map k' v' => scalarMismatch k k' || scalarMismatch v v'
  | .struct a as, .struct b bs => a == b && as.length == bs.length && (as.zip bs).any fun (x, y) => scalarMismatch x y
  | a, b =>
    let scalar : Ty → Bool := fun
      | .int | .logic | .char | .char32 | .rational | .float | .enum _ => true
      | _ => false
    scalar a && scalar b && !(a == b)

/-- A call of a rational helper (#116), `$ratMake` or `$ratLt`. -/
partial def ratCall (ctx : Ctx) (p : Pos) (f : String) (args : List Expr) : EM Expr := do
  let some s := ctx.sig? f | eerr p "internal error: the rational helpers are missing"
  return .call s.idx args

/-- The test of `x op y`, where one operand is a rational and the other an
    int or a rational (#116): it fails when the comparison does not hold.
    Rationals are in lowest terms, so `=` and `<>` are the tuples'; an
    ordering is `$ratLt`'s. -/
partial def ratTest (ctx : Ctx) (p : Pos) (op : String) (x y : R) : EM Expr := do
  let asRat (r : R) : EM Expr := match r.ty with
    | .rational => pure r.e
    | .int => pure (.prim .mkTup [r.e, .lit (.int 1)])
    | t => eerr p s!"'{op}' compares a rational with an int or a rational, not with {t.show}"
  let xa ← asRat x
  let ya ← asRat y
  match op with
  | "=" => return p2 .eq xa ya
  | "<>" => return p2 .ne xa ya
  | "<" => ratCall ctx p "$ratLt" [xa, ya]
  | ">" => ratCall ctx p "$ratLt" [ya, xa]
  | "<=" => return Expr.notE (← ratCall ctx p "$ratLt" [ya, xa])
  | _ => return Expr.notE (← ratCall ctx p "$ratLt" [xa, ya])

partial def elabCmp (ctx : Ctx) (p : Pos) (a : SExpr) (rest : List (String × SExpr)) : EM R := do
  let opOf : String → Prim
    | "=" => .eq | "<>" => .ne | "<" => .lt | "<=" => .le | ">" => .gt | _ => .ge
  -- (the orderings of floats are IEEE's, #127: false on NaN)
  let ordOf (op : String) (t : Ty) : Prim :=
    if t == .float then
      match op with
      | "<" => .flt | "<=" => .fle | ">" => .fgt | ">=" => .fge | _ => opOf op
    else opOf op
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
      -- (nor an int with a rational inside containers, #116: equal values
      -- that Verse Core holds differently, `1` and `(1, 1)`)
      if ratMismatch ta tb then
        eerr p s!"'{op}' compares values of different types, {ta.show} and {tb.show} (an int and a rational inside them: convert the ints first)"
      if scalarMismatch ta tb then
        eerr p s!"'{op}' compares values of different types, {ta.show} and {tb.show}"
    else if !((ta == .int && tb == .int) || (ta == .char && tb == .char) || (ta == .char32 && tb == .char32) ||
        (ta == .float && tb == .float)) then
      eerr p s!"'{op}' compares ints, chars, char32s or floats, found {ta.show} and {tb.show}"
  let ra := widenR ctx.types (← elabE ctx a none)
  -- (an array and a tuple compare as arrays: the tuple is converted)
  let asArr (r : R) (other : Ty) : EM R := do
    match r.ty, other with
    | .tup _, .arr _ => return ⟨← coerce p r other, other⟩
    | _, _ => return r
  match rest with
  | [(op, b)] =>
    let rb := widenR ctx.types (← elabE ctx b (some ra.ty))
    if ra.ty == .rational || rb.ty == .rational then
      let ta ← fresh ra.ty
      let tb ← fresh rb.ty
      let test ← ratTest ctx p op ⟨.local ta, ra.ty⟩ ⟨.local tb, rb.ty⟩
      return ⟨.seq (.assign ta ra.e) (.seq (.assign tb rb.e) (.seq test (.local ta))), ra.ty⟩
    let ra ← asArr ra rb.ty
    let rb ← asArr rb ra.ty
    checkTys op ra.ty rb.ty
    return ⟨p2 (ordOf op ra.ty) ra.e rb.e, ra.ty⟩
  | _ =>
    -- a chain: each operand is evaluated once, every adjacent pair is checked,
    -- and the result is the leftmost operand (Book of Verse §5.4)
    let t0 ← fresh ra.ty
    let mut prev := t0
    let mut prevTy := ra.ty
    let mut steps : Array Expr := #[.assign t0 ra.e]
    for (op, b) in rest do
      let rb := widenR ctx.types (← elabE ctx b (some prevTy))
      let rb ← asArr rb prevTy
      -- (the previous operand, as an array when this one is)
      let prevE ← match prevTy, rb.ty with
        | .tup _, .arr _ => coerce p ⟨.local prev, prevTy⟩ rb.ty
        | _, _ => pure (.local prev)
      let tb ← fresh rb.ty
      if prevTy == .rational || rb.ty == .rational then
        steps := steps.push (.assign tb rb.e)
        steps := steps.push (← ratTest ctx p op ⟨.local prev, prevTy⟩ ⟨.local tb, rb.ty⟩)
      else
        checkTys op (match prevTy, rb.ty with | .tup _, .arr _ => rb.ty | _, _ => prevTy) rb.ty
        steps := steps.push (.assign tb rb.e)
        steps := steps.push (p2 (ordOf op prevTy) prevE (.local tb))
      prev := tb
      prevTy := rb.ty
    return ⟨steps.foldr Expr.seq (.local t0), ra.ty⟩

partial def elabSet (ctx : Ctx) (p : Pos) (lhs0 : SExpr) (op : Option String) (rhs0 : SExpr) : EM R := do
  -- (`$withOld(O, R)`: for `op=`, the old value was read into `O` before
  -- the code that computes `R`, as `set` evaluates, #208)
  let (rhs, oldIn) : SExpr × Option Expr := match rhs0 with
    | .app _ (.ident _ "$withOld") [.ident _ o, r] false => (r, (ctx.lookup o).map (fun l => Expr.local l.slot))
    | r => (r, none)
  -- the right side at the target's type; for `set F *= N` of a float, an
  -- int too (#127), so without it when that fails
  let rhsAt (t : Ty) : EM R :=
    if op == some "*" && t == .float then
      tryCatch (elabE ctx rhs (some t)) fun _ => elabE ctx rhs none
    else elabE ctx rhs (some t)
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
  let combine (old0 : Expr) (ty : Ty) (o : String) (new0 : R) : EM Expr := do
    let old := oldIn.getD old0
    -- (a refinement's value is its base; a refined variable is set only
    -- through a cast, #136)
    let new := widenR (← get).env new0
    if let .refine n := ty then
      eerr p s!"set {o}= on {withArticle n} needs a cast: write set X = {n}[X {o} …], which fails when the result is not one"
    match o, ty, new.ty with
    | "+", .int, .int => pure (p2 .add old new.e)
    | "-", .int, .int => pure (p2 .sub old new.e)
    | "*", .int, .int => pure (p2 .mul old new.e)
    | "+", .arr t, .arr u => do
        if t == u then pure (p2 .concat old new.e)
        else if refUp (← get).env (.arr u) (.arr t) then pure (p2 .concat old (← coerce p new (.arr t)))
        else eerr p s!"cannot concatenate {ty.show} and {new.ty.show}"
    -- floats (#127)
    | "+", .float, .float => pure (p2 .fadd old new.e)
    | "-", .float, .float => pure (p2 .fsub old new.e)
    | "*", .float, .float => pure (p2 .fmul old new.e)
    | "*", .float, .int => pure (p2 .fmul old (.prim .fofInt [new.e]))
    | "/", .float, .float => pure (p2 .fdiv old new.e)
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
    -- `X?`: the value inside an option; fails when empty
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
      | _, _ => eerr p "internal: set path"
    if refLevel?.isNone && !l.mutable then
      eerr p s!"'{root}' is not a var; declare it with var {root}:t = …"
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
    -- a value of a class with no instance cannot exist, so the set is
    -- unreachable once the path reaches one; but the steps before it (the
    -- indices and keys, then the containers read) may fail first (#104)
    if let some ke := (List.range steps.length).find? fun k =>
        match tysA[k]! with | .struct sn _ => ctx.types.isEmptyClass sn | _ => false then
      let stepsA := steps.toArray
      let mut c := l.slot
      for k in [0:ke] do
        let (_, f?, _) := stepsA[k]!
        let c' ← fresh tysA[k + 1]!
        pre := pre.push (.assign c' (← readStep c tysA[k]! f? keys[k]!))
        c := c'
      -- (the right-hand side never runs, but is checked, and the field set
      -- at the empty class must be a var, as on any path)
      let lastCls := (List.range steps.length).reverse.find? fun k =>
        match tysA[k]!, stepsA[k]! with
        | .struct sn _, (_, some f, _) => f != "?" && ctx.types.classes.contains sn
        | _, _ => false
      if let some kc := lastCls then
        if let (.struct sn _, (sp, some f, _)) := (tysA[kc]!, stepsA[kc]!) then
          if !ctx.types.isVarField sn f then eerr sp (classSetMsg sn f)
      let r ← rhsAt leafTy
      match op with
      | none => discard <| coerce p r leafTy
      | some o => discard <| combine (.prim .userErr []) leafTy o r
      let tu ← fresh leafTy
      return ⟨pre.toList.foldr Expr.seq (.assign tu (.prim .userErr [])), leafTy⟩
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
    let mut oldLeaf : Option Nat := none
    for k in [0:stepsA.size] do
      let (sp, f?, _) := stepsA[k]!
      levels := levels.push (cur, tys[k]!, sp, f?, keys[k]!)
      if k == rhsAfter then
        -- `set P op= e` reads P before e, as the direct form does (Book of
        -- Verse: `set X += e` is `set X = X + e`; #58): the rest of the path,
        -- read now, gives the old leaf (it fails as `P` would, and is read
        -- again for the rebuild below)
        if op.isSome then
          let mut c2 := cur
          for k2 in [k:stepsA.size] do
            let (_, f2, _) := stepsA[k2]!
            let t2 := if k2 + 1 < stepsA.size then tys[k2 + 1]! else leafTy
            let c3 ← fresh t2
            pre := pre.push (.assign c3 (← readStep c2 tys[k2]! f2 keys[k2]!))
            c2 := c3
          oldLeaf := some c2
        let r ← rhsAt leafTy
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
      | none => rhsAt leafTy
    let leaf ← match op with
      | none => coerce p r leafTy
      | some o =>
        -- (only an `op=` reads the old value: a read can have an effect)
        let old ← match oldLeaf with
          | some t => pure (Expr.local t)
          | none => readStep lc lty lf lkey
        combine old leafTy o r
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
          let (j, ft) := (fieldIndex (ctx.types.fields sn targs) f).get!
          pre := pre.push (← setFieldAt ctx.types p sn targs c f j ft newVal)
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
    let r ← rhsAt l.ty
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
      let r ← rhsAt vt
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
      let ri := widenR ctx.types (← elabE ctx i (some .int))
      if ri.ty != .int then eerr p "an array index must be an int"
      let ti ← fresh .int
      let tv ← fresh t
      let r ← rhsAt t
      let v ← match op with
        | none => coerce p r t
        | some o => combine (p2 .index (.local l.slot) (.local ti)) t o r
      -- `set A[i] = v` fails out of range and returns `v` (Book of Verse §3.3)
      return ⟨.seq (.assign ti ri.e)
        (.seq (.assign l.slot (.prim .arrSet [.local l.slot, .local ti, .assign tv v])) (.local tv)), t⟩
    | ty => eerr p s!"cannot index a value of type {ty.show}"
  | .member _ (.ident _ n) f =>
    -- an object's field: written in place, through any variable (#34)
    if let some l := ctx.lookup n then
      if let .struct sn _ := l.ty then
        if ctx.types.isRefClass sn then
          let targs := match l.ty with | .struct _ ts => ts | _ => []
          let some (k, t) := fieldIndex (ctx.types.fields sn targs) f
            | eerr p s!"class {sn} has no field '{f}'"
          if !ctx.types.isVarField sn f then eerr p (classSetMsg sn f)
          let r ← rhsAt t
          noteFx p (if op.isSome then ["reads", "writes"] else ["writes"])
          let v ← match op with
            | none => coerce p r t
            -- (the current value, read as a read does)
            | some o => combine (← elabMember ctx p ⟨.local l.slot, l.ty⟩ f).e t o r
          return ⟨← setFieldAt ctx.types p sn targs l.slot f k t v, t⟩
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
        let r ← rhsAt t
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
  -- (a choice is a generator over its alternatives, #208)
  let clauses := Choice.prepare clauses (choiceValues ctx) (choiceField ctx)
  -- (a call of a recursive function with several values, #235: a generator
  -- over the array of its values; at a written type, through a binding)
  let clauses := clauses.flatMap fun c => match Choice.binding? c with
    | some { pos := q, name := n, ty := none, each := some arr, .. } => [.gen q n none arr]
    | some { pos := q, name := n, ty := some t, each := some arr, .. } =>
      let tmp := s!"$e{q.line}_{q.col}"
      [.gen q tmp none arr, .decl q n (some t) false (.ident q tmp)]
    | _ => [c]
  -- split into groups: [filters before the first generator], then (generator, filters)…
  let isGen : SExpr → Bool
    | .gen .. => true
    | .decl _ _ none false (.range ..) => true
    | c => (Choice.binding? c).isSome
  let pre := clauses.takeWhile (!isGen ·)
  let rest := clauses.dropWhile (!isGen ·)
  let rec groups : List SExpr → List (SExpr × List SExpr)
    | [] => []
    | g :: cs =>
      let fs := cs.takeWhile (!isGen ·)
      (g, fs) :: groups (cs.dropWhile (!isGen ·))
  let gs := groups rest
  let bodyCtx (c : Ctx) : Ctx := { c with canFail := ctx.canFail, inLoop := false, inRepeat := true }
  -- elaborate the filters of one generator (in a failure context)
  let elabFilters (c : Ctx) (fs : List SExpr) : EM (Expr × Ctx) := do
    match fs with
    | [] => return (.lit (.logic true), c)
    | _ =>
      let (r, c') ← elabSeq { c with canFail := true, inTaking := true } fs none
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
          let es ← elabInts { c with canFail := true, inTaking := true } gp [lo, hi]
          let (slot, c1) ← declare c n .int
          pure (slot, Expr.prim .range es, c1, Expr.lit (.logic true))
        | .gen gp x idx srcE => do
          let rs ← elabE { c with canFail := true, inTaking := true } srcE none
          match rs.ty with
          | .map kt vt =>
            -- `for (V : M)` and `for (K -> V : M)`: over the (key, value) pairs
            let tmp ← fresh rs.ty
            let src := if (rs.e.mayFail ctx.sigProg) then
                Expr.orE tmp rs.e (.lit (.arr #[])) else rs.e
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
                Expr.orE tmp rs.e (.lit (.arr #[])) else rs.e
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
              Expr.orE tmp rs.e (.lit (.arr #[])) else rs.e
          let (slot, c1) ← declare c x ty
          pure (slot, src, c1, Expr.lit (.logic true))
        | .decl gp n _ false _ => do
          -- `X := a₁ | … | aₙ` (#208): over the alternatives' indices, each
          -- alternative bound in the filter (so a failing one is skipped)
          let some b := Choice.binding? g | eerr g.pos "bad for clause"
          -- (an `if` with choices in its branches picks its branch first, once, #235)
          let (pre, ty, es) ← match b.branchy with
            | some i => elabBranchAlts { c with canFail := true, inTaking := true } gp i b.ty b.place
            | none => do let (ty, es) ← elabAlts { c with canFail := true } gp b; pure (none, ty, es)
          checkNewLocal c gp n
          let k ← fresh .int
          let (xs, c1) ← declare c n ty
          let idx := Expr.lit (.arr (choiceIdx es.length))
          pure (k, (pre.map (Expr.seq · idx)).getD idx, c1, Expr.assign xs (Expr.altE k es))
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
    | [] => return ⟨.forE slot (.lit (.arr #[.tup []])) filt inner.e, .arr inner.ty⟩
    | _ =>
      match inner.ty with
      | .arr t => return ⟨.prim .flatten [.forE slot (.lit (.arr #[.tup []])) filt inner.e], .arr t⟩
      | _ => eerr p "internal: nested for"

/-- An `if … else if … else …` with choices in its branches (#235): code that
    picks the branch, once, into a fresh slot (each condition a failure
    context of its own, tried when the ones before failed), and every
    branch's alternatives guarded by it (`B = j; a`), each seeing the names
    its conditions bind, at their written type or their join. -/
partial def elabBranchAlts (ctx : Ctx) (p : Pos) (i : SExpr) (sty : Option STy) (place : Option SExpr := none) :
    EM (Option Expr × Ty × List Expr) := do
  let arms := Choice.arms i
  let bi ← fresh .int
  let mut conds : Array (Option Expr) := #[]
  let mut ctxs : Array Ctx := #[]
  for (cs?, _) in arms do
    match cs? with
    | some cs =>
      let (rc, cT) ← if Choice.hasChoice cs then elabOneClauses { ctx with canFail := true } cs
        else elabSeq { ctx with canFail := true, inTaking := true } cs none
      if !(rc.e.mayFail ctx.sigProg) && (← get).fnNeeds.isEmpty then
        eerr p "the condition of this if cannot fail (Verse requires a failable condition)"
      conds := conds.push (some rc.e)
      ctxs := ctxs.push { cT with canFail := ctx.canFail, inTaking := ctx.inTaking }
    | none =>
      conds := conds.push none
      ctxs := ctxs.push ctx
  -- (from the last branch back: `if (c₀) then B := 0 else if (c₁) then B := 1 … else B := n`)
  let setB (j : Nat) : Expr := .assign bi (.lit (.int j))
  let pick := (conds.toList.zipIdx).foldr (fun (c?, j) acc => match c? with
    | some c => Expr.ite c (setB j) acc
    | none => setB j) (.lit .void)
  -- (the written type, or for `set L = if …` the type of `L`)
  let t? ← match ← sty.mapM (resolveTy ctx.types p) with
    | some t => pure (some t)
    | none => match place with
      | some l => tryCatch (do pure (some (← elabE ctx l none).ty)) fun _ => pure none
      | none => pure none
  let mut rs : Array (Nat × SExpr × R) := #[]
  for ((_, arm), j) in arms.zipIdx do
    let c := ctxs.getD j ctx
    for a in (Choice.alts? arm).getD [arm] do
      -- (without a type, each later one against the first's, else on its
      -- own, as `elabAlts` does, #32)
      let r ← match t?, rs[0]? with
        | some t, _ => elabE c a (some t)
        | none, none => elabE c a none
        | none, some (_, _, r0) =>
          if c.retries ≥ 3 then tryCatch (elabE c a none) fun _ => elabE c a (some r0.ty)
          else
            let c2 := { c with retries := c.retries + 1 }
            tryCatch (elabE c2 a (some r0.ty)) fun _ => elabE c2 a none
      rs := rs.push (j, a, r)
  let some (_, _, r0) := rs[0]? | eerr p "internal: an if without branches"
  let ty ← match t? with
    | some t => pure t
    | none => rs.toList.foldlM (fun acc (_, _, r) => join p acc r.ty none) r0.ty
  if ty == .never then eerr p "cannot infer the type of this if's choices"
  let es ← rs.toList.mapM fun (j, a, r) => do
    return Expr.seq (.prim .eq [.local bi, .lit (.int j)]) (← coerce a.pos r ty)
  return (some pick, ty, es)

/-- The alternatives of a choice (#208), at its written type or at their
    join (each one against the first's type, else on its own, as `if`'s
    branches are), and that type. -/
partial def elabAlts (ctx : Ctx) (p : Pos) (b : Choice.Binding) : EM (Ty × List Expr) := do
  -- (a choice or a call with several values left in an alternative is in a
  -- failure context that takes values, where it cannot be lifted from)
  let ctx := { ctx with inTaking := true }
  let alts := b.alts
  -- (the written type, or for `set L = a | b` the type of `L`)
  let t? ← match ← b.ty.mapM (resolveTy ctx.types p) with
    | some t => pure (some t)
    | none => match b.place with
      | some l => tryCatch (do pure (some (← elabE ctx l none).ty)) fun _ => pure none
      | none => pure none
  match t? with
  | some t => return (t, ← alts.mapM fun a => do coerce a.pos (← elabE ctx a (some t)) t)
  | none =>
    let some a0 := alts.head? | eerr p "internal: a choice without alternatives"
    let r0 ← elabE ctx a0 none
    -- (each later one against the first's type, else on its own, to join;
    -- a few levels deep, then on its own first, as the join needs, #32)
    let rs ← alts.tail.mapM fun a =>
      if ctx.retries ≥ 3 then tryCatch (elabE ctx a none) fun _ => elabE ctx a (some r0.ty)
      else
        let c2 := { ctx with retries := ctx.retries + 1 }
        tryCatch (elabE c2 a (some r0.ty)) fun _ => elabE c2 a none
    let ty ← rs.foldlM (fun acc r => join p acc r.ty none) r0.ty
    if ty == .never then eerr p "cannot infer the type of this choice"
    return (ty, ← ((alts.zip (r0 :: rs)).mapM fun (a, r) => coerce a.pos r ty))

/-- The clauses of a failure context that takes its first success (an `if`
    condition, `first{…}`), when one of them binds a choice (#208):
    `Expr.firstE` over the clauses, each choice an `Expr.chooseFirst` around
    the clauses after it, which `break` when all of them succeed. Its value is
    `void`: an `if` and `first{…}` read their clauses' values through names. -/
partial def elabOneClauses (ctx : Ctx) (cs : List SExpr) : EM (R × Ctx) := do
  -- (a `break` here would leave `firstE`'s loop, not the program's)
  let (code, ctx') ← elabOneGo { ctx with inLoop := false, inChoice := ctx.inLoop, inTaking := true }
    (Choice.prepare cs (choiceValues ctx) (choiceField ctx))
  return (⟨Expr.firstE code, .void⟩, { ctx' with inLoop := ctx.inLoop, inChoice := ctx.inChoice, inTaking := ctx.inTaking })

partial def elabOneGo (ctx : Ctx) : List SExpr → EM (Expr × Ctx)
  | [] => return (Expr.brkV, ctx)
  | cl :: rest => do
    if let .app p (.ident _ "$defer") _ _ := cl then
      eerr p "defer: cannot be a clause of an if condition or first{…} that has a choice (#208)"
    match Choice.binding? cl with
    | some b@{ each := some arr, .. } =>
      -- (a call of a recursive function with several values, #235: each
      -- element of the array of its values in turn, the clauses after it
      -- in the filter, as `chooseFirst` does with alternatives)
      let p := b.pos
      let ra ← elabE ctx arr none
      let ety ← match ra.ty with
        | .arr t => pure t
        | t => eerr p s!"internal: the values of a call are {t.show}"
      let ty ← match ← b.ty.mapM (resolveTy ctx.types p) with
        | some t => pure t
        | none => pure ety
      checkNewLocal ctx p b.name
      let e ← fresh ety
      let x ← fresh ty
      let c1 := { ctx with locals := { name := b.name, slot := x, ty, mutable := false } :: ctx.locals }
      let (inner, c2) ← elabOneGo c1 rest
      let bindX ← coerce p ⟨.local e, ety⟩ ty
      return (.forE e ra.e (.seq (.assign x bindX) (.seq inner Expr.failV)) (.lit .void), c2)
    | some b =>
      let p := b.pos
      let n := b.name
      let (pre, ty, es) ← match b.branchy with
        | some i => elabBranchAlts ctx p i b.ty b.place
        | none => do let (ty, es) ← elabAlts ctx p b; pure (none, ty, es)
      checkNewLocal ctx p n
      let k ← fresh .int
      let x ← fresh ty
      let c1 := { ctx with locals := { name := n, slot := x, ty, mutable := false } :: ctx.locals }
      let (inner, c2) ← elabOneGo c1 rest
      let code := Expr.chooseFirst k x es inner
      return ((pre.map (Expr.seq · code)).getD code, c2)
    | none =>
      let (r, c1) ← elabStmt ctx cl none
      let (inner, c2) ← elabOneGo c1 rest
      return (.seq r.e inner, c2)

/-- `e.m`: `.Length` of an array or string, or a field of a struct. -/
partial def elabMember (ctx : Ctx) (p : Pos) (r : R) (m : String) (exp : Option Ty := none) : EM R := do
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
        -- (where every class below has it, so does every placeholder below,
        -- even when that is not `k`: an interface listed after another,
        -- #157; and with one type in all of them, #205)
        let env := ctx.types
        let p0 := pos.headD k
        let tyOK := env.fieldTyAgrees sn targs f
        if tyOK && pos.all (· == p0) then return ⟨.heap (.get p0) [r.e], t⟩
        if let some d := ds.find? fun d => !env.sameCore d sn && (env.fieldAcc.idxOf? (d, f)).isNone then
          if !tyOK then
            eerr p s!"field '{f}' of {sn} has another type in {d}, which takes it from another interface, and {d} has type parameters that {sn} does not have: reading it through {sn} is not supported yet (#205)"
          eerr p s!"field '{f}' of {sn} sits at different places in the classes below it, and {d} has type parameters that {sn} does not have: reading it is not supported yet (#53, #157)"
        let x ← fresh r.ty
        let mut acc : Expr := .prim .userErr []   -- no class: unreachable
        let mut refined := false
        for (d, kd) in (ds.zip pos).reverse do
          match env.fieldAcc.idxOf? (d, f) with
          | some i =>
            -- (a class that fixes the type arguments: its getter, under the
            -- refinement, #157)
            acc := .ite (.heap (.isTag [env.tagOf d]) [.local x]) (.call (env.fieldAccBase + 2 * i) [.local x]) acc
            refined := true
          | none =>
            let yd ← fresh (.struct d (env.argsAt sn targs d))
            acc := .ite (.assign yd (.heap (.isTag [env.tagOf d]) [.local x])) (.heap (.get kd) [.local yd]) acc
        if refined then
          -- (checked against the field's type, as the refined calls need one)
          let y ← fresh t
          return ⟨.seq (.assign x r.e) (.assign y acc), t⟩
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
        if f.startsWith "(" then
          eerr p s!"X.{f}, a qualified method, cannot be used as a value: call it with X.{f}(…) (#210)"
        -- (a method that a class below overloads is renamed, #106: one
        -- overload visible here is still a value; more are overloaded)
        let visibleOv := ((ctx.types.methodOverloads.lookup f).getD []).filter (ctx.hasMethod sn ·)
        if visibleOv.length > 1 then
          eerr p s!"'{f}' is an overloaded method of {sn}: an overloaded method cannot be used as a value (Book of Verse ch. 6)"
        let hasValue := (ctx.types.supers sn).any fun x => ctx.types.classes.contains s!"{x}${f}$fn"
        if ctx.hasMethod sn f || (visibleOv.length == 1 && hasValue) then
          -- a method as a value (#210): an object of the value class of the
          -- nearest class that declares or overrides it (#219: an override
          -- may narrow the result), holding the receiver, of its type, or
          -- of a class further up whose type is the one expected
          let env := ctx.types
          -- (one implementation per class below, as a call needs, #70; of
          -- the overload visible here, as a class below renamed it, #106)
          let fv := if ctx.hasMethod sn f then f else visibleOv.headD f
          let roots := ctx.rootsOf sn fv
          if let some root := roots.head? then
            for d in env.concreteBelow sn do
              for o in roots do
                if ctx.implFor? d o fv != ctx.implFor? d root fv then
                  eerr p s!"{d} implements {f} separately for {root} and {o}, so the value {f} would not say which: call it as X.({root}:){f}(…) or X.({o}:){f}(…)"
          let typeOf (x : String) : Ty :=
            let cls := s!"{x}${f}$fn"
            let i := (env.info cls).ifaces.headD ""
            let σ := (((env.sparams.lookup cls).getD []).map (·.1)).zip (env.argsAt sn targs x)
            .struct i (((env.iargs.lookup (cls, i)).getD []).map (Ty.subst σ))
          let candidates := (env.supers sn).filter fun x => env.classes.contains s!"{x}${f}$fn"
          -- (#231) wanted at a closed function type that no value class of
          -- it gives but that it fits by variance: a class made for that type,
          -- `{x}${f}$fn${k}` (the nearest class's, without type parameters),
          -- holding the receiver; asked for the first time (a placeholder,
          -- and the program is elaborated again with the class made)
          if let some t@(.struct tm tts) := exp then
            if (FnValues.parseName tm).isSome && (tts.all fun u => u.params.isEmpty) &&
                !(candidates.any fun x => typeOf x == t) then
              if let some x0 := candidates.head? then
                if ((env.sparams.lookup s!"{x0}${f}$fn").getD []).isEmpty then
                  let variantTy (c : String) : Ty :=
                    let i := (env.info c).ifaces.headD ""
                    .struct i ((env.iargs.lookup (c, i)).getD [])
                  match env.classes.find? (fun c => c.startsWith s!"{x0}${f}$fn$" && variantTy c == t) with
                  | some vc =>
                    let tv ← fresh r.ty
                    let nm := s!"$recv{tv}"
                    let ctx' := { ctx with locals := { name := nm, slot := tv, ty := r.ty, mutable := false } :: ctx.locals }
                    let rv ← elabConstruct ctx' p vc [] [.decl p "$self" none false (.ident p nm)] (some (.struct vc []))
                    return ⟨.seq (.assign tv r.e) (← coerce p rv t), t⟩
                  | none =>
                    let key := s!".{x0}${f}"
                    if !env.fnRequests.contains (key, t) && fnTyFits env (typeOf x0) t then
                      modify fun st => { st with fnNeeds := st.fnNeeds ++ [(key, t)] }
                      return ⟨.seq r.e (.prim .userErr []), t⟩
          let some x := (candidates.find? fun x => exp == some (typeOf x)).orElse fun _ => candidates.head?
            | eerr p s!"'{f}' is a method of {sn} that cannot be used as a value: call it with {f}(…) (a generic method, one with named parameters, and one whose type does not mention each of its class's type parameters once, as a whole parameter or result type, are no values, #210)"
          let cls := s!"{x}${f}$fn"
          let xargs := env.argsAt sn targs x
          let t ← fresh r.ty
          let nm := s!"$recv{t}"
          let ctx' := { ctx with locals := { name := nm, slot := t, ty := r.ty, mutable := false } :: ctx.locals }
          let rv ← elabConstruct ctx' p cls [] [.decl p "$self" none false (.ident p nm)] (some (.struct cls xargs))
          let own := typeOf x
          return ⟨.seq (.assign t r.e) (← coerce p rv own), own⟩
        if visibleOv.length == 1 then
          eerr p s!"'{f}' is a method of {sn} that cannot be used as a value: call it with {f}(…) (a generic method, one with named parameters, and one whose type does not mention each of its class's type parameters once, as a whole parameter or result type, are no values, #210)"
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
        -- (and so does a pinned class's, whose pins may be on more type
        -- arguments than the type it is used at, #209)
        if tas.isEmpty && (ctx.types.corePins name).isEmpty then return ⟨.heap (.new (ctx.types.tagOf name)) es, ty⟩
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
    | some k, some v => return ⟨.lit (.arr #[]), .map k v⟩
    | _, _ => eerr p "the type of an empty map{} must be given (e.g. M:[string]int = map{})"
  | (k0, v0) :: _ =>
    let rk0 ← elabE ctx k0 kt?
    let rv0 ← elabE ctx v0 vt?
    let kt := kt?.getD rk0.ty
    if !kt.comparable ctx.types then eerr p (notComparable ctx.types kt "a map key")
    let vt0 := vt?.getD rv0.ty
    let mut rs : Array (SExpr × R × SExpr × R) := #[]
    for (k, v) in entries do
      rs := rs.push (k, ← elabE ctx k (some kt), v, ← elabE ctx v (some vt0))
    -- the values' type: the expected one (or the first's) when every value
    -- converts to it, else their join, as for an array literal (#67)
    let vt ← match ← tryCatch (some <$> rs.toList.mapM fun (_, _, v, rv) => coerce v.pos rv vt0) (fun _ => pure none) with
      | some _ => pure vt0
      | none => rs.toList.foldlM (fun acc (_, _, v, rv) => do
          match joinTy (← get).env acc rv.ty vt? with
          | some j => pure j
          | none => eerr v.pos s!"the values of this map have different types: {acc.show} and {rv.ty.show}") rv0.ty
    let mut steps : Array Expr := #[]
    let mut slots : Array (Nat × Nat) := #[]
    for (k, rk, v, rv) in rs do
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
      Expr.ite cond (.prim .mkArr [.prim .mkTup [.local tk, .local tv]]) (.lit (.arr #[]))
    let built := Expr.prim .flatten [.prim .mkArr items]
    return ⟨steps.toList.foldr Expr.seq built, .map kt vt⟩

partial def elabCase (ctx : Ctx) (p : Pos) (scrut : SExpr) (arms : List (Option SExpr × SExpr))
    (exp : Option Ty) : EM R := do
  let rs := widenR ctx.types (← elabE ctx scrut none)
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
        -- (a pattern is tested in a condition, #156)
        if Suspend.hasSusp (fun f => ctx.sigs.any fun s => s.idx == f && s.suspends) rp.e then
          eerr pe.pos "a case pattern cannot suspend: it is tested as a condition (#156)"
        results := results.push (some rp.e, rv)
    let mut ty : Ty := .never
    for (_, rv) in results do ty ← join p ty rv.ty exp
    let hasDefault := results.any (·.1.isNone)
    -- an enum case that names every enumerator needs no `_` (Book of Verse
    -- §7.6), unless the enum is open: it may gain values (ch. 9)
    let exhaustive := match rs.ty with
      | .enum n =>
        !ctx.types.openEnums.contains n &&
        let k := ((ctx.types.enums.lookup n).getD []).length
        (List.range k).all fun i => results.any fun (pat, _) => match pat with
          | some (.lit (.int j)) => j == i
          | _ => false
      | _ => false
    let mut acc : Expr ← if hasDefault then pure (.lit .void) else
      if exhaustive then pure (.prim .userErr [])   -- unreachable
      else if ctx.canFail then pure (.prim .fail [])
      else match rs.ty with
        | .enum n =>
          if ctx.types.openEnums.contains n then
            eerr p s!"a case on the open enum {n} needs _ (it may gain values), unless failure is allowed (e.g. in a <decides> function)"
          else eerr p "a case without _ is only allowed where failure is (e.g. a <decides> function), or on an enum when every value is named"
        | _ => eerr p "a case without _ is only allowed where failure is (e.g. a <decides> function), or on an enum when every value is named"
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
  /-- Functions wanted as values at closed function types no class of
      theirs gives (#214): the program is elaborated again, with them. -/
  fnNeeds : List (String × Ty) := []
  /-- Branches of casts that refine type arguments, to lift (#243): the
      program is elaborated again, with them. -/
  castNeeds : List Refine.Lift := []

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

/-- How a program is compiled from the command line: its shell arguments,
    bound to `Args : []string` (unless the program defines `Args`), and an
    expression to run instead of `Main`. -/
structure Options where
  args : Option (List String) := none
  entry : Option SExpr := none
  /-- Functions wanted as values at closed function types no class of
      theirs gave in an earlier elaboration (#214): a class for each. -/
  fnRequests : List (String × Ty) := []
  /-- On an internal error (an elaborated function the checker rejects),
      also print that function's Verse Core, its slot types and signature,
      for a bug report (`OPENVERSE_DEBUG=1`). -/
  debug : Bool := false
  /-- Branches of casts that refine type arguments, found in an earlier
      elaboration (#243): a function for each. -/
  castRequests : List Refine.Lift := []

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

/-- The names a type mentions, in order of first occurrence. -/
partial def STy.names : STy → List String
  | .name m => [m]
  | .arr u | .opt u => u.names
  | .tup ts => (ts.flatMap STy.names).eraseDups
  | .app n ts => (n :: ts.flatMap STy.names).eraseDups
  | .map a b => (a.names ++ b.names).eraseDups
  | .fn ps _ r => ((ps ++ [r]).flatMap STy.names).eraseDups

/-- The type names `n` (a type parameter, say) somewhere. -/
partial def STy.mentions (t : STy) (n : String) : Bool := match t with
  | .name m => m == n
  | .arr u | .opt u => u.mentions n
  | .tup ts | .app _ ts => ts.any (·.mentions n)
  | .map a b => a.mentions n || b.mentions n
  | .fn ps _ r => ps.any (·.mentions n) || r.mentions n

/-- Constructor functions (#11, Book of Verse ch. 10). `K<constructor>(ps) :=
    c:` with items becomes two functions with K's parameters and effects:
    - `K$init` runs the items in order and gives the fields they set, as the
      struct `K$fields` (or nothing). An initializer `F := e` binds `F$v`, a
      `let:` its declarations, and a `block:` runs. A delegation
      `D<constructor>(args)` calls `D$init(args)` and takes D's fields.
    - `K` constructs `c` from them, the other fields taking their defaults
      (so `c`'s own `block:` clauses run last).
    A constructor sees no `Self`. -/
def expandCtors (ctors : List (Pos × String × List SParam × List TParam × List String × String × List SExpr))
    (cdef? : String → Option CDef) (fullOf : String → List (String × STy × Option SExpr × Bool))
    (supers : String → List String) (targsOf : String → List STy)
    (allTargs : List (String × List STy)) : Except String (List STop) := do
  let directOf (items : List SExpr) : List (Pos × String) := items.filterMap fun
    | .decl p f none false _ => some (p, f)
    | _ => none
  let delegsOf (items : List SExpr) : List (Pos × String) := items.filterMap fun
    | .app p (.ident _ d) _ _ => if d.startsWith "$ctor:" then some (p, (d.drop "$ctor:".length).toString) else none
    | _ => none
  -- the checks of each constructor on its own
  -- overloaded constructors (Book of Verse ch. 10, #74): one class, and the
  -- same fields, so a delegation to any of them sets the same ones
  for ((p, k, _, _, _, c, _), i) in ctors.zip (List.range ctors.length) do
    if let some (_, _, _, _, _, c', _) := (ctors.take i).find? (·.2.1 == k) then
      if c' != c then throw s!"{p.show}: the overloads of constructor {k} construct {c'} and {c}: they must construct one class"
      -- (up to the names of their type parameters: each renamed by its place)
      let norm (j : Nat) : String :=
        let ts := ((allTargs.drop j).head?.map (·.2)).getD []
        let tps := ((ctors.drop j).head?.map fun (_, _, _, t, _, _, _) => t).getD []
        let vs := (ts.flatMap STy.names).eraseDups.filter fun n => tps.any (·.name == n)
        let ρ := (vs.zip (List.range vs.length)).map fun (n, q) => (n, STy.name s!"${q}")
        reprStr (ts.map (·.substNames ρ))
      let mine := (List.range ctors.length).filter fun j => ((ctors.drop j).head?.map (·.2.1)) == some k
      if (mine.map norm).eraseDups.length > 1 then
        throw s!"{p.show}: the overloads of constructor {k} construct {c} at different type arguments: they must construct one type"
  for ((p, k, ps, tps, _, c, items), ci) in ctors.zip (List.range ctors.length) do
    let some cd := cdef? c | throw s!"{p.show}: constructor {k}: {c} is not a class"
    if cd.isIface then throw s!"{p.show}: constructor {k}: {c} is an interface"
    -- a parametric class's constructor names its type arguments, `:= box(t):`
    let targs := ((allTargs.drop ci).head?.map (·.2)).getD (targsOf k)
    if cd.tps.length != targs.length then
      if cd.tps.isEmpty then throw s!"{p.show}: constructor {k}: {c} takes no type arguments"
      else if targs.isEmpty then
        throw s!"{p.show}: constructor {k}: {c} takes {cd.tps.length} type argument(s): write {c}(…) after :="
      else throw s!"{p.show}: constructor {k}: {c} takes {cd.tps.length} type argument(s), not {targs.length}"
    -- a call infers the constructor's type parameters from its arguments
    if let some tp := tps.find? fun tp => !ps.any (·.ty.mentions tp.name) then
      throw s!"{p.show}: the type parameter {tp.name} of {k} appears in none of its parameters, so a call could not infer it"
    let direct := directOf items
    for ((fp, f), i) in direct.zip (List.range direct.length) do
      if !(fullOf c).any (·.1 == f) then throw s!"{fp.show}: {k}: {c} has no field {f}"
      if (direct.take i).any (·.2 == f) then throw s!"{fp.show}: {k} sets {f} twice"
    match delegsOf items with
    | [] => pure ()
    | [(dp, d)] =>
      let some (_, _, _, _, _, dc, _) := ctors.find? (·.2.1 == d)
        | throw s!"{dp.show}: {d} is not a constructor function"
      if !(supers c).contains dc then
        throw s!"{dp.show}: {k} constructs {c}, and {d} constructs {dc}, which is not {c} or a class above it"
      if dc == c && !direct.isEmpty then
        throw s!"{dp.show}: {k} delegates to {d}, which constructs {c} itself and so sets its fields: {k} cannot set fields too"
      -- (the Book: a subclass's fields first, then the parent's constructor)
      let dIdx := items.findIdx? fun | .app _ (.ident _ x) _ _ => x.startsWith "$ctor:" | _ => false
      let late := items.zip (List.range items.length) |>.filterMap fun
        | (.decl fp f none false _, j) => if dIdx.any (· < j) then some (fp, f) else none
        | _ => none
      if let some (fp, f) := late.head? then
        throw s!"{fp.show}: {k} sets {f} after delegating to {d}: set the fields of {c} first, then delegate"
    | _ :: (dp, _) :: _ => throw s!"{dp.show}: {k} delegates to more than one constructor"
  -- the fields each sets: its own, and its delegate's
  -- the fields each name's constructors set (#80, overloads: all their
  -- fields; one that does not set a field gives it its default, below): the
  -- least fixpoint of their own and their delegates'
  let names := (ctors.map (·.2.1)).eraseDups
  let overloaded (k : String) : Bool := (ctors.filter (·.2.1 == k)).length > 1
  let mut setBy : List (String × List String) := names.map fun k =>
    (k, ((ctors.filter (·.2.1 == k)).flatMap fun (_, _, _, _, _, _, items) => (directOf items).map (·.2)).eraseDups)
  for _ in [0:ctors.length + 1] do
    let mut changed := false
    for (_, k, _, _, _, _, items) in ctors do
      if let some (_, d) := (delegsOf items).head? then
        if d != k then
          let cur := (setBy.lookup k).getD []
          let add := ((setBy.lookup d).getD []).filter (!cur.contains ·)
          if !add.isEmpty then
            setBy := setBy.map fun (n, fs) => if n == k then (n, fs ++ add) else (n, fs)
            changed := true
    if !changed then break
  -- a delegation cycle through names that are not overloaded never ends (one
  -- through an overloaded name is resolved by its arguments, and may)
  for (p, k, _, _, _, _, items) in ctors do
    if overloaded k then continue
    let next (x : String) : Option String :=
      if overloaded x then none else
      (ctors.find? (·.2.1 == x)).bind fun (_, _, _, _, _, _, its) => ((delegsOf its).map (·.2)).head?
    let mut cur := next k
    let mut onCycle := false
    let mut intoCycle := false
    let mut seen : List String := []
    for _ in [0:ctors.length] do
      match cur with
      | some x =>
        if x == k then onCycle := true; break
        if seen.contains x then intoCycle := true; break
        seen := seen ++ [x]
        cur := next x
      | none => break
    let d := ((delegsOf items).map (·.2)).headD k
    if onCycle then throw s!"{p.show}: {k} delegates to itself, through {d}"
    if intoCycle then throw s!"{p.show}: {k} delegates to {d}, which delegates in a cycle"
  for (p, k, _, _, _, _, items) in ctors do
    let mine := (directOf items).map (·.2) ++ (((delegsOf items).head?.bind fun (_, d) => setBy.lookup d).getD [])
    if let some f := mine.find? fun f => (mine.filter (· == f)).length > 1 then
      throw s!"{p.show}: {k} sets {f} twice: itself, and by delegating"
  for (p, k, _, _, _, c, items) in ctors do
    let mine := (directOf items).map (·.2) ++ (((delegsOf items).head?.bind fun (_, d) => setBy.lookup d).getD [])
    if let some (f, _) := (fullOf c).find? fun (f, _, d, _) => d.isNone && !mine.contains f then
      throw s!"{p.show}: {k} does not set {f}, a field of {c} without a default"
  -- the functions
  let mut out : Array STop := #[]
  for ((p, k, ps, tps, effs, c, items), ci) in ctors.zip (List.range ctors.length) do
    let fs := (setBy.lookup k).getD []
    let fieldsTy := s!"{k}$fields"
    -- the class's type parameters are the archetype's type arguments, which
    -- may mention the constructor's own (a generic constructor, `where`)
    let targs := ((allTargs.drop ci).head?.map (·.2)).getD (targsOf k)
    let ctps : List TParam := ((cdef? c).map (fun cd => cd.tps)).getD []
    let σ : List (String × STy) := (ctps.map (fun tp => tp.name)).zip targs
    let tyOf (f : String) : STy :=
      let t0 : STy := (((fullOf c).find? (·.1 == f)).map (·.2.1)).getD (.name "void")
      t0.substNames σ
    -- (K$fields is parametric over the type parameters the class's type
    -- arguments mention, in order: the same for every overload of K)
    let sparams : List TParam := ((targs.flatMap STy.names).eraseDups).filterMap fun n => tps.find? (·.name == n)
    let tpTys : List STy := sparams.map fun tp => STy.name tp.name
    let fieldsSTy : STy := if sparams.isEmpty then .name fieldsTy else .app fieldsTy tpTys
    if !fs.isEmpty && !out.any (fun | .const _ n _ _ => n == fieldsTy | _ => false) then
      out := out.push (.const p fieldsTy none (.structDef p sparams (fs.map fun f => (f, tyOf f, none, false))))
    let mut body : Array SExpr := #[]
    let mut di := 0
    for it in items do
      match it with
      | .decl ip f none false e => body := body.push (.decl ip s!"{f}$v" (some (tyOf f)) false e)
      | .app ip (.ident _ "$let") [.block _ ds] _ =>
        for d in ds do
          match d with
          | .decl .. => body := body.push d
          | _ => throw s!"{ip.show}: a let: in a constructor has only declarations"
      | .app ip (.ident _ d0) args br =>
        let d := (d0.drop "$ctor:".length).toString
        let call := SExpr.app ip (.ident ip s!"{d}$init") args br
        match (setBy.lookup d).getD [] with
        | [] => body := body.push call
        | dfs =>
          let tmp := s!"$deleg{di}"
          di := di + 1
          body := body.push (.decl ip tmp none false call)
          for f in dfs do
            body := body.push (.decl ip s!"{f}$v" (some (tyOf f)) false (.member ip (.ident ip tmp) f))
      | it => body := body.push (.app p (.ident p "$nofail") [it] false)   -- a `block:` clause
    -- the name's fields this overload does not set (another overload does):
    -- their defaults, as construction would give them
    let mine := (directOf items).map (·.2) ++ (((delegsOf items).head?.bind fun (_, d) => setBy.lookup d).getD [])
    for f in fs.filter (!mine.contains ·) do
      if let some (_, _, some d, _) := (fullOf c).find? (·.1 == f) then
        -- (in a function of its own: the default sees no parameter of K)
        if tps.any (fun tp => (tyOf f).mentions tp.name) then
          throw s!"{p.show}: {k} leaves {f} to another overload, and its default's type mentions a type parameter of {k}: give {f} in every overload of a generic constructor"
        let helper := s!"{k}$default${f}"
        if !out.any (fun | .fn _ n .. => n == helper | _ => false) then
          -- (its effects are its code's, inferred as a `block:`'s are: every
          -- overload that leaves F to it then pays for what it does)
          out := out.push (.fn p helper [] [] [] (tyOf f) d)
        body := body.push (.decl p s!"{f}$v" (some (tyOf f)) false (.app p (.ident p helper) [] false))
    let initRet : SExpr :=
      if fs.isEmpty then .block p []
      else .construct p fieldsTy tpTys (fs.map fun f => .decl p f none false (.ident p s!"{f}$v"))
    out := out.push (.fn p s!"{k}$init" ps tps effs (if fs.isEmpty then .name "void" else fieldsSTy)
      (.block p (body.toList ++ [initRet])))
    let args := ps.map fun prm =>
      if prm.named then SExpr.decl p s!"?{prm.name}" none false (.ident p prm.name) else .ident p prm.name
    let callInit := SExpr.app p (.ident p s!"{k}$init") args (effs.contains "decides")
    let kbody : SExpr :=
      if fs.isEmpty then .block p [callInit, .construct p c targs []]
      else .block p [.decl p "$fields" none false callInit,
        .construct p c targs (fs.map fun f => .decl p f none false (.member p (.ident p "$fields") f))]
    -- (an abstract class is only constructed by delegating to its constructors)
    if !((cdef? c).map (·.specs.contains "abstract")).getD false then
      out := out.push (.fn p k ps tps effs (if targs.isEmpty then .name c else .app c targs) kbody)
  return out.toList

/-- The concurrency helpers (#156), written in Verse: the scheduler's
    state (the clock, in ticks of 1/30 s, and the earliest tick a sleeping
    task waits for), and `Sleep`'s frame with its `new`, `init` and `resume`.
    `Sleep` itself is a stub that only marks the suspension point: the
    lowering (`Suspend.lean`) calls the others in its place. -/
def concPrelude : String := "
sched := class:
    var Now:int = 0
    var Next:int = -1
    var Progress:logic = false
    var Head:?int = false
    var Tail:?int = false
    var Dead:logic = false
    var CancelCur:logic = false
taskBase := class:
    var Done:logic = false
    var Sch:?sched = false
    var Cancelled:logic = false
    var Running:logic = false
    var Root:?int = false
task(t:type) := class(taskBase):
    var Result:?t = false
waitf := class:
    var Pc:int = 0
    var T:taskBase
waitNew(X:taskBase):waitf = waitf{T := X}
waitInit(F:waitf, X:taskBase):void =
    set F.Pc = 0
    set F.T = X
waitResume(F:waitf, C:sched):int =
    if (F.T.Cancelled?):
        set C.CancelCur = true
        return 0
    if (F.T.Done?) then return 1
    if (F.Pc = 0):
        set F.Pc = 1
        set F.T.Sch = option{C}
    0
WaitDone(X:taskBase)<suspends><computes>:void = {}
Await(T:task(t) where t:type)<suspends>:t =
    WaitDone(T)
    if (R := T.Result?) then R else Err()
spawnMark(A:[]void)<computes>:void = {}
cancelMark(X:taskBase)<suspends><computes>:void = {}
branchMark(A:[]void)<computes>:void = {}
evrec(t:type) := class(taskBase):
    var Got:?t = false
    var Next:?evrec(t) = false
event(t:type) := class:
    var Head:?evrec(t) = false
    var Tail:?evrec(t) = false
    Signal(X:t):void =
        if (Head?) then signalAll(Self, X)
signalAll(E:event(t), X:t where t:type):void =
    var Cur:?evrec(t) = E.Head
    set E.Head = false
    set E.Tail = false
    loop:
        if (W := Cur?):
            set W.Got = option{X}
            set W.Done = true
            if (S := W.Sch?) then set S.Progress = true
            set Cur = W.Next
        else:
            break
EvAwait(E:event(t) where t:type)<suspends>:t =
    loop:
        if (H := E.Head?, H.Done?):
            set E.Head = H.Next
        else:
            break
    if (E.Head?) {} else { set E.Tail = false }
    W := evrec(t){}
    if (L := E.Tail?) then set L.Next = option{W} else set E.Head = option{W}
    set E.Tail = option{W}
    defer:
        set W.Done = true
    WaitDone(W)
    if (V := W.Got?) then V else Err()
sticky_event(t:type) := class(event(t)):
    var Last:?t = false
    Signal<override>(X:t):void =
        set Last = option{X}
        if (Head?) then signalAll(Self, X)
StickyAwait(E:sticky_event(t) where t:type)<suspends>:t =
    if (V := E.Last?) then V else EvAwait(E)
sleep := class:
    var Pc:int = 0
    var Secs:float = 0.0
    var Wake:int = 0
sleepNew(S:float):sleep = sleep{Secs := S}
sleepInit(F:sleep, S:float):void =
    set F.Pc = 0
    set F.Secs = S
sleepResume(F:sleep, C:sched):int =
    if (F.Pc = 0):
        set F.Pc = 1
        if (F.Secs >= 0.0, F.Secs < 1000000000000000.0):
            N:int = if (R := Round[F.Secs * 30.0], R >= 1) then R else 1
            set F.Wake = C.Now + N
        else if (F.Secs >= 0.0):
            set F.Wake = -1
        else:
            return 1
    if (F.Wake < 0):
        return 0
    if (C.Now >= F.Wake):
        return 1
    if (C.Next < 0):
        set C.Next = F.Wake
    else if (F.Wake < C.Next):
        set C.Next = F.Wake
    0
Sleep(S:float)<suspends><computes>:void = {}
syncMark(A:[]void)<suspends><computes>:void = {}
raceMark(A:[]void)<suspends><computes>:void = {}
rushMark(A:[]void)<suspends><computes>:void = {}
"

def concTops : Except String (List STop) :=
  parsePrelude concPrelude ["sched", "Now", "Next", "sleep", "Pc", "Secs", "Wake", "sleepNew",
    "sleepInit", "sleepResume", "Sleep", "syncMark", "raceMark", "S", "F", "C", "N", "R", "A",
    "Progress", "Roots", "taskBase", "Done", "Result", "waitf", "T", "X", "waitNew", "waitInit", "waitResume",
    "WaitDone", "Await", "spawnMark", "t", "Sch", "Dead", "evrec", "Got", "Next", "Head", "Tail", "Cur", "W", "L", "V",
    "EvAwait", "E", "branchMark", "rushMark", "signalAll", "H", "StickyAwait", "Last", "CancelCur", "Cancelled", "Running", "Root", "cancelMark"]

/-- `subscribable_event(t)` (#210): an event whose `Signal` also calls the
    functions subscribed to it, each `Subscribe` giving a `cancelable` whose
    `Cancel` unsubscribes it. Added, with the concurrency prelude it
    extends, to a program that mentions it. -/
def subPrelude : String := "
cancelable := interface:
    Cancel():void
subscription := class(cancelable):
    var Live:logic = true
    Cancel<override>():void =
        set Live = false
subscribable_event(t:type) := class(event(t)):
    var Handlers:[]tuple(subscription, type{_(:t):void}) = array{}
    Signal<override>(X:t):void =
        if (Head?) then signalAll(Self, X)
        Hs := Handlers
        set Handlers = for (H : Hs, H(0).Live?) { H }
        for (H : Hs, H(0).Live?):
            H(1)(X)
    Subscribe(F:type{_(:t):void}):cancelable =
        S := subscription{}
        set Handlers += array{(S, F)}
        S
"

def subTops : Except String (List STop) :=
  parsePrelude subPrelude ["subscription", "Live", "Handlers", "Hs", "H", "S", "F", "X", "t", "Head", "signalAll"]

/-- The number of constructors in a Verse Core type (to bound the types a
    specialisation is made at, #174). -/
partial def _root_.OpenVerse.VTy.size : VTy → Nat
  | .arr t | .opt t => 1 + t.size
  | .tup ts | .ref _ ts => 1 + (ts.map VTy.size).sum
  | _ => 1

/-- An error of the lowering in function `name` (#156): with the position of
    its definition among `tops`, and the name the program gave it (a
    specialised copy's original's, #174). -/
def inFnMsg (tops : List STop) (name msg : String) : String :=
  let base := (name.splitOn "$at").headD name
  let pos := tops.findSome? fun
    | .fn q m .. => if m == base then some q else none
    | .classDef _ c _ _ _ _ _ _ ms => ms.findSome? fun
      | .fn q m .. => if s!"{c}.{m}" == base then some q else none
      | _ => none
    | _ => none
  match pos with
  | some q => s!"{q.show}: in {base}: {msg}"
  | none => s!"in {base}: {msg}"

/-- (#174) Specialise the generic functions whose tasks' roots would depend
    on their type parameters: those with a `branch` or `rush` (marks
    `branchMark`, `rushMark`), or a `spawn` (`spawnMark`) whose call's
    arguments or result have such types (or a spawned dispatch reading
    values of such types), or (immediate ones, `isSusp` false) any `spawn`,
    and those calling one at such types. Each call of one at closed type
    arguments, read off the call's witnesses (its last `ntpOf g` arguments,
    whose types the checker infers exactly), goes to a copy at those types
    (appended to `fns`, `slotTys`), whose own calls are handled the same
    way; in a copy, the refined dispatch tests its types rule out are
    dropped. The originals are then never called and keep only their
    parameters. Gives the functions, their slot types, the copies'
    signatures, each copy's original and type arguments, and which
    functions were replaced. -/
def specialise (fns0 : Array Fn) (slotTys0 : Array (List VTy)) (S0 : Sigs) (ntpOf : Nat → Nat)
    (isSusp : Nat → Bool) (branchMark rushMark spawnMark : Nat)
    (inFn : String → String → String := fun n m => s!"in {n}: {m}") :
    Except String (Array Fn × Array (List VTy) × Array (List VTy × VTy) × Array (Nat × List VTy) × Array Bool) := do
  let mut fns := fns0
  let mut slotTys := slotTys0
  let nOrig := fns.size
  let mut specSigs : Array (List VTy × VTy) := #[]
  let mut needy : Array Bool := #[]
  let resTy (S : Sigs) (gi : Nat) : VTy := ((S.fns[gi]?).map (·.2)).getD .void
  for gi in List.range nOrig do
    let Γ := slotTys[gi]!
    let ρ := resTy S0 gi
    let openTy (e : Expr) : Bool := (tc S0 Γ ρ e none).all (·.mentionsVar)
    let openSlot (j : Nat) : Bool := ((Γ[j]?).map (·.mentionsVar)).getD false
    let spawnOpen (es : List Expr) : Bool := match es with
      | [.prim .mkArr [.seq (.call _ hs) _, .seq (.local t) _]] => openSlot t || hs.any openTy
      | _ => (Suspend.slotsOf (.prim .mkTup es)).any openSlot
    needy := needy.push (ntpOf gi > 0 && (Suspend.callsOf fns[gi]!.body).any fun (g, es) =>
      g == branchMark || g == rushMark || (g == spawnMark && (!isSusp gi || spawnOpen es)))
  let witTys (S : Sigs) (Γ : List VTy) (ρ : VTy) (g : Nat) (es : List Expr) : List (Option VTy) :=
    (es.drop (es.length - ntpOf g)).map fun e => tc S Γ ρ e none
  -- (a call of one at types that mention the caller's type parameters: the
  -- caller needs specialising too)
  let mut changed := true
  while changed do
    changed := false
    for gi in List.range nOrig do
      if needy[gi]! || ntpOf gi == 0 then continue
      if (Suspend.callsOf fns[gi]!.body).any (fun (g, es) => (needy[g]?.getD false) &&
          (witTys S0 slotTys[gi]! (resTy S0 gi) g es).any (·.all (·.mentionsVar))) then
        needy := needy.set! gi true
        changed := true
  -- (#225) the other generic suspends functions are copied too where they
  -- are called at small closed types, within a budget, and kept for every
  -- other call: a copy keeps its callers' child frames in fields of its own
  -- class, resumed outside any condition, not in options unwrapped in a
  -- condition, where a resumption's writes make the reference interpreter
  -- copy the heap
  let mut soft : Array Bool := (List.range nOrig).toArray.map fun gi => ntpOf gi > 0 && isSusp gi && !needy[gi]!
  let mut softCopies := 0
  let mut specKeys : Array (Nat × List VTy) := #[]
  let mut queue : Array Nat := ((List.range nOrig).filter fun gi => !needy[gi]!).toArray
  let mut qi := 0
  while qi < queue.size do
    let gi := queue[qi]!
    qi := qi + 1
    let S : Sigs := { S0 with fns := S0.fns ++ specSigs.toList }
    let Γ := slotTys[gi]!
    let ρ := resTy S gi
    let calls := (Suspend.callsOf fns[gi]!.body).filter fun (g, _) => needy[g]?.getD false || soft[g]?.getD false
    if calls.isEmpty then continue
    for (g, es) in calls do
      if !(needy[g]?.getD false) then
        -- (a soft one: copied only at a small closed type, within the budget)
        let some θ := (witTys S Γ ρ g es).mapM id | continue
        if θ.any (·.mentionsVar) || θ.any (·.size > 40) then continue
        if !specKeys.contains (g, θ) then
          if softCopies ≥ 200 then continue
          let σ : Nat → VTy := fun i => θ.getD i (.var i)
          let fn := fns[g]!
          let Γc := slotTys[g]!.map (VTy.subst σ)
          fns := fns.push { fn with name := s!"{fn.name}$at{specKeys.size}", body := Suspend.pruneDead S0 Γc fn.body }
          slotTys := slotTys.push Γc
          let (ps, τ) := (S0.fns[g]?).getD ([], .void)
          specSigs := specSigs.push (ps.map (VTy.subst σ), τ.subst σ)
          needy := needy.push false
          soft := soft.push false
          queue := queue.push (nOrig + specKeys.size)
          specKeys := specKeys.push (g, θ)
          softCopies := softCopies + 1
        continue
      let some θ := (witTys S Γ ρ g es).mapM id
        | throw (inFn fns[gi]!.name s!"a type argument of a call of {fns[g]!.name} has no type of its own (#174)")
      -- (types that grow at each copy, doubling for instance: polymorphic
      -- recursion; linear growth meets the bound on copies first)
      if θ.any (·.size > 2000) then
        throw (inFn fns[gi]!.name s!"{fns[g]!.name} would be compiled at a type of more than 2000 parts, as if at ever bigger types: a generic function with branch, rush or spawn, or one using such a function at its own type parameters, cannot call itself at bigger types (#174)")
      if θ.any (·.mentionsVar) then throw s!"internal error: specialising a call of {fns[g]!.name} in {fns[gi]!.name}"
      if !specKeys.contains (g, θ) then
        -- (the soft copies, #225, have their own budget)
        if specKeys.size - softCopies ≥ 500 then
          throw (inFn fns[gi]!.name s!"more than 500 copies of generic functions with branch, rush or spawn, one per type each is used at (last {fns[g]!.name}): a function calling itself at ever bigger types, or many nested generic uses, cannot be compiled (#174)")
        let σ : Nat → VTy := fun i => θ.getD i (.var i)
        let fn := fns[g]!
        let Γc := slotTys[g]!.map (VTy.subst σ)
        fns := fns.push { fn with name := s!"{fn.name}$at{specKeys.size}", body := Suspend.pruneDead S0 Γc fn.body }
        slotTys := slotTys.push Γc
        let (ps, τ) := (S0.fns[g]?).getD ([], .void)
        specSigs := specSigs.push (ps.map (VTy.subst σ), τ.subst σ)
        needy := needy.push false
        soft := soft.push false
        queue := queue.push (nOrig + specKeys.size)
        specKeys := specKeys.push (g, θ)
    let keys := specKeys
    let isNeedy := needy
    let isSoft := soft
    let S : Sigs := { S0 with fns := S0.fns ++ specSigs.toList }
    let body := Suspend.redirectCalls (fun g es =>
      if isNeedy[g]?.getD false || isSoft[g]?.getD false then
        match (witTys S Γ ρ g es).mapM id with
        | some θ => (keys.idxOf? (g, θ)).map (nOrig + ·)
        | none => none
      else none) fns[gi]!.body
    fns := fns.set! gi { fns[gi]! with body }
  for gi in List.range nOrig do
    if needy[gi]! then
      let fn := fns[gi]!
      fns := fns.set! gi { fn with nslots := fn.arity, body := .prim .userErr [] }
      slotTys := slotTys.set! gi (slotTys[gi]!.take fn.arity)
  return (fns, slotTys, specSigs, specKeys, needy.extract 0 nOrig)

/-- The concurrency lowering (#156), at the end of `elabProgramCore`: each
    `<suspends>` function becomes a frame class and its resume, cancel and
    arm functions (`Suspend.lower`), after the generic functions with task
    roots are specialised (#174) and spawned dispatches are lifted (#173);
    then the task roots, branch wrappers, the scheduler's list and, for a
    suspends `Main`, `$Run` and `$Start`. Gives the functions, their slot
    types and signatures, the class table, the frame classes and `Main`'s
    call. (A function of its own, so that `elabProgramCore` stays within
    Lean's elaboration limits.) -/
def lowerConcurrency (env : TyEnv) (sigs gsigs : Array Sig) (mainSig : Sig) (fsigs0 : List (List VTy × VTy))
    (protos : HeapTy) (pins : List (List (Option VTy))) (inFn : String → String → String)
    (fns0 : Array Fn) (slotTys0 : Array (List VTy)) (fsigsIn : List (List VTy × VTy)) (classTable0 : List (List VTy)) :
    Except String (Array Fn × Array (List VTy) × List (List VTy × VTy) × List (List VTy) × Array (List VTy) × Expr) := do
  let mut fns := fns0
  let mut slotTys := slotTys0
  let mut fsigs := fsigsIn
  let mut classTable := classTable0
  let mut frameClasses : Array (List VTy) := #[]
  let mut extraSigs : Array (List VTy × VTy) := #[]
  let mut mainCall : Expr := .call mainSig.idx []
  let allS := sigs.toList ++ gsigs.toList
  let idxOf (n : String) : Nat := ((allS.find? (·.name == n)).map (·.idx)).getD 0
  let sleepIdx := idxOf "$Sleep"
  let waitIdx := idxOf "$WaitDone"
  let syncMark := idxOf "$syncMark"
  let raceMark := idxOf "$raceMark"
  let rushMark := idxOf "$rushMark"
  let spawnMark := idxOf "$spawnMark"
  let branchMark := idxOf "$branchMark"
  let isMark (f : Nat) : Bool := f == syncMark || f == raceMark || f == rushMark
  let leaves := ["$Sleep", "$WaitDone", "$syncMark", "$raceMark", "$rushMark", "$spawnMark", "$branchMark",
    "$cancelMark"]
  -- (#174) the generic functions whose tasks' roots would depend on their
  -- type parameters, specialised at the types they are called at
  let sigOf (f : Nat) : Option Sig := allS.find? (·.idx == f)
  let nOrig := fns.size
  -- (#209) an override that reads its class's type arguments' values from
  -- its receiver is not copied per type, so its spawns would not be lowered
  for g in gsigs do
    if !g.selfTps.isEmpty && !(Suspend.spawnSites spawnMark fns[g.idx]!.body).isEmpty then
      throw (inFn g.name "a spawn in an override of a class with type parameters that its parent's type arguments do not give is not supported yet (#209)")
  let (fns1, slotTys1, specSigs, specKeys, replaced) ← specialise fns slotTys
    { fns := fsigs0, classes := classTable, protos, pins }
    (fun f => ((sigOf f).map (·.ndicts)).getD 0) (fun f => ((sigOf f).map (·.suspends)).getD false)
    branchMark rushMark spawnMark inFn
  fns := fns1
  slotTys := slotTys1
  let fsigs0 := fsigs0 ++ specSigs.toList
  fsigs := fsigs ++ specSigs.toList
  let specUser : List (Nat × String × Nat) := specKeys.toList.zipIdx.filterMap fun ((g, _), k) =>
    if ((sigOf g).map (fun s => s.suspends && !leaves.contains s.name)).getD false then
      some (nOrig + k, fns[nOrig + k]!.name, 0)
    else none
  -- each `spawn` of a method with several implementations (#173): its
  -- dispatch chain becomes a suspends function `$dispatchK` of the slots
  -- it uses (the receiver, the arguments, and the slots its tests bind the
  -- narrowed receiver to, which start as the caller's), which the spawn
  -- calls
  let dispBase := fns.size
  let mut lifted : Array (Expr × List Nat × Nat) := #[]
  let mut liftedIn : Array Nat := #[]
  for gi in List.range dispBase do
    let n0 := lifted.size
    let (body, acc) := (Suspend.liftChains spawnMark dispBase fns[gi]!.body).run lifted
    if acc.size > n0 then
      fns := fns.set! gi { fns[gi]! with body }
      lifted := acc
      liftedIn := liftedIn ++ (List.replicate (acc.size - n0) gi).toArray
  let mut disps : List (Nat × String × Nat) := []
  let mut dispSigs : Array (List VTy × VTy) := #[]
  for ((ch, ops, t), k) in lifted.toList.zipIdx do
    let gi := liftedIn[k]!
    let Γ := slotTys[gi]!
    let tys := ops.map fun o => (Γ[o]?).getD .int
    if tys.any (·.mentionsVar) then
      throw (inFn fns[gi]!.name "a spawned call whose arguments' types mention the function's type parameters is not supported yet (#156)")
    let ρ ← match Γ[t]? with
      | some (.ref _ [ρ]) => pure ρ
      | _ => throw s!"internal error: lowering {fns[gi]!.name}: a spawn's task"
    fns := fns.push { name := s!"$dispatch{k}", arity := ops.length, nslots := ops.length, decides := false,
                      writes := true, body := Suspend.renumber (fun j => (ops.idxOf? j).getD 0) ch }
    slotTys := slotTys.push tys
    dispSigs := dispSigs.push (tys, ρ)
    disps := disps ++ [(dispBase + k, s!"$dispatch{k}", 0)]
  let fsigs0 := fsigs0 ++ dispSigs.toList
  fsigs := fsigs ++ dispSigs.toList
  -- (the specialised originals, never called, are not lowered)
  let user := (allS.filter fun s => s.suspends && !leaves.contains s.name && !(replaced[s.idx]?.getD false)).map
    (fun s => (s.idx, s.name, s.tparams.length)) ++ specUser ++ disps
  -- (copies of immediate functions that spawn, their spawns lifted)
  let specImm : List (Nat × String × Nat) := specKeys.toList.zipIdx.filterMap fun ((g, _), k) =>
    if ((sigOf g).map (fun s => !s.suspends && !s.isConst)).getD false &&
        !(Suspend.spawnSites spawnMark fns[nOrig + k]!.body).isEmpty then
      some (nOrig + k, fns[nOrig + k]!.name, 0)
    else none
  let tagBase := env.classes.length
  let schedTag := env.tagOf "$sched"
  let schedTy : VTy := .ref [schedTag] []
  let fieldIdx (c f : String) : Nat := ((env.fields c).findIdx? (·.1 == f)).getD 0
  let Sorig : Sigs := { fns := fsigs0, classes := classTable, protos, pins }
  -- each `spawn` (#156) gets a root: a function `$spawnK(T, args…)` that
  -- runs the spawned call and fills the task `T`
  let mut roots : Array (Nat × String × Nat) := #[]
  let mut spawnOf : Array (List Nat) := #[]   -- each user function's spawns' root numbers
  let nFns0 := fns.size
  -- (immediate functions may spawn too: their spawns start the task on
  -- the scheduler, which is its class's prototype, a literal)
  let imm := ((sigs.toList.filter fun s => !s.suspends && !s.isConst && s.tparams.isEmpty &&
    !(Suspend.spawnSites spawnMark fns[s.idx]!.body).isEmpty).map fun s => (s.idx, s.name, 0)) ++ specImm
  let mut immSpawns : Array (Nat × List Nat) := #[]
  for (gi, gname, _) in user ++ imm do
    if ((sigOf gi).map (!·.selfTps.isEmpty)).getD false then
      throw (inFn gname "a spawn in an override of a class with type parameters that its parent's type arguments do not give is not supported yet (#209)")
    let fn := fns[gi]!
    let Γ := slotTys[gi]!
    let mut mine : List Nat := []
    for (h, hs, t) in Suspend.spawnSites spawnMark fn.body do
      let some ttyT := Γ[t]? | throw s!"internal error: lowering {gname}: a spawn's task"
      let mut atys : Array VTy := #[]
      -- (the callee's type arguments, from its witnesses)
      if ((sigOf h).map (!·.selfTps.isEmpty)).getD false then
        throw (inFn gname s!"a spawn of {((sigOf h).map (·.name)).getD "a method"}, a method of a class with type parameters that its parent's type arguments do not give, is not supported yet (#209)")
      let ntpH := ((sigOf h).map (·.tparams.length)).getD 0
      let wit := (hs.drop (hs.length - ntpH)).map fun w => tc Sorig Γ (fsigs0[gi]!).2 w none
      let θh : Nat → VTy := fun i => match wit[i]? with
        | some (some τ) => τ
        | _ => .var i
      for (e, i) in hs.zipIdx do
        match tc Sorig Γ (fsigs0[gi]!).2 e none with
        | some τ =>
          if τ.mentionsVar then
            throw (inFn gname "a spawned call whose arguments' types mention the function's type parameters is not supported yet (#156)")
          atys := atys.push τ
        | none =>
          -- (`array{}` or `false` has no type of its own: the callee's
          -- parameter type at its type arguments, when that is closed)
          let pt := (((fsigs0[h]?).bind (·.1[i]?)).getD (.var 0)).subst θh
          if pt.mentionsVar then
            throw (inFn gname "the arguments of a spawned call of a generic function must have types of their own (#156)")
          atys := atys.push pt
      let k := roots.size
      let n := hs.length
      let body : Expr := .seq
        (.heap (.set (fieldIdx "task" "$Result")) [.local 0, .prim .mkSome [.call h ((List.range n).map (fun i => Expr.local (i + 1)))]])
        (.seq (.heap (.set (fieldIdx "task" "$Done")) [.local 0, .lit (.logic true)]) (.lit .void))
      let Γk := ttyT :: atys.toList
      fns := fns.push { name := s!"$spawn{k}", arity := n + 1, nslots := n + 1, decides := false,
                        writes := true, body }
      slotTys := slotTys.push Γk
      roots := roots.push (nFns0 + k, s!"$spawn{k}", 0)
      mine := mine ++ [k]
    if imm.any (·.1 == gi) then immSpawns := immSpawns.push (gi, mine)
    else spawnOf := spawnOf.push mine
  let fsigs0 := fsigs0 ++ roots.toList.map fun (ri, _, _) => (slotTys[ri]!, VTy.void)
  fsigs := fsigs ++ roots.toList.map fun (ri, _, _) => (slotTys[ri]!, VTy.void)
  let lows := user ++ roots.toList
  let nFns := fns.size
  let isS : Nat → Bool := fun f => f == sleepIdx || f == waitIdx || isMark f || lows.any (·.1 == f)
  -- each one's body (initialisations stripped), suspension points and arms
  let mut parts : Array (List Expr × Expr × Nat × Nat) := #[]
  for (gi, gname, _) in lows do
    let fn := fns[gi]!
    let some (ds, b) := Suspend.stripInits (fn.nslots - fn.arity) fn.body
      | throw s!"internal error: lowering {gname}: unexpected initialisations"
    parts := parts.push (ds, b, Suspend.countSusp (fun f => isS f || f == branchMark) (fun _ => false) false (· == spawnMark) b +
        Suspend.countArms (· == rushMark) b,
      Suspend.countArms (fun f => isMark f || f == branchMark) b)
  let frameTy (j : Nat) : VTy :=
    .ref [tagBase + j] ((List.range lows[j]!.2.2).map VTy.var)
  -- the methods called through `Typed.dispatch` (#142) of classes that fix
  -- type arguments (a generic one at or above the receiver's class is
  -- called without the refinement, so it is never one)
  let targets : List Nat := (lows.foldl (fun acc (gi, _, _) => acc ++
    Suspend.dispatchTargets (fun f => user.any fun (h, _, _) => h == f) fns[gi]!.body) []).eraseDups
  -- each one's `new`, `reset`, `cancel` and `result` (fixed indices), each
  -- target's receiver-first helpers, each root's trampoline and `start`,
  -- then the arms' functions
  let L := lows.length
  let selfBase := nFns + 4 * L
  let trampOf (k : Nat) : Nat := selfBase + 4 * targets.length + 2 * k
  -- the scheduler: its class's prototype
  let some schedLit := Suspend.coreDefault Sorig [] 0 schedTy
    | throw "internal error: no prototype for the scheduler"
  -- an immediate function's spawns: start the task now
  for (gi, ks) in immSpawns do
    let fn := fns[gi]!
    let body := Suspend.substSpawns spawnMark (fun i _ hs t =>
      let k := (ks[i]?).getD 0
      .call (trampOf k + 1) [schedLit, .call (nFns + 4 * (user.length + k)) (schedLit :: .local t :: hs)]) fn.body
    fns := fns.set! gi { fn with writes := true, body }
  -- each `branch` (numbered across the functions, in order) gets a
  -- wrapper class `[pc, frame]` and its `tramp`, `start` and `stop`
  let mut branchOf : Array (List Nat) := #[]
  let mut branchHome : Array Nat := #[]
  for (j, part) in (List.range L).zip parts.toList do
    let n := Suspend.countSusp (· == branchMark) (fun _ => false) false (fun _ => false) part.2.1 +
      Suspend.countArms (· == rushMark) part.2.1
    branchOf := branchOf.push ((List.range n).map (· + branchHome.size))
    branchHome := branchHome ++ (List.replicate n j).toArray
  let B := branchHome.size
  -- (`$link(sched, root)`, which adds a root to the scheduler's list,
  -- comes before them)
  let linkIdx := selfBase + 4 * targets.length + 2 * roots.size
  let wrapFnBase := linkIdx + 1
  let wrapTag (K : Nat) : Nat := tagBase + L + K
  let wrapTy (K : Nat) : VTy := .ref [wrapTag K] []
  let callee : Nat → Option Suspend.Callee := fun f =>
    if f == sleepIdx then
      some { tag := env.tagOf "$sleep", newFn := idxOf "$sleepNew", initFn := idxOf "$sleepInit",
             resumeFn := idxOf "$sleepResume", cancelFn := none, passFields := [], resField := none }
    else if f == waitIdx then
      some { tag := env.tagOf "$waitf", newFn := idxOf "$waitNew", initFn := idxOf "$waitInit",
             resumeFn := idxOf "$waitResume", cancelFn := none, passFields := [], resField := none }
    else match lows.zipIdx.find? (·.1.1 == f) with
      | some ((gi, _, ntp), j) =>
        let (_, _, sites, arms) := parts[j]!
        some { tag := tagBase + j, newFn := nFns + 4 * j, initFn := nFns + 4 * j + 1, resumeFn := gi,
               cancelFn := some (nFns + 4 * j + 2),
               passFields := (List.range fns[gi]!.arity).map fun i => Suspend.slotBaseOf sites arms + i,
               resField := some Suspend.resF, generic := ntp != 0, newSched := true,
               resultFn := if ntp == 0 then some (nFns + 4 * j + 3) else none, ntp,
               selfFns := (targets.idxOf? gi).map fun i =>
                 (selfBase + 4 * i, selfBase + 4 * i + 1, selfBase + 4 * i + 2, selfBase + 4 * i + 3) }
      | none => none
  for ((gi, _, _), j) in lows.zipIdx do
    let ps := slotTys[gi]!.take fns[gi]!.arity
    extraSigs := extraSigs.push (schedTy :: ps, frameTy j)
    extraSigs := extraSigs.push (frameTy j :: ps, VTy.void)
    extraSigs := extraSigs.push (frameTy j :: schedTy :: ps, VTy.void)
    extraSigs := extraSigs.push ([frameTy j], (fsigs0[gi]!).2)
  -- each target's helpers (#142), whose first parameter is the receiver:
  -- `arrive(self, args…, frame, sched)` resets the frame (or makes one)
  -- and gives it; `take(self, frame)` its result; `resume(frame, sched)`
  -- and `cancel(frame, sched)` pass the parameters from the frame
  let mut selfFns : Array Fn := #[]
  let mut selfTys : Array (List VTy) := #[]
  let mut selfSigs : Array (List VTy × VTy) := #[]
  for gi in targets do
    let some j := lows.findIdx? (·.1 == gi) | throw "internal error: a dispatch target"
    let (_, gname, ntp) := lows[j]!
    let a := fns[gi]!.arity
    let ps := slotTys[gi]!.take a
    let ρ := (fsigs0[gi]!).2
    let (_, _, sites, arms) := parts[j]!
    let wide : VTy := .ref [tagBase + j, schedTag] []
    let locals := (List.range a).map Expr.local
    let isF (i : Nat) : Expr := .heap (.isTag [tagBase + j]) [.local i]
    let pass := (List.range a).map fun i => Expr.heap (.get (Suspend.slotBaseOf sites arms + i)) [.local 0]
    let resumeOwn : Fn := { name := s!"{gname}$resumeOwn", arity := 2, nslots := 2, decides := false, writes := true,
                            body := .call gi (.local 0 :: .local 1 :: pass) }
    let cancelOwn : Fn := { name := s!"{gname}$cancelOwn", arity := 2, nslots := 2, decides := false, writes := true,
                            body := .call (nFns + 4 * j + 2) (.local 0 :: .local 1 :: pass) }
    if ntp != 0 then
      -- (a generic one's frame is kept in an option field, as any generic
      -- callee's: `arrive(self, args…, frame?, sched)` resets it or makes
      -- one; `take(self, frame?)` gives its result, failing without a frame,
      -- so that the caller unwraps it in a condition)
      let optF : VTy := .opt (frameTy j)
      let arriveBody : Expr := .seq (.ite (.call (nFns + 4 * j + 1) (.prim .query [.local a] :: locals)) Suspend.vd
        (.seq (.assign a (.prim .mkSome [.call (nFns + 4 * j) (.local (a + 1) :: locals)])) Suspend.vd)) (.local a)
      let takeBody : Expr := .heap (.get Suspend.resF) [.prim .query [.local 1]]
      selfFns := selfFns ++ #[
        { name := s!"{gname}$arrive", arity := a + 2, nslots := a + 2, decides := false, writes := true,
          body := arriveBody },
        { name := s!"{gname}$take", arity := 2, nslots := 2, decides := true, writes := false, body := takeBody },
        resumeOwn, cancelOwn]
      selfTys := selfTys ++ #[ps ++ [optF, schedTy], [ps.headD .int, optF], [frameTy j, schedTy], [frameTy j, schedTy]]
      selfSigs := selfSigs ++ #[(ps ++ [optF, schedTy], optF), ([ps.headD .int, optF], ρ),
        ([frameTy j, schedTy], .int), ([frameTy j, schedTy], VTy.void)]
      continue
    let arriveBody : Expr := .seq (.ite (isF a) (.call (nFns + 4 * j + 1) (.local a :: locals))
      (.seq (.assign a (.call (nFns + 4 * j) (.local (a + 1) :: locals))) Suspend.vd)) (.local a)
    selfFns := selfFns ++ #[
      { name := s!"{gname}$arrive", arity := a + 2, nslots := a + 2, decides := false, writes := true,
        body := arriveBody },
      { name := s!"{gname}$take", arity := 2, nslots := 2, decides := false, writes := false,
        body := .ite (isF 1) (.call (nFns + 4 * j + 3) [.local 1]) (.prim .userErr []) },
      resumeOwn, cancelOwn]
    selfTys := selfTys ++ #[ps ++ [wide, schedTy], [ps.headD .int, wide], [frameTy j, schedTy], [frameTy j, schedTy]]
    selfSigs := selfSigs ++ #[(ps ++ [wide, schedTy], wide), ([ps.headD .int, wide], ρ),
      ([frameTy j, schedTy], .int), ([frameTy j, schedTy], VTy.void)]
  let rootJ (k : Nat) : Nat := user.length + k
  let rootTags := (List.range roots.size).map (fun k => tagBase + rootJ k) ++ (List.range B).map wrapTag
  let mainJ := (lows.findIdx? (·.1 == mainSig.idx)).getD 0
  let rootAny : VTy := .ref ((tagBase + mainJ) :: rootTags) []
  -- each root's trampoline (frame, sched) and `start(sched, frame)`
  let mut rootSigs : Array (List VTy × VTy) := #[]
  for k in List.range roots.size do
    rootSigs := rootSigs.push ([frameTy (rootJ k), schedTy], .int)
    rootSigs := rootSigs.push ([schedTy, frameTy (rootJ k)], VTy.void)
  let Sinf : Sigs := { fns := fsigs0 ++ extraSigs.toList ++ selfSigs.toList ++ rootSigs.toList, classes := classTable,
                       protos, pins }
  let mut newFns : Array Fn := #[]
  let mut newTys : Array (List VTy) := #[]
  let mut armFns : Array Fn := #[]
  let mut armTys : Array (List VTy) := #[]
  let mut armSigs : Array (List VTy × VTy) := #[]
  let armBase := wrapFnBase + 3 * B
  let mut branchFns : Array Fn := #[]
  let mut branchTys : Array (List VTy) := #[]
  -- (each branch's arm resume function, done field, and the passing of its
  -- function's parameters from the frame, for cancelling it)
  let mut branchInfo : Array (Nat × Nat × List Expr) := #[]
  let mut branchSigs : Array (List VTy × VTy) := #[]
  let progressF := fieldIdx "$sched" "$Progress"
  let headF := fieldIdx "$sched" "$Head"
  let tailF := fieldIdx "$sched" "$Tail"
  -- (set when a root ends or is stopped: the list then has cells to drop)
  let deadF := fieldIdx "$sched" "$Dead"
  -- (cancellation: the task's flags and root; the scheduler's request to
  -- cancel the root that just ran)
  let cancelCurF := fieldIdx "$sched" "$CancelCur"
  let tDoneF := fieldIdx "task" "$Done"
  let tCancelledF := fieldIdx "task" "$Cancelled"
  let runningF := fieldIdx "task" "$Running"
  let rootF := fieldIdx "task" "$Root"
  for ((gi, gname, _), j) in lows.zipIdx do
    let fn := fns[gi]!
    let Γ := slotTys[gi]!
    let a := fn.arity
    let (ds, b, sites, arms) := parts[j]!
    let ρ := (fsigs0[gi]!).2
    let fnBase := armBase + armFns.size
    let spawns : Array (Nat × Nat) := ((spawnOf[j]?).getD []).toArray.map fun k =>
      (nFns + 4 * rootJ k, trampOf k + 1)
    let branches : Array (Nat × Nat × Nat) := ((branchOf[j]?).getD []).toArray.map fun K =>
      (wrapFnBase + 3 * K + 1, wrapFnBase + 3 * K + 2, wrapTag K)
    let low ← (Suspend.lower Sinf callee syncMark raceMark rushMark spawnMark spawns branchMark branches a Γ ρ (frameTy j)
      schedTag fnBase b).mapError fun e => inFn gname e
    -- its branches' wrappers: `tramp(w, sched)` resumes the arm (with the
    -- function's parameters from its frame) unless the function stopped
    -- it; `start(sched, frame)` makes the wrapper, registers it and runs
    -- it once; `stop(w)` marks it done
    let (_, _, sitesJ, armsJ) := parts[j]!
    for (K, (armRes, doneA, runNow)) in ((branchOf[j]?).getD []).zip low.branchArms do
      let fr : Expr := .heap (.get 1) [.local 0]
      let pass := (List.range a).map fun i => Expr.heap (.get (Suspend.slotBaseOf sitesJ armsJ + i)) [fr]
      branchInfo := branchInfo.push (armRes, doneA, pass)
      -- (a `rush` loser that runs `return` after the `rush` ended has
      -- unwound itself and ends there: it is marked so, and not stopped
      -- again when the function exits, #181)
      let tramp : Expr := .seq (.ite (.prim .eq [.heap (.get doneA) [fr], Suspend.int 0])
          (.seq (Suspend.seqVoid [.assign 2 (.call armRes (fr :: .local 1 :: pass)),
            .ite (.prim .eq [.local 2, Suspend.int 1]) (.seq (.heap (.set doneA) [fr, Suspend.int 1]) Suspend.vd) Suspend.vd,
            .ite (.prim .eq [.local 2, Suspend.int 2])
              (.seq (Suspend.seqVoid [.heap (.set doneA) [fr, Suspend.int 2], .assign 2 (Suspend.int 1)]) Suspend.vd)
              Suspend.vd])
            Suspend.vd)
          (.seq (.assign 2 (Suspend.int 1)) Suspend.vd)) (.local 2)
      branchFns := branchFns.push { name := s!"$branch{K}$tramp", arity := 2, nslots := 3, decides := false,
                                    writes := true, body := initPrefixE 2 [Suspend.int 0] tramp }
      branchTys := branchTys.push [wrapTy K, schedTy, .int]
      branchSigs := branchSigs.push ([wrapTy K, schedTy], .int)
      -- (a `rush` loser's wrapper only registers it: it already started)
      let register : Expr := .call linkIdx [.local 0, .local 2]
      let start : Expr := .seq (Suspend.seqVoid (if !runNow then [register] else [register,
        .assign 3 (.call (wrapFnBase + 3 * K) [.local 2, .local 0]),
        .ite (.prim .eq [.local 3, Suspend.int 1])
          (.seq (Suspend.seqVoid [.heap (.set Suspend.pcF) [.local 2, Suspend.int (-1)],
            .heap (.set progressF) [.local 0, .lit (.logic true)], .heap (.set deadF) [.local 0, .lit (.logic true)]])
            Suspend.vd) Suspend.vd])) (.local 2)
      let startFn : Fn := { name := s!"$branch{K}$start", arity := 2, nslots := 4, decides := false, writes := true,
                            body := initPrefixE 2 [.heap (.new (wrapTag K)) [Suspend.int 0, .local 1], Suspend.int 0] start }
      branchFns := branchFns.push startFn
      branchTys := branchTys.push [schedTy, frameTy j, wrapTy K, .int]
      branchSigs := branchSigs.push ([schedTy, frameTy j], wrapTy K)
      let stopFn : Fn := { name := s!"$branch{K}$stop", arity := 2, nslots := 2, decides := false, writes := true,
                           body := Suspend.seqVoid [.heap (.set Suspend.pcF) [.local 0, Suspend.int (-1)],
                             .heap (.set deadF) [.local 1, .lit (.logic true)]] }
      branchFns := branchFns.push stopFn
      branchTys := branchTys.push [wrapTy K, schedTy]
      branchSigs := branchSigs.push ([wrapTy K, schedTy], VTy.void)
    let ps := Γ.take a
    let dflt (params : List VTy) (τ : VTy) : Except String Expr :=
      match Suspend.coreDefault Sinf params 0 τ with
      | some d => pure d
      | none => throw s!"internal error: lowering {gname}: no initial value for a slot of type {repr τ}"
    -- the frame's slots after the parameters: the function's own, then the
    -- pass's temporaries
    let tempTys := (low.fields.drop (2 + sites + 2 * arms + a + (fn.nslots - a)))
    -- each function keeps its parameters and the transient slots it uses
    let resumeLike (name : String) (lf : Suspend.LFn) : Except String Fn := do
      let inits ← (lf.slots.drop (a + 2)).mapM (dflt (lf.slots.take (a + 2)))
      return { name, arity := a + 2, nslots := lf.slots.length, decides := false, writes := true,
               body := initPrefixE (a + 2) inits lf.body }
    fns := fns.set! gi (← resumeLike gname low.body)
    slotTys := slotTys.set! gi low.body.slots
    fsigs := fsigs.set gi (frameTy j :: schedTy :: ps, .int)
    frameClasses := frameClasses.push low.fields
    -- `g$new(sched, params…)`: the frame, with the arguments and initial
    -- values (a non-generic callee's frame field starts as the scheduler)
    let childTys := low.fields.drop 2 |>.take sites
    let nps := schedTy :: ps
    let newBody : Expr := .heap (.new (tagBase + j))
      ([Suspend.int 0, ← dflt nps ρ] ++ childTys.map (fun τ => match τ with
          | .ref _ _ => Expr.local 0
          | τ => Expr.lit τ.default) ++
        List.replicate (2 * arms) (Suspend.int 0) ++
        (List.range a).map (fun i => Expr.local (i + 1)) ++ ds.map (Suspend.shift 1) ++
        (← tempTys.mapM (dflt nps)))
    newFns := newFns.push { name := s!"{gname}$new", arity := a + 1, nslots := a + 1, decides := false,
                            writes := true, body := newBody }
    newTys := newTys.push nps
    -- `g$reset(frame, params…)`: the frame, made ready for another call
    let resetBody := Suspend.seqVoid (.heap (.set Suspend.pcF) [.local 0, Suspend.int 0] ::
      (List.range a).map fun i => .heap (.set (Suspend.slotBaseOf sites arms + i)) [.local 0, .local (i + 1)])
    newFns := newFns.push { name := s!"{gname}$reset", arity := a + 1, nslots := a + 1, decides := false,
                            writes := true, body := resetBody }
    newTys := newTys.push (frameTy j :: ps)
    -- `g$cancel(frame, sched, params…)`: unwinds it
    newFns := newFns.push (← resumeLike s!"{gname}$cancel" low.cancel)
    newTys := newTys.push low.cancel.slots
    -- `g$result(frame)`
    newFns := newFns.push { name := s!"{gname}$result", arity := 1, nslots := 1, decides := false,
                            writes := false, body := .heap (.get Suspend.resF) [.local 0] }
    newTys := newTys.push [frameTy j]
    -- the arms of its `sync`s and `race`s
    for ((res, can), i) in low.arms.zipIdx do
      armFns := armFns.push (← resumeLike s!"{gname}$arm{i}" res)
      armFns := armFns.push (← resumeLike s!"{gname}$arm{i}$cancel" can)
      armTys := armTys.push res.slots
      armTys := armTys.push can.slots
      armSigs := armSigs.push (frameTy j :: schedTy :: ps, .int)
      armSigs := armSigs.push (frameTy j :: schedTy :: ps, VTy.void)
    -- its refined calls' helpers (#171), whose slots are their parameters
    -- (one calling a <decides> method can fail too, #179)
    for ((body, vps, vτ), i) in low.vias.zipIdx do
      let canFail := (Suspend.callsOf body).any fun (g, _) =>
        if g < fns.size then ((fns[g]?).map (·.decides)).getD false
        else if selfBase ≤ g then ((selfFns[g - selfBase]?).map (·.decides)).getD false
        else false
      armFns := armFns.push { name := s!"{gname}$via{i}", arity := vps.length, nslots := vps.length,
                              decides := canFail, writes := true, body }
      armTys := armTys.push vps
      armSigs := armSigs.push (vps, vτ)
  -- each root's trampoline, which resumes it with its parameters from its
  -- frame, and `start`, which registers it with the scheduler and runs it
  -- up to its first suspension point (a root that is done has its
  -- suspension point set to -1, and a done root lets the scheduler make
  -- another pass in the same tick, for the tasks waiting for it)
  let mut rootFns : Array Fn := #[]
  let mut rootTys : Array (List VTy) := #[]
  for k in List.range roots.size do
    let j := rootJ k
    let (ri, _, _) := roots[k]!
    let (_, _, sites, arms) := parts[j]!
    let a := fns[ri]!.arity - 2
    let pass := (List.range a).map fun i => Expr.heap (.get (Suspend.slotBaseOf sites arms + i)) [.local 0]
    -- (the task is the root's first parameter; it is marked running while
    -- the root runs, so that cancelling it from inside waits until it
    -- suspends)
    let task : Expr := .heap (.get (Suspend.slotBaseOf sites arms)) [.local 0]
    let trampBody : Expr := Suspend.seqVoid [
      .heap (.set runningF) [task, .lit (.logic true)],
      .assign 2 (.call ri (.local 0 :: .local 1 :: pass)),
      .heap (.set runningF) [task, .lit (.logic false)]] |> fun e => Expr.seq e (.local 2)
    rootFns := rootFns.push { name := s!"$spawn{k}$tramp", arity := 2, nslots := 3, decides := false, writes := true,
                              body := initPrefixE 2 [Suspend.int 0] trampBody }
    rootTys := rootTys.push [frameTy j, schedTy, .int]
    let start : Expr := Suspend.seqVoid [
      .call linkIdx [.local 0, .local 1],
      .heap (.set rootF) [.heap (.get (Suspend.slotBaseOf sites arms)) [.local 1], .prim .mkSome [.local 1]],
      .assign 2 (.call (trampOf k) [.local 1, .local 0]),
      .ite (.prim .eq [.local 2, Suspend.int 1])
        (.seq (Suspend.seqVoid [.heap (.set Suspend.pcF) [.local 1, Suspend.int (-1)],
          .heap (.set progressF) [.local 0, .lit (.logic true)], .heap (.set deadF) [.local 0, .lit (.logic true)]])
          Suspend.vd) Suspend.vd]
    rootFns := rootFns.push { name := s!"$spawn{k}$start", arity := 2, nslots := 3, decides := false, writes := true,
                              body := initPrefixE 2 [Suspend.int 0] start }
    rootTys := rootTys.push [schedTy, frameTy j, .int]
  -- the scheduler's roots are a list of cells `[root, next]`, so that
  -- adding one costs one cell (an array would be copied, and C keeps every
  -- copy): `$link(sched, root)` adds one at the end
  let cellTag := tagBase + L + B
  let cellTy : VTy := .ref [cellTag] []
  let nextF := 1
  -- (the last cell is read in the condition and written after it: a write
  -- in a condition makes the reference interpreter keep the heap as it
  -- was, for the rollback, and so copy it, once per root, #215; the slot
  -- it is read into starts as a cell of its own, as a slot of a reference
  -- type must)
  let linkBody : Expr := Suspend.seqVoid [
    .ite (.assign 3 (.prim .query [.heap (.get tailF) [.local 0]]))
      (.seq (.heap (.set nextF) [.local 3, .prim .mkSome [.local 2]]) Suspend.vd)
      (.seq (.heap (.set headF) [.local 0, .prim .mkSome [.local 2]]) Suspend.vd),
    .heap (.set tailF) [.local 0, .prim .mkSome [.local 2]]]
  let linkFn : Fn := { name := "$link", arity := 2, nslots := 4, decides := false, writes := true,
                       body := initPrefixE 2 [.heap (.new cellTag) [.local 1, .lit .none],
                         .heap (.new cellTag) [.local 1, .lit .none]] linkBody }
  fns := fns ++ newFns ++ selfFns ++ rootFns ++ [linkFn] ++ branchFns ++ armFns
  slotTys := slotTys ++ newTys ++ selfTys ++ rootTys ++ [[schedTy, rootAny, cellTy, cellTy]] ++ branchTys ++ armTys
  fsigs := fsigs ++ extraSigs.toList ++ selfSigs.toList ++ rootSigs.toList ++ [([schedTy, rootAny], VTy.void)] ++
    branchSigs.toList ++ armSigs.toList
  -- the wrappers' classes, after the frames', then the cells'
  for K in List.range B do
    frameClasses := frameClasses.push [.int, frameTy branchHome[K]!]
  frameClasses := frameClasses.push [rootAny, .opt cellTy]
  classTable := classTable.set schedTag (((classTable[schedTag]!).set headF (.opt cellTy)).set tailF (.opt cellTy))
  -- a task's root: the type of its `Root` field (in every class that has it)
  for d in env.classes do
    if let some ri := (env.fields d).findIdx? (·.1 == "$Root") then
      classTable := classTable.set (env.tagOf d) ((classTable[env.tagOf d]!).set ri (.opt rootAny))
  -- cancelling (#156): `$cancelRoot(sched, root)` unwinds a root that is
  -- not done, through its kind's cancel function (a spawned task's root
  -- also marks its task cancelled), and marks it done
  let cancelRootIdx := fns.size
  let cancelTOf (k : Nat) : Nat := cancelRootIdx + 1 + k
  let cancelWOf (K : Nat) : Nat := cancelRootIdx + 1 + roots.size + K
  let dispatchCancel : Expr := (List.range roots.size).foldr (fun k acc =>
      Expr.ite (.heap (.isTag [tagBase + rootJ k]) [.local 1]) (.call (cancelTOf k) [.local 1, .local 0]) acc)
    ((List.range B).foldr (fun K acc =>
      Expr.ite (.heap (.isTag [wrapTag K]) [.local 1]) (.call (cancelWOf K) [.local 1, .local 0]) acc) Suspend.vd)
  let cancelRootBody : Expr := .ite (.prim .ne [.heap (.get Suspend.pcF) [.local 1], Suspend.int (-1)])
    (.seq (Suspend.seqVoid [dispatchCancel, .heap (.set Suspend.pcF) [.local 1, Suspend.int (-1)],
      .heap (.set deadF) [.local 0, .lit (.logic true)], .heap (.set progressF) [.local 0, .lit (.logic true)]])
      Suspend.vd) Suspend.vd
  let cancelRootFn : Fn := { name := "$cancelRoot", arity := 2, nslots := 2, decides := false, writes := true, body := cancelRootBody }
  let mut cancelFns : Array Fn := #[cancelRootFn]
  let mut cancelTys : Array (List VTy) := #[[schedTy, rootAny]]
  let mut cancelSigs : Array (List VTy × VTy) := #[([schedTy, rootAny], VTy.void)]
  for k in List.range roots.size do
    let j := rootJ k
    let (ri, _, _) := roots[k]!
    let (_, _, sites, arms) := parts[j]!
    let a := fns[ri]!.arity - 2
    let pass := (List.range a).map fun i => Expr.heap (.get (Suspend.slotBaseOf sites arms + i)) [.local 0]
    let task : Expr := .heap (.get (Suspend.slotBaseOf sites arms)) [.local 0]
    let cbody : Expr := Suspend.seqVoid [.call (nFns + 4 * j + 2) (.local 0 :: .local 1 :: pass),
      .heap (.set tCancelledF) [task, .lit (.logic true)], .heap (.set tDoneF) [task, .lit (.logic true)]]
    let cfn : Fn := { name := s!"$spawn{k}$cancelT", arity := 2, nslots := 2, decides := false, writes := true, body := cbody }
    cancelFns := cancelFns.push cfn
    cancelTys := cancelTys.push [frameTy j, schedTy]
    cancelSigs := cancelSigs.push ([frameTy j, schedTy], VTy.void)
  for K in List.range B do
    let (armRes, doneA, pass) := branchInfo[K]!
    let fr : Expr := .heap (.get 1) [.local 0]
    let pass := pass.map fun e => match e with
      | .heap op _ => Expr.heap op [fr]
      | e => e
    let wbody : Expr := .ite (.prim .eq [.heap (.get doneA) [fr], Suspend.int 0])
      (.seq (Suspend.seqVoid [.call (armRes + 1) (fr :: .local 1 :: pass), .heap (.set doneA) [fr, Suspend.int 2]])
        Suspend.vd) Suspend.vd
    let wfn : Fn := { name := s!"$branch{K}$cancelT", arity := 2, nslots := 2, decides := false, writes := true, body := wbody }
    cancelFns := cancelFns.push wfn
    cancelTys := cancelTys.push [wrapTy K, schedTy]
    cancelSigs := cancelSigs.push ([wrapTy K, schedTy], VTy.void)
  fns := fns ++ cancelFns
  slotTys := slotTys ++ cancelTys
  fsigs := fsigs ++ cancelSigs.toList
  -- `T.Cancel()` (the mark `$cancelMark(T)`, in suspends code, whose slot 1
  -- is the scheduler): a task that is not done is cancelled now, or, when
  -- it is the one running (it cancels itself), at its next suspension
  let cancelMark := idxOf "$cancelMark"
  let cancelAt (t : Expr) : Expr :=
    .ite (.prim .eq [.heap (.get tDoneF) [t], .lit (.logic false)])
      (.seq (.ite (.prim .query [.heap (.get runningF) [t]])
        (.seq (.heap (.set cancelCurF) [.local 1, .lit (.logic true)]) Suspend.vd)
        (.seq (.ite (.call cancelRootIdx [.local 1, .prim .query [.heap (.get rootF) [t]]]) Suspend.vd Suspend.vd)
          Suspend.vd)) Suspend.vd) Suspend.vd
  let replCancel : List Expr → Expr := fun es => match es with
    | [t] => cancelAt t
    | _ => .prim .userErr []
  fns := fns.map fun fn => { fn with body := Suspend.substCall cancelMark replCancel fn.body }
  -- a suspends `Main` runs under the scheduler: a loop of ticks; in each,
  -- passes that resume `Main` and then every root that is not done, again
  -- while a root ends; between ticks the clock moves to the earliest tick
  -- a sleeping task waits for (none: no task can go on)
  if mainSig.suspends then
    let j := mainJ
    let runIdx := fns.size
    let sch : Expr := .local 0
    -- slots: sched, Main's frame, a status, Main done, a root, the next
    -- cell, a cell, another cell (a root that ended is recorded in the
    -- scheduler's `deadF`)
    let st := 2
    let mainDone := 3
    let r := 4
    let cur := 5
    let c := 6
    let n := 7
    let dispatch : Expr := ((List.range roots.size).foldr (fun k acc =>
      Expr.ite (.heap (.isTag [tagBase + rootJ k]) [.local r]) (.call (trampOf k) [.local r, sch]) acc)
      ((List.range B).foldr (fun K acc =>
        Expr.ite (.heap (.isTag [wrapTag K]) [.local r]) (.call (wrapFnBase + 3 * K) [.local r, sch]) acc)
        (.prim .userErr [])))
    let rootOf (cell : Expr) : Expr := .heap (.get 0) [cell]
    let dead (cell : Expr) : Expr := .prim .eq [.heap (.get Suspend.pcF) [rootOf cell], Suspend.int (-1)]
    -- (each cell's next is read after its root ran, so that the roots it
    -- added run in this pass too)
    let pollRoots : List Expr := if rootTags.isEmpty then [] else [
      .assign cur (.heap (.get headF) [sch]),
      .loop (Suspend.seqVoid [
        .ite (.assign c (.prim .query [.local cur])) Suspend.vd .brk,
        .assign r (rootOf (.local c)),
        .ite (.prim .ne [.heap (.get Suspend.pcF) [.local r], Suspend.int (-1)])
          (.seq (Suspend.seqVoid [.assign st dispatch,
            -- (a root asked to be cancelled: awaiting a cancelled task, or
            -- cancelling its own)
            .ite (.prim .query [.heap (.get cancelCurF) [sch]])
              (.seq (Suspend.seqVoid [.heap (.set cancelCurF) [sch, .lit (.logic false)],
                .call cancelRootIdx [sch, .local r]]) Suspend.vd) Suspend.vd,
            .ite (.prim .eq [.local st, Suspend.int 1])
              (.seq (Suspend.seqVoid [.heap (.set Suspend.pcF) [.local r, Suspend.int (-1)],
                .heap (.set progressF) [sch, .lit (.logic true)], .heap (.set deadF) [sch, .lit (.logic true)]]) Suspend.vd)
              Suspend.vd]) Suspend.vd) Suspend.vd,
        .assign cur (.heap (.get nextF) [.local c])])]
    let pass : Expr := .loop (Suspend.seqVoid ([
      .heap (.set progressF) [sch, .lit (.logic false)],
      .heap (.set 1) [sch, Suspend.int (-1)],
      .assign st (.call mainSig.idx [.local 1, sch]),
      .ite (.prim .eq [.local st, Suspend.int 1]) (.seq (.assign mainDone (Suspend.int 1)) .brk) Suspend.vd,
      -- (`Main` awaited a cancelled task: it is cancelled, and so the program ends)
      .ite (.prim .query [.heap (.get cancelCurF) [sch]])
        (.seq (Suspend.seqVoid [.heap (.set cancelCurF) [sch, .lit (.logic false)],
          .call (nFns + 4 * j + 2) [.local 1, sch], .assign mainDone (Suspend.int 1)]) .brk) Suspend.vd] ++
      pollRoots ++
      [.ite (.prim .query [.heap (.get progressF) [sch]]) Suspend.vd .brk]))
    -- (between ticks, after a root ended, the cells of the roots that are
    -- done are unlinked: no allocation but the new end)
    let compact : List Expr := if rootTags.isEmpty then [] else [
      .ite (.prim .query [.heap (.get deadF) [sch]]) (.seq (Suspend.seqVoid [
        .heap (.set deadF) [sch, .lit (.logic false)],
        .loop (Suspend.seqVoid [
          .ite (.assign c (.prim .query [.heap (.get headF) [sch]])) Suspend.vd .brk,
          .ite (dead (.local c)) (.seq (.heap (.set headF) [sch, .heap (.get nextF) [.local c]]) Suspend.vd) .brk]),
        .ite (.assign c (.prim .query [.heap (.get headF) [sch]]))
          (.seq (Suspend.seqVoid [
            .loop (Suspend.seqVoid [
              .ite (.assign n (.prim .query [.heap (.get nextF) [.local c]])) Suspend.vd .brk,
              .ite (dead (.local n))
                (.seq (.heap (.set nextF) [.local c, .heap (.get nextF) [.local n]]) Suspend.vd)
                (.seq (.assign c (.local n)) Suspend.vd)]),
            .heap (.set tailF) [sch, .prim .mkSome [.local c]]]) Suspend.vd)
          (.seq (.heap (.set tailF) [sch, .lit .none]) Suspend.vd)]) Suspend.vd) Suspend.vd]
    let run : Expr := Suspend.seqVoid [.loop (Suspend.seqVoid (compact ++ [pass,
      .ite (.prim .eq [.local mainDone, Suspend.int 1]) .brk Suspend.vd,
      .ite (.prim .lt [.heap (.get 1) [sch], Suspend.int 0]) (.seq (.prim .userErr []) Suspend.vd) Suspend.vd,
      .heap (.set 0) [sch, .heap (.get 1) [sch]]]))]
    let cellInit : Expr := .heap (.new cellTag) [.local 1, .lit .none]
    fns := fns.push { name := "$Run", arity := 2, nslots := 8, decides := false, writes := true,
                      body := initPrefixE 2 [Suspend.int 0, Suspend.int 0, .local 1, .lit .none,
                        cellInit, cellInit] run }
    slotTys := slotTys.push [schedTy, frameTy j, .int, .int, rootAny, .opt cellTy, cellTy, cellTy]
    fsigs := fsigs ++ [([schedTy, frameTy j], VTy.void)]
    -- (the prelude calls a function without arguments, `checkPrelude`)
    -- (the scheduler is its class's prototype, so that immediate code can
    -- spawn on it)
    fns := fns.push { name := "$Start", arity := 0, nslots := 0, decides := false, writes := true,
                      body := .call runIdx [schedLit, .call (nFns + 4 * j) [schedLit]] }
    slotTys := slotTys.push []
    fsigs := fsigs ++ [([], VTy.void)]
    mainCall := .call (runIdx + 1) []
  return (fns, slotTys, fsigs, classTable, frameClasses, mainCall)

/-- Whether `e` itself prints (`Print`), for `checkEager`. -/
partial def exprPrints : Expr → Bool
  | .print _ => true
  | .assign _ e | .ret e | .loop e => exprPrints e
  | .seq a b => exprPrints a || exprPrints b
  | .prim _ es | .heap _ es | .call _ es => es.any exprPrints
  | .ite c t e => exprPrints c || exprPrints t || exprPrints e
  | .forE _ it f b => exprPrints it || exprPrints f || exprPrints b
  | _ => false

/-- (#235) A recursive function with several values is computed at its
    call as `F$all`, all its values at once, so nothing it may run may print
    or call `Err()`. Followed through its Verse Core code, so through every
    call it may make: functions, methods (each implementation a dispatch
    may pick), function values (each function of that type used as a
    value), constructors (field defaults, `block:` clauses), constants, and
    parameter defaults (elaborated at the call). `errs` says where each
    function elaborated from the program calls `Err()`. -/
def checkEager (fns : Array Fn) (errs : Array (Option Pos)) (posOf : String → Option Pos) :
    Except String Unit := do
  for i in List.range fns.size do
    let fn := fns[i]!
    if !fn.name.endsWith "$all" then continue
    let g := String.ofList (fn.name.toList.take (fn.name.length - 4))
    let loc := ((posOf g).map (·.show ++ ": ")).getD ""
    let mut seen : Array Bool := Array.replicate fns.size false
    let mut todo : List Nat := [i]
    seen := seen.set! i true
    while !todo.isEmpty do
      let j := todo.head!
      todo := todo.tail!
      let fj := fns[j]!
      let shown := if fj.name.endsWith ".$block" then
          s!"the block: of {String.ofList (fj.name.toList.take (fj.name.length - 7))}" else fj.name
      let via := if fj.name == fn.name then "" else s!" ({shown} does)"
      let what? : Option String :=
        if exprPrints fj.body then some "print"
        else if let some (some _) := errs[j]? then some "call Err()" else none
      if let some what := what? then
        throw s!"{loc}{g} has several values and is recursive, or called by a recursive one, and it may {what}{via}: such a function must be <computes>, keep no local state, and reach nothing that prints or calls Err(), as all its values are computed at a call (#235)"
      for (f, _) in Suspend.callsOf fj.body do
        if f < fns.size && !seen[f]! then
          seen := seen.set! f true
          todo := todo ++ [f]

/-- Elaborate a parsed program into a Verse Core program that passes `Prog.check`
    and `Prog.checkTypes`. -/
def elabProgramCore (allTops0r : List STop) (opts : Options := {}) : Except String Compiled := do
  -- rationals (#116): the helpers, for a program that may use them
  let isRatMarker : STop → Bool := fun
    | .const _ n _ _ => n == ratMarker || n == replaceAllMarker
    | _ => false
  let usesReplaceAll := allTops0r.any (fun | .const _ n _ _ => n == replaceAllMarker | _ => false) || opts.entry.isSome
  let usesRat := allTops0r.any isRatMarker || opts.entry.isSome
  -- (a type of the program's own cannot take a built-in type's name)
  for t in allTops0r do
    match t with
    | .const p n _ (.structDef ..) | .const p n _ (.enumDef ..) | .classDef p n .. =>
      if ("char32" :: typeNames).contains n then throw s!"{p.show}: {n} is a built-in type"
    | _ => pure ()
  let helpers ← if usesRat then ratTops else pure []
  let helpers := helpers ++ (← if usesReplaceAll then replaceAllTops else pure [])
  -- concurrency (#156): the helpers, for a program with a <suspends> function
  -- (and `subscribable_event`, which extends the concurrency prelude's
  -- `event`, #210)
  -- (unless the program defines its own)
  let defines0 (n : String) : Option Pos := allTops0r.findSome? fun
    | .classDef p m .. | .fn p m .. | .const p m .. => if m == n then some p else none
  let usesSub := (defines0 "subscribable_event").isNone && allTops0r.any (·.usesType "subscribable_event")
  if usesSub then
    if let some p := defines0 "cancelable" then
      throw s!"{p.show}: cancelable is the type subscribable_event's Subscribe gives: a program that uses subscribable_event cannot define its own (#210)"
  let usesConc := usesSub || allTops0r.any fun
    | .fn _ _ _ _ effs _ _ => effs.contains "suspends"
    | .classDef _ _ _ _ _ _ _ _ ms => ms.any fun
      | .fn _ _ _ _ effs _ _ => effs.contains "suspends"
      | _ => false
    | _ => false
  let helpers := helpers ++ (← if usesConc then concTops else pure []) ++ (← if usesSub then subTops else pure [])
  let allTops000 := allTops0r.filter (!isRatMarker ·)
  -- modules (#112): every reference to a member, qualified (the entry
  -- expression's too)
  let rawEntry : List STop := match opts.entry with
    | some e => [.fn e.pos "$Do" [] [] ["decides"] (.name "void") (.app e.pos (.ident e.pos "$Show") [e] false)]
    | none => []
  let resolved ← resolveModules (allTops000 ++ rawEntry)
  -- functions with several values (#235): inlined at their calls
  let resolved ← Choice.inlineMulti resolved
  -- the branches of casts that refine type arguments, as functions (#243)
  -- (in front, as the entry expression is the end)
  let resolved := Refine.functions opts.castRequests resolved ++ resolved
  -- (the helpers after: they name nothing of the program's)
  -- function values (#210): the function types' interfaces, and a class
  -- for each function used as a value
  -- (the entry expression is scanned too)
  let allTops00 := FnValues.desugar (resolved.take (resolved.length - rawEntry.length) ++ helpers)
    (resolved.drop (resolved.length - rawEntry.length)) (opts.fnRequests.map fun (n, t) => (n, t.toSTy))
  let entryTop := resolved.drop (resolved.length - rawEntry.length)
  -- the command line: `Args`, and an entry expression
  let defines (n : String) := allTops00.any fun
    | .fn _ m .. | .const _ m .. | .classDef _ m .. => m == n
  let argsTop : List STop :=
    match opts.args with
    | some as =>
      if defines "Args" then []
      else [.const { line := 0, col := 0 } "Args" (some (.arr (.name "string")))
              (.arrayLit { line := 0, col := 0 } (as.map fun a => .str { line := 0, col := 0 } [.text a]))]
    | none => []
  -- overloaded methods (#106): a method name declared with two or more
  -- parameter lists is renamed, in every class and interface, by its list
  -- (`M$ovN`): an override has its method's list, so its name too
  -- (up to the names of type parameters: the class's and the method's own,
  -- each by its place, so a generic override that renames them has its
  -- method's list)
  let sigText (ctps : List TParam) (mtps : List TParam) (ps : List SParam) : String :=
    let ρ : List (String × STy) :=
      ((ctps.zip (List.range ctps.length)).map fun (tp, i) => (tp.name, STy.name s!"$c{i}")) ++
      ((mtps.zip (List.range mtps.length)).map fun (tp, i) => (tp.name, STy.name s!"$m{i}"))
    -- (and `string` is `[]char`)
    let ρ := ρ ++ [("string", STy.arr (.name "char"))]
    reprStr (ps.map fun q => (q.named, if q.named then q.name else "", q.ty.substNames ρ))
  -- (per class hierarchy: classes and interfaces connected by inheritance,
  -- so unrelated classes' methods of one name are not overloads)
  let classDefs : List (String × List TParam × List STy × List STop) :=
    (allTops00 ++ argsTop ++ entryTop).filterMap fun
      | .classDef _ n tps _ parents _ _ _ methods => some (n, tps, parents, methods)
      | _ => none
  let parentName : STy → Option String := fun | .name q => some q | .app q _ => some q | _ => none
  let mut hier : List (String × String) := classDefs.map fun (n, _) => (n, n)
  for _ in [0:classDefs.length + 1] do
    -- (until a pass joins nothing: a pass per class made it cubic)
    let mut joined := false
    for (n, _, ps, _) in classDefs do
      for q in ps.filterMap parentName do
        match hier.lookup n, hier.lookup q with
        | some a, some b =>
          if a != b then
            let r := if a < b then a else b
            hier := hier.map fun (x, h) => if h == a || h == b then (x, r) else (x, h)
            joined := true
        | _, _ => pure ()
    if !joined then break
  let hierOf (n : String) : String := (hier.lookup n).getD n
  -- each class's ancestors (itself first), each with its type parameters in
  -- the class's terms
  let infoOf (n : String) := (classDefs.find? (·.1 == n)).map fun (_, tps, ps, ms) => (tps, ps, ms)
  let mut anc : List (String × List (String × List (String × STy))) :=
    classDefs.map fun (n, _) => (n, [(n, [])])
  for _ in [0:classDefs.length + 1] do
    let mut changed := false
    for (n, _, ps, _) in classDefs do
      let mine := (anc.lookup n).getD []
      let mut add : List (String × List (String × STy)) := []
      for pty in ps do
        let (q, args) := match pty with | .app q as => (q, as) | .name q => (q, []) | _ => ("", [])
        let qtps := ((infoOf q).map (·.1)).getD []
        let σq : List (String × STy) := (qtps.map (·.name)).zip args
        for (y, σy) in (anc.lookup q).getD [] do
          if !(mine ++ add).any (·.1 == y) then
            let σ := if y == q then σq else σy.map fun (v, t) => (v, t.substNames σq)
            add := add ++ [(y, σ)]
      if !add.isEmpty then
        anc := anc.map fun (x, a) => if x == n then (x, a ++ add) else (x, a)
        changed := true
    if !changed then break
  -- the non-override declarations of a method in a class: its lists
  let ownLists (y mn : String) : List (List TParam × List SParam) := ((infoOf y).map fun (_, _, ms) =>
    ms.filterMap fun
      | .fn _ x ps mtps effs .. => if x == mn && !effs.contains "override" then some (mtps, ps) else none
      | _ => none).getD []
  let decls : List ((String × String) × String) := classDefs.flatMap fun (cn, ctps, _, methods) =>
    methods.filterMap fun
      -- (an override joins its method's list: only the others make lists)
      | .fn _ mn ps mtps effs .. =>
        if mn == "$block" || mn.startsWith "(" || effs.contains "override" then none
        else some ((hierOf cn, mn), sigText ctps mtps ps)
      | _ => none
  let keys := (decls.map (·.1)).eraseDups
  -- (a name is overloaded where some class's ancestors declare two or more
  -- of its lists: siblings' own lists are not overloads)
  let listsSeen (n mn : String) : List String :=
    (((anc.lookup n).getD []).flatMap fun (y, _) =>
      let ytps := ((infoOf y).map (·.1)).getD []
      (ownLists y mn).map fun (mtps, ps) => sigText ytps mtps ps).eraseDups
  let mov : List ((String × String) × List String) := keys.filterMap fun key =>
    let sigs := ((decls.filter (·.1 == key)).map (·.2)).eraseDups
    if sigs.length > 1 && classDefs.any (fun (n, _) => hierOf n == key.1 && (listsSeen n key.2).length > 1) then
      some (key, sigs)
    else none
  let mangle (cn mn : String) (ctps mtps : List TParam) (ps : List SParam) (isOverride : Bool)
      (within : Option String) : String :=
    match mov.lookup (hierOf cn, mn) with
    | none => mn
    | some sigs =>
      if !isOverride then s!"{mn}$ov{(sigs.idxOf? (sigText ctps mtps ps)).getD 0}"
      else
        -- an override: the ancestor list it has, each in this class's terms
        -- (through the type arguments the class gives its parents)
        let mine := sigText ctps mtps ps
        -- (a qualified `(q:)M`: only `q`'s lists, and those above it)
        let none' : List (String × List (String × STy)) := []
        let ups0 : List (String × List (String × STy)) := ((anc.lookup cn).getD none').drop 1
        let ups : List (String × List (String × STy)) := match within with
          | some q =>
            let above : List String := ((anc.lookup q).getD none').map Prod.fst
            ups0.filter fun u => u.1 == q || above.contains u.1
          | none => ups0
        let cands : List (Nat × String × Nat) := ups.flatMap fun (y, σ) =>
          let ytps := ((infoOf y).map (·.1)).getD []
          (ownLists y mn).filterMap fun (dmtps, dps) =>
            (sigs.idxOf? (sigText ytps dmtps dps)).map fun k =>
              -- (its own type parameters renamed apart first: the class's
              -- arguments must not capture them)
              let apart : List (String × STy) := (dmtps.zip (List.range dmtps.length)).map fun (tp, i) =>
                (tp.name, STy.name s!"$own{i}")
              let dmtps' := (dmtps.zip (List.range dmtps.length)).map fun (tp, i) => { tp with name := s!"$own{i}" }
              (k, sigText ctps dmtps' (dps.map fun q => { q with ty := (q.ty.substNames apart).substNames σ }), dps.length)
        match (cands.filter (·.2.1 == mine)).map (·.1) |>.eraseDups with
        | [k] => s!"{mn}$ov{k}"
        | _ =>
          match (cands.filter (·.2.2 == ps.length)).map (·.1) |>.eraseDups with
          | [k] => s!"{mn}$ov{k}"
          | _ => mn   -- refused below
  let mut tops1 : Array STop := #[]
  for t in allTops00 ++ argsTop ++ entryTop do
    match t with
    | .classDef cp n tps specs parents isI fields ovs methods =>
      let mut ms : Array STop := #[]
      for m in methods do
        match m with
        | .fn mp mn ps mtps effs ret body =>
          -- `(q:)M`, implementing `q`'s overload of `M` that has its list
          -- (#125): `(q:)M$ovK`
          let qual : Option (String × String) := if mn.startsWith "(" then
              match (mn.drop 1).toString.splitOn ":)" with
              | [q, m'] => some (q, m')
              | _ => none
            else none
          match qual with
          | some (q, m') =>
            -- (`q` above the class: otherwise the check below explains)
            let isAbove := (((anc.lookup n).getD []).drop 1).any (·.1 == q)
            if isAbove && (mov.lookup (hierOf n, m')).isSome then
              let k := mangle n m' tps mtps ps true (some q)
              if k == m' then
                throw s!"{mp.show}: ({q}:){m'} must have the parameters of one of {q}'s overloads of {m'}"
              ms := ms.push (.fn mp s!"({q}:){k}" ps mtps effs ret body)
            else ms := ms.push (.fn mp mn ps mtps effs ret body)
          | none =>
            ms := ms.push (.fn mp (mangle n mn tps mtps ps (effs.contains "override") none) ps mtps effs ret body)
        | m => ms := ms.push m
      tops1 := tops1.push (.classDef cp n tps specs parents isI fields ovs ms.toList)
    | t => tops1 := tops1.push t
  let allTops0 := tops1.toList
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
  -- (by the name as written: an overload's is its method's, #106)
  let declaresBase (n m : String) : Bool := ((cdef? n).map fun cd => cd.methods.any fun
    | .fn _ x .. => methodBase x == m
    | _ => false).getD false
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
      if qargs.length != qd.tps.length then
        throw s!"{p.show}: {q} takes {qd.tps.length} type argument(s), found {qargs.length}"
      -- (an interface's type arguments are its references'; one that extends
      -- a parametric interface gives it its own, unchanged, #53)
      if cd.isIface && qd.isIface && !qargs.isEmpty then
        let own := cd.tps.map (·.name)
        let given := qargs.map fun | .name x => x | _ => "?"
        if given != own then
          throw s!"{p.show}: interface {cd.name} must give {q} its own type parameters, in order, as in interface({q}({", ".intercalate own})) (#53)"

      if qd.isIface then ifaces := ifaces.push q
      else
        if cd.isIface then throw s!"{p.show}: interface {cd.name} cannot extend class {q}"
        if parent.isSome then throw s!"{p.show}: class {cd.name} has two superclasses (a class inherits from at most one)"
        if qd.specs.contains "final" then throw s!"{p.show}: class {q} is <final>: it cannot be inherited from"
        parent := some q
    let info : ClassInfo := { parent, ifaces := ifaces.toList, isIface := cd.isIface,
                              isAbstract := cd.specs.contains "abstract", isFinal := cd.specs.contains "final" }
    cinfo := cinfo.push (cd.name, info)
  let henv : TyEnv := { classes := cdefs.map (·.name), cinfo := cinfo.toList,
                        cinfoMap := cinfo.foldl (fun m (n, i) => m.insert n i) {} }
  let henv : TyEnv := { henv with supersMap := henv.classes.foldl (fun m d => m.insert d (henv.supers d)) {} }
  let directUp (n : String) : List String := (henv.info n).parent.toList ++ (henv.info n).ifaces
  for cd in cdefs do
    let mut seen : List String := []
    let mut frontier := directUp cd.name
    for _ in [0:cdefs.length + 1] do
      let new := frontier.filter (!seen.contains ·)
      seen := seen ++ new
      frontier := new.flatMap directUp
    if seen.contains cd.name then throw s!"{cd.pos.show}: {cd.name} inherits from itself"
  -- the type arguments `c` gives `T` above it, as written in terms of `c`'s
  -- type parameters (through parents of both kinds, #39, #53)
  let supArgsSTy (c T : String) : Option (List STy) := Id.run do
    let mut frontier : List (String × List STy) :=
      [(c, ((cdef? c).map fun cd => cd.tps.map fun tp => STy.name tp.name).getD [])]
    for _ in [0:cdefs.length + 1] do
      if let some (_, a) := frontier.find? (·.1 == T) then return some a
      frontier := frontier.flatMap fun (x, xa) => match cdef? x with
        | some xd =>
          let σ := (xd.tps.map (·.name)).zip xa
          (xd.parents.zip xd.parentArgs).map fun (q, qa) => (q, qa.map (·.substNames σ))
        | none => []
    return none
  -- the fields of each class: its superclass's, then those of the
  -- interfaces above it that are not there yet (once, along a diamond), then
  -- its own (an `<override>` field gives an inherited one a new default)
  let mut full : Array (String × List (String × STy × Option SExpr × Bool)) := #[]
  let mut fieldOverrides : Array (Pos × String × String × STy) := #[]
  let mut defaultClashes : Array String := #[]
  -- (each class's fields by name too: lookups in `full` made this cubic)
  let mut fullMap : Std.HashMap String (List (String × STy × Option SExpr × Bool)) := {}
  for _ in [0:cdefs.length + 1] do
    -- (until a pass resolves nothing more, or every class is resolved)
    if full.size == cdefs.length then break
    let before := full.size
    for cd in cdefs do
      if fullMap.contains cd.name then continue
      let inherited? : Option (List (String × STy × Option SExpr × Bool)) :=
        match (henv.info cd.name).parent with
        | none => some []
        | some q =>
          -- in terms of this class's type parameters (#39)
          let qargs := ((cd.parents.zip cd.parentArgs).lookup q).getD []
          let σ := ((((cdef? q).map (·.tps)).getD []).map (·.name)).zip qargs
          fullMap[q]?.map fun fs => fs.map fun (f, sty, d, v) => (f, sty.substNames σ, d, v)
      let some inh := inherited? | continue
      -- the interfaces above must be resolved first
      let ifacesUp := ((henv.supers cd.name).drop 1).filter (henv.info · |>.isIface)
      if ifacesUp.any (fun i => !fullMap.contains i) then continue
      let mut fs : List (String × STy × Option SExpr × Bool) := inh
      -- each interface field not inherited through the class chain, once; its
      -- default is that of the most specific interface that gives one (as for
      -- methods, whatever the order of the parents)
      for i in ifacesUp do
        -- (in terms of this class's type parameters, #53)
        let iσ := ((((cdef? i).map (·.tps)).getD []).map (·.name)).zip ((supArgsSTy cd.name i).getD [])
        for (f, sty0, _, isVar) in fullMap[i]?.getD [] do
          let sty := sty0.substNames iσ
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
      -- (#209) each type parameter that is not one of its parent's type
      -- arguments as a whole: a hidden field holds a value of it, from
      -- which a method of the class, run by a dispatch that opens it, gets
      -- its slots of that type (`Sig.selfTps`)
      -- (only where an override, at or below, may need it)
      let methodsBelow := cdefs.any fun cd' => henv.isSub cd'.name cd.name &&
        cd'.methods.any fun | .fn _ _ _ _ effs .. => effs.contains "override" | _ => false
      if let some q := (henv.info cd.name).parent then
        let qargs := ((cd.parents.zip cd.parentArgs).lookup q).getD []
        for tp in (if methodsBelow then cd.tps else []) do
          if !qargs.any (fun | .name v => v == tp.name | _ => false) then
            fs := fs ++ [(s!"$w.{cd.name}.{tp.name}", .name tp.name, some (.ident cd.pos "$witness"), false)]
      full := full.push (cd.name, fs)
      fullMap := fullMap.insert cd.name fs
    if full.size == before then break
  let fullOf (n : String) := fullMap[n]?.getD []
  for cd in cdefs do
    for (f, _, _, _) in fullOf cd.name do
      if (henv.supers cd.name).any (declaresBase · f) then
        throw s!"{cd.pos.show}: '{f}' is both a field and a method of {cd.name}"
  -- the methods
  let mut expanded : Array STop := #[]
  let mut abstracts : Array (String × String) := #[]
  let mut overridePairs : Array (Pos × String × String) := #[]
  let mut implChecks : Array (Pos × String × String × String) := #[]
  -- constructor functions (#11): `K<constructor>(ps) := c:` and its items
  let ctorOf (t : STop) :
      Option (Pos × String × List SParam × List TParam × List String × String × List SExpr) :=
    match t with
    | .fn p k ps tps effs _ (.block _ items) =>
      match effs.find? (·.startsWith "$constructor:") with
      | some e => some (p, k, ps, tps, effs.filter (· != e), (e.drop "$constructor:".length).toString, items)
      | none => none
    | _ => none
  let ctors := allTops0.filterMap ctorOf
  for t in allTops0 do
    match t with
    | .classDef .. => pure ()
    | t => if (ctorOf t).isNone then expanded := expanded.push t
  let ctorTargs : List (String × List STy) := allTops0.filterMap fun
    | t@(.fn _ k _ _ _ (.app _ ts) _) => if (ctorOf t).isSome then some (k, ts) else none
    | _ => none
  expanded := expanded ++
    (← expandCtors ctors cdef? fullOf (fun c => henv.supers c) (fun k => (ctorTargs.lookup k).getD [])
      (allTops0.filterMap fun t => match t, ctorOf t with
        | .fn _ k _ _ _ (.app _ ts) _, some _ => some (k, ts)
        | .fn _ k _ _ _ _ _, some _ => some (k, [])
        | _, _ => none)).toArray
  for cd in cdefs do
    let n := cd.name
    let fs := fullOf n
    expanded := expanded.push (.const cd.pos n none (.structDef cd.pos cd.tps fs))
    let selfTy : STy := if cd.tps.isEmpty then .name n else .app n (cd.tps.map fun tp => STy.name tp.name)
    for (m, mi) in cd.methods.zip (List.range cd.methods.length) do
      match m with
      | .fn mp mn ps mtps effs ret body =>
        if fs.any (·.1 == methodBase mn) then throw s!"{mp.show}: '{methodBase mn}' is both a field and a method of {n}"
        if mn != "$block" && (cd.methods.take mi).any (fun | .fn _ x .. => x == mn | _ => false) then
          throw s!"{mp.show}: {n} defines {mn} twice with the same parameters"
        if ps.any (·.name == "Self") then throw s!"{mp.show}: a method parameter cannot be called Self"
        if builtins.contains (methodBase mn) || softBuiltins.contains (methodBase mn) then throw s!"{mp.show}: a method cannot be called {methodBase mn}, the name of a built-in function"
        for prm in ps do
          if fs.any (·.1 == prm.name) || (henv.supers n).any (declaresBase · prm.name) then
            throw s!"{mp.show}: parameter '{prm.name}' of {mn} is already a field or method of {n}; Verse does not allow shadowing"
        -- a class's `block:` clauses: run at construction, after those of the
        -- classes above it, so never overridden
        -- overriding (Book of Verse ch. 10: `M<override>`, the same signature)
        let isOverride := effs.contains "override"
        -- `(q:)M`: implements slot q of M (#70), q the interface that
        -- introduces M
        let qual? : Option (String × String) :=
          if mn.startsWith "(" then match (mn.drop 1).toString.splitOn ":)" with
            | [q, m'] => some (q, m')
            | _ => none
          else none
        if let some (q, m') := qual? then
          if !((henv.supers n).drop 1).contains q then
            throw s!"{mp.show}: ({q}:){m'}: {q} is not a class or interface above {n}"
          let roots := henv.rootsOf (declares · m') q
          let qualify := " or ".intercalate (roots.map fun r => s!"({r}:)")
          if roots.isEmpty then throw s!"{mp.show}: ({q}:){m'}: {q} has no method {m'}"
          if !declares q m' then
            throw s!"{mp.show}: ({q}:){m'}: {q} does not declare {m'} itself; qualify it with {qualify}"
          if roots != [q] then
            throw s!"{mp.show}: ({q}:){m'}: {q}'s {m'} overrides another; qualify it with the interface that introduces {m'}, {qualify}"
          if !isOverride then throw s!"{mp.show}: ({q}:){m'} must be marked <override>"
          if effs.contains "$abstract" then throw s!"{mp.show}: ({q}:){m'} needs a body"
          if cd.methods.any (fun | .fn _ x .. => x == m' | _ => false) then
            throw s!"{mp.show}: {n} implements {m'} both plainly and as ({q}:){m'}: give one or the other"
        -- what the method overrides: the declarations above it in its slots
        -- (for `(q:)m'`, those below q, and the `(q:)m'` above), and for a
        -- plain one the qualified implementations above too
        let ups1 := (henv.supers n).drop 1
        let overridden : List (String × String) :=
          if mn == "$block" then [] else match qual? with
          | some (q, m') =>
            (ups1.filter fun e => declares e m' && henv.isSub e q).map (·, m') ++
              (ups1.filter (declares · mn)).map (·, mn)
          | none =>
            (ups1.filter (declares · mn)).map (·, mn) ++
              ups1.flatMap fun e => (henv.rootsOf (declares · mn) n).filterMap fun r =>
                if declares e s!"({r}:){mn}" then some (e, s!"({r}:){mn}") else none
        match overridden with
        | [] =>
          if isOverride then
            if (henv.supers n).any (fun e => ((cdef? e).map fun ed => ed.methods.any fun
                | .fn _ x .. => x.startsWith s!"{mn}$ov" | _ => false).getD false) then
              throw s!"{mp.show}: {mn}<override> has the parameters of no overload of {mn} above {n}"
            throw s!"{mp.show}: {mn}<override> does not override an inherited method"
        | qs@((q, _) :: _) =>
          if !isOverride then throw s!"{mp.show}: {mn} is inherited from {q}: mark it {mn}<override> to override it"
          for (q, x) in qs do
            match (cdef? q).bind (methodNamed · x) with
            | some (.fn _ _ _ qtps qeffs _ _) =>
              if qeffs.contains "final" then throw s!"{mp.show}: {q}.{x} is <final>: it cannot be overridden"
              -- (a method with its own type parameters overrides one with as
              -- many, compared up to their names below)
              if qtps.length != mtps.length then
                throw s!"{mp.show}: {mn} has {mtps.length} type parameter(s) of its own, and {q}.{x}, which it overrides, {qtps.length}"
            | _ => pure ()
            overridePairs := overridePairs.push (mp, s!"{n}.{mn}", s!"{q}.{x}")
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
    -- (a `block:` is not a method: each class runs its own; a qualified
    -- `(q:)M` implements q's M, below)
    for mn in names.filter (fun x => x != "$block" && !x.startsWith "(") do
      let decls := ups.filter (declares · mn)
      -- each slot (#70): its implementation, as `Ctx.implFor?` chooses at a
      -- call, satisfies every declaration in the slot
      let roots := henv.rootsOf (declares · mn) cd.name
      let implAt (r e : String) : Option String :=
        if hasBody e s!"({r}:){mn}" then some s!"{e}.({r}:){mn}"
        else if hasBody e mn then some s!"{e}.{mn}" else none
      let clsOf (f : String) : String := (f.splitOn ".").head!
      let mut chosen : List String := []
      for r in roots do
        match henv.slotImpls (implAt r) ups r with
        | [] => throw s!"{cd.pos.show}: {cd.name} must implement {mn} (declared abstract in {r})"
        | f :: g :: _ =>
          throw s!"{cd.pos.show}: {cd.name} inherits {mn} from both {clsOf f} and {clsOf g}: override it in {cd.name}"
        | [f] =>
          chosen := chosen ++ [f]
          for q in decls.filter (henv.isSub · r) do
            if f != s!"{q}.{mn}" then implChecks := implChecks.push (cd.pos, cd.name, f, s!"{q}.{mn}")
      -- without a qualified implementation, one implementation for all slots
      let qualified := ups.any fun e => roots.any fun r => declares e s!"({r}:){mn}"
      match chosen.eraseDups with
      | f :: g :: _ =>
        if !qualified then
          throw s!"{cd.pos.show}: {cd.name} inherits {mn} from both {clsOf f} and {clsOf g}: override it in {cd.name}"
      | _ => pure ()
  let allTops := expanded.toList
  -- the type definitions: `name := struct …` and `name := enum …`
  let isTypeDef : STop → Bool
    | .const _ _ none (.structDef ..) | .const _ _ none (.enumDef ..) | .const _ _ none (.refineDef ..) => true
    | _ => false
  let tops := allTops.filter (!isTypeDef ·)
  let varFields : List (String × String) := cdefs.flatMap fun cd =>
    (fullOf cd.name).filterMap fun (f, _, _, isVar) => if isVar then some (cd.name, f) else none
  let uniques : List String := (cdefs.filter (·.specs.contains "unique")).map (·.name)
  let mut env : TyEnv := { classes := henv.classes, cinfo := henv.cinfo, cinfoMap := henv.cinfoMap,
                           classIx := henv.classes.zipIdx.foldl (fun m (n, i) => m.insert n i) {},
                           belowReady := true,
                           supersMap := henv.classes.foldl (fun m d => m.insert d (henv.supers d)) {},
                           belowMap := henv.classes.foldl (fun m d =>
                             let i := henv.info d
                             if i.isIface || i.isAbstract then m else
                             (henv.supers d).foldl (fun m T => m.insert T ((m[T]?.getD []) ++ [d])) m) {},
                           abstracts := abstracts.toList, fnRequests := opts.fnRequests,
                           castRequests := opts.castRequests }
  env := { env with varFields := varFields, uniques := uniques,
                    overriders := (overridePairs.toList.map fun (_, dm, _) => (dm.splitOn ".").headD "") ++
                      (implChecks.toList.map fun (_, _, impl, _) => (impl.splitOn ".").headD "") }
  -- the class whose code each inherited field default is (#39): the nearest
  -- one, the class's own first, that gives the field a default itself
  let homeOf (c f : String) : String :=
    ((henv.supers c).find? fun x =>
      ((cdef? x).map fun xd => xd.fields.any fun (g, _, d, _) => g == f && d.isSome).getD false).getD c
  env := { env with defaultHome := cdefs.flatMap fun cd =>
    (fullOf cd.name).filterMap fun (f, _, d, _) => d.map fun _ => ((cd.name, f), homeOf cd.name f) }
  for t in allTops do
    match t with
    | .const _ n none (.enumDef _ vals isOpen) =>
      env := { env with enums := env.enums ++ [(n, vals)],
                        openEnums := if isOpen then env.openEnums ++ [n] else env.openEnums }
    | .const _ n none (.structDef _ _ _) => env := { env with structs := env.structs ++ [(n, [])] }
    | .const p n none (.refineDef _ v sty conds) =>
      -- a refinement type (#136)
      let (base, _) ← (resolveTy env p sty).run {}
      env := { env with refines := env.refines ++ [(n, base, ← refineConds p v base conds)] }
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
  -- the type arguments of each parametric interface a class or interface
  -- lists as a parent (#53)
  let mut iargs : Array ((String × String) × List Ty) := #[]
  for cd in cdefs do
    for (q, qargs) in cd.parents.zip cd.parentArgs do
      if (henv.info q).isIface && !qargs.isEmpty then
        let cenv := { env with tvars := ((env.sparams.lookup cd.name).getD []).map fun (v, c) => (v, Ty.param v c) }
        let tys ← qargs.mapM fun sty => do
          let (ty, _) ← (resolveTy cenv cd.pos sty).run {}
          pure ty
        for (ty, (v, needComp)) in tys.zip ((env.sparams.lookup q).getD []) do
          if needComp && !ty.comparable env then
            throw s!"{cd.pos.show}: {cd.name} gives {q} the type argument {ty.show} for {v}, which must be comparable"
        iargs := iargs.push ((cd.name, q), tys)
  env := { env with iargs := iargs.toList }
  -- a class overrides a method only if its Verse Core type arguments are its
  -- own distinct type parameters, as many as the declaring class's: code
  -- generic over that class can then call its implementation (it could not
  -- give it a type argument it fixes, nor one it adds)
  let core (c : String) : List Ty :=
    env.coreArgs c (((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k)
  -- a class below an interface has as its Verse Core type arguments exactly
  -- those it gives the interface: references to the interface have those,
  -- and dispatch and field reads through them recover the class's (#53)
  for cd in cdefs do
    if !cd.isIface then
      let ps := ((env.sparams.lookup cd.name).getD []).map fun (v, k) => Ty.param v k
      for i in (env.supers cd.name).filter (env.info · |>.isIface) do
        let ia := env.upArgs cd.name ps i
        if !(ia == core cd.name) then
          let showArgs (ts : List Ty) : String := if ts.isEmpty then "none" else ", ".intercalate (ts.map Ty.show)
          if ia.length < (core cd.name).length then
            throw s!"{cd.pos.show}: {cd.name} gives {i} the type arguments {showArgs ia}, but its own are {showArgs (core cd.name)}: a class below an interface with type parameters of its own is not supported yet (#53, #209)"
          throw s!"{cd.pos.show}: {cd.name} gives {i} the type arguments {showArgs ia}, but its own are {showArgs (core cd.name)}: references to {i} could not recover them (#53)"
  for (mp, dm, qm) in overridePairs do
    let d := (dm.splitOn ".").head!
    let q := (qm.splitOn ".").head!
    let mn := (dm.splitOn ".").getLast!
    let (cd', cq) := (core d, core q)
    if !env.sameCorePinned d q then
      if ((env.sparams.lookup d).getD []).isEmpty then
        throw s!"{mp.show}: {d} has more Verse Core type arguments than {q} (a class between them has type parameters of its own), so it cannot override {mn} yet: code generic over {q} could not give them (#39)"
      throw s!"{mp.show}: {d} has type parameters that {q} does not have and that the type arguments it gives {q} do not determine, so it cannot override {mn}: code generic over {q} could not give them (#39, #209)"
    -- (its Verse Core type arguments are {q}'s, except where it fixes them
    -- or relates them to each other: dispatch is then typed under the
    -- refinement its pins give, #142, #209)
  -- the classes whose implementations fix type arguments their declaring
  -- class leaves open, and the classes below them, are dispatched to under
  -- a refinement, so Verse Core records their pins (#142)
  -- (the pins of the classes in override pairs, once, #238; not of every
  -- class, as a class whose Verse Core type would contain itself is refused
  -- only below, and computing its pins would not end)
  let pinClasses := (overridePairs.toList.flatMap fun (_, dm, qm) =>
      [(dm.splitOn ".").head!, (qm.splitOn ".").head!]).eraseDups
  env := { env with pinsMap := pinClasses.foldl (fun m d => m.insert d (env.pinsOf d)) {} }
  let fixes (e q : String) : Bool :=
    ((env.pinsOf q).zip (env.pinsOf e)).any (fun (a, b) => a != b) || (env.pinsOf e).length > (env.pinsOf q).length
  let headOf (f : String) : String := (f.splitOn ".").head!
  let fixers := (overridePairs.toList.filterMap fun (_, dm, qm) =>
      if fixes (headOf dm) (headOf qm) then some (headOf dm) else none) ++
    (implChecks.toList.filterMap fun (_, _, impl, decl) =>
      if fixes (headOf impl) (headOf decl) then some (headOf impl) else none)
  -- (and the classes that fix an interface's type arguments, below an
  -- interface whose fields sit at different places in its classes: its
  -- fields are reached through accessors, under the refinement, #157; so
  -- is a field such a class types otherwise than a class or interface
  -- above it, taking it from another interface, #205)
  let mut fieldAcc : Array (String × String) := #[]
  let mut accFixers : Array String := #[]
  for i in env.classes do
    let ds := env.concreteBelow i
    for (f, _, _) in env.fields i do
      let pos := ds.map fun d => ((fieldIndex (env.fields d) f).map (·.1)).getD 0
      let moved := (env.info i).isIface && !pos.all (· == pos.headD 0)
      let τi := env.coreFieldTy i f
      -- (a read that tests the class first needs an accessor for each class
      -- that fixes type arguments, also one that types the field as `i`)
      let retyped := ds.any fun d => env.coreFieldTy d f != τi
      for d in ds do
        if (moved || retyped) && fixes d i && env.sameCorePinned d i &&
            !fieldAcc.contains (d, f) then
          fieldAcc := fieldAcc.push (d, f)
          accFixers := accFixers.push d
  -- (and a concrete class with a class below it that types one of its
  -- fields otherwise: a read that tests for it reaches the field through
  -- its accessor, whose receiver is of exactly its class, as a temporary
  -- of its type also holds the classes below it, #205)
  for d in env.classes.filter (fun d => let i := env.info d; !i.isIface && !i.isAbstract) do
    for (f, _, _) in env.fields d do
      let τ := env.coreFieldTy d f
      if (env.concreteBelow d).any (fun d' => d' != d && env.coreFieldTy d' f != τ) &&
          !fieldAcc.contains (d, f) then
        fieldAcc := fieldAcc.push (d, f)
  -- (#243) and the classes refining casts test for, by their target
  -- (whose pins the dispatch to the cast's branch refines by)
  let fixers := fixers ++ accFixers.toList ++ env.castRequests.map (·.target)
  env := { env with pinned := env.classes.filter fun d => fixers.any fun f => d == f || (env.supers d).contains f,
                    fieldAcc := fieldAcc.toList }
  -- (#157) a hidden class below each generic class or interface whose
  -- concrete classes all fix some of its type arguments: a variable of its
  -- type at other type arguments starts as one. It has the class's fields
  -- (a class's include its interfaces'), and the program never makes one
  -- (an interface's placeholder is laid out for reads through `n` and the
  -- interfaces above it: each of `n`'s fields, inherited ones too, where
  -- every class below `n` has it, when they agree, else after those, as a
  -- read then tests the class first; padding between. A read through an
  -- interface `T` above `n` goes straight to the field only when every class
  -- below `T` has it at one place, and those include `n`'s, so it is the
  -- place here too. A placeholder needs a concrete class below, and no two
  -- fields share a place in one)
  let ifaceLayout (n : String) : List (String × Ty × Option SExpr) := Id.run do
    let ds := env.concreteBelow n
    let mut fixed : List (Nat × String × Ty) := []
    let mut free : List (String × Ty) := []
    for (f, t, _) in env.fields n do
      let pos := ds.map fun d => ((fieldIndex (env.fields d) f).map (·.1)).getD 0
      match pos.head? with
      | some p0 => if pos.all (· == p0) then fixed := fixed ++ [(p0, f, t)] else free := free ++ [(f, t)]
      | none => free := free ++ [(f, t)]
    let size := (fixed.map (·.1 + 1)).foldl max 0
    let laid := (List.range size).map fun k => match fixed.find? (·.1 == k) with
      | some (_, f, t) => (f, t, (none : Option SExpr))
      | none => (s!"$pad{k}", Ty.void, none)
    return laid ++ free.map fun (f, t) => (f, t, none)
  let coreLen (c : String) : Nat :=
    (env.coreArgs c (((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k)).length
  let needsPh (n : String) : Bool :=
    env.isRefClass n &&
    (((env.sparams.lookup n).isSome &&
        (env.concreteBelow n).all (fun d => env.pinned.contains d && (env.corePins d).any Option.isSome)) ||
      -- (or a class below with type parameters a dispatch on `n` opens,
      -- #209: an object of it needs more type arguments than `n`'s)
      (env.concreteBelow n).any fun d => env.pinned.contains d && coreLen d > coreLen n)
  for n in env.classes.filter needsPh do
    let h := s!"{n}$placeholder"
    let i := env.info n
    let ps := (env.sparams.lookup n).getD []
    let own := ps.map fun (v, c) => Ty.param v c
    env := { env with
      classes := env.classes ++ [h],
      structs := env.structs ++ [(h, if i.isIface then ifaceLayout n else (env.structs.lookup n).getD [])],
      sparams := env.sparams ++ [(h, ps)],
      cinfo := env.cinfo ++ [(h, { parent := if i.isIface then none else some n,
                                   ifaces := if i.isIface then [n] else [], isAbstract := true })],
      pargs := if i.isIface then env.pargs else env.pargs ++ [(h, own)],
      iargs := if i.isIface then env.iargs ++ [((h, n), own)] else env.iargs,
      phs := env.phs ++ [h],
      -- (below a class that records pins, it records the same)
      pinned := if env.pinned.contains n then env.pinned ++ [h] else env.pinned }
  -- (their superclasses too, as every class's, so that a test of whether
  -- a placeholder is below a class does not walk the chain each time:
  -- `refTags` asks that of each at each conversion of a class type)
  env := { env with supersMap := env.phs.foldl (fun m h => m.insert h (env.supersWalk h)) env.supersMap }
  env := { env with protos := env.makeProtos }
  if let some n := env.recursiveStruct? then
    if env.classes.contains n then
      throw s!"the Verse Core type of class {n} would contain itself, through its type arguments (#63)"
    throw s!"struct {n} contains itself (recursive struct types are not supported)"
  -- map keys in field types, now that every struct's fields are known
  -- (a key type can be a struct that holds a class)
  for (sn, fs) in env.structs do
    for (f, ft, _) in fs do
      if !ft.mapKeysOK env then
        throw s!"field '{f}' of {sn}: a map key must be comparable, and {ft.show} has a key that is not"
  -- overloading (#74): functions of one name, each renamed `F$ovN`; a call
  -- takes the one its arguments fit (`elabApp`), and no call fits two
  let fnNames := tops.filterMap fun | .fn _ n .. => some n | _ => none
  let ovNames := (fnNames.filter fun n => (fnNames.filter (· == n)).length > 1 && !n.contains '.').eraseDups
  let mut ovMap : List (String × List String) := []
  let mut renamed : Array STop := #[]
  for t in tops do
    match t with
    | .fn p n ps tps effs ret body =>
      if ovNames.contains n then
        if n == "Main" then throw s!"{p.show}: Main cannot be overloaded"
        if builtins.contains n then throw s!"{p.show}: '{n}' is a built-in function"
        if tops.any (fun | .const _ m .. | .classDef _ m .. => m == n | _ => false) ||
            env.classes.contains n || (env.structs.lookup n).isSome || (env.enums.lookup n).isSome then
          throw s!"{p.show}: '{n}' is defined twice (only functions can be overloaded)"
        let prev := (ovMap.lookup n).getD []
        let m := s!"{n}$ov{prev.length}"
        ovMap := (ovMap.filter (·.1 != n)) ++ [(n, prev ++ [m])]
        renamed := renamed.push (.fn p m ps tps effs ret body)
      else renamed := renamed.push t
    | t => renamed := renamed.push t
  let tops := renamed.toList
  env := { env with overloads := ovMap,
                    methodOverloads :=
                      let bases := (mov.map (·.1.2)).eraseDups
                      bases.map fun mn =>
                        let n := (mov.filter (·.1.2 == mn)).foldl (fun acc (_, sigs) => max acc sigs.length) 0
                        (mn, (List.range n).map fun k => s!"{mn}$ov{k}") }
  -- generic functions (those with a `where` clause) are numbered after the
  -- other functions and constants
  let isGeneric : STop → Bool
    | .fn _ _ _ (_ :: _) .. => true
    | _ => false
  let generics := tops.filter isGeneric
  let names := tops.map fun | .fn _ n .. => n | .const _ n .. => n | .classDef _ n .. => n
  let tops := tops.filter (!isGeneric ·)
  for (n, i) in names.zip (List.range names.length) do
    if names.take i |>.contains n then throw s!"'{n}' is defined twice (only functions can be overloaded)"
    if builtins.contains n then throw s!"'{n}' is a built-in function"
  -- a function's parameter and result types
  let fnTypes (env : TyEnv) (p : Pos) (n : String) (ps : List SParam) (effs : List String) (ret : STy) :
      Except String (List Ty × Ty) := do
    if effs.contains "suspends" then
      if effs.contains "decides" then
        throw s!"{p.show}: {n} is both <suspends> and <decides>, which exclude each other"
      if n.endsWith "$init" then
        throw s!"{p.show}: a <suspends> constructor is not supported (#156)"
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
      if (["converges", "computes", "transacts"].filter effs.contains).length > 1 then
        throw s!"{p.show}: {n} has more than one of <converges>, <computes> and <transacts> (they exclude each other)"
      if effs.contains "computes" && ("transacts" :: heapFx).any effs.contains then
        throw s!"{p.show}: <computes> excludes the heap effects (<reads>, <writes>, <allocates>, <transacts>) that {n} also has"
      sigs := sigs.push { idx, name := n, params := tys, ret := rt, decides := effs.contains "decides",
                          suspends := effs.contains "suspends",
                          -- (a `block:`'s effects are inferred below, from none, as a
                          -- constant's: blocks that construct each other's classes)
                          fx := if n.endsWith ".$block" || (n.splitOn "$default$").length > 1 then [] else allowedFx effs,
                          isConst := false,
                          named := (ps.filter (·.named)).map fun q => (q.name, q.default),
                          pnames := ps.map (·.name) }
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
      let tparams ← checkTParams env tps
      let genv := { env with tvars := tparams.map fun (v, c) => (v, Ty.param v c) }
      let (tys, rt) ← fnTypes genv p n ps effs ret
      if (["converges", "computes", "transacts"].filter effs.contains).length > 1 then
        throw s!"{p.show}: {n} has more than one of <converges>, <computes> and <transacts> (they exclude each other)"
      if effs.contains "computes" && ("transacts" :: heapFx).any effs.contains then
        throw s!"{p.show}: <computes> excludes the heap effects (<reads>, <writes>, <allocates>, <transacts>) that {n} also has"
      -- (#209) a method of a class with type parameters that its parent's
      -- type arguments do not give reads their values from its receiver
      -- (an overriding implementation: what a dispatch that opens them
      -- reaches; the class's other methods are called at known types)
      let selfTps : List String := match n.splitOn "." with
        | [c, m] =>
          if effs.contains "override" && env.classes.contains c && env.isRefClass c && !m.startsWith "$" &&
              (match tys.head? with | some (.struct c' _) => c' == c | _ => false) then
            (env.addedParams c).filter fun v => tparams.any (·.1 == v) && (env.witnessField? c v).isSome
          else []
        | _ => []
      if !selfTps.isEmpty && effs.contains "suspends" then
        throw s!"{p.show}: {n} is a <suspends> override, and its class has type parameters that its parent's type arguments do not give: not supported yet (#209)"
      -- generic functions come after the others
      gsigs := gsigs.push { idx := tops.length + gidx, name := n, params := tys, ret := rt, selfTps,
                            decides := effs.contains "decides", isConst := false,
                            suspends := effs.contains "suspends",
                            -- (a parametric class's `block:`: inferred from none, #41)
                            fx := if n.endsWith ".$block" then [] else allowedFx effs,
                            tparams,
                            named := (ps.filter (·.named)).map fun q => (q.name, q.default),
                            pnames := ps.map (·.name) }
    | _ => pure ()
  let mkSigProg (sigs : Array Sig) : Prog :=
    { fns := (sigs ++ gsigs).toList.map fun s =>
        { name := s.name, arity := s.params.length + s.ndicts, nslots := 0,
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
      -- a class's `block:` clauses have the effects of their code, and so
      -- does a default an overloaded constructor fills in (#99)
      | .fn _ n ps _ _ _ body =>
        if (n.splitOn "$default$").length > 1 then
          let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env }
          match (elabStmt ctx body (some sigs[idx]!.ret)).run { env } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k)
            if fx != sigs[idx]!.fx then
              sigs := sigs.set! idx { sigs[idx]! with fx }
              changed := true
          | .error _ => pure ()
        else if n.endsWith ".$block" then
          let s := sigs[idx]!
          let locals := (ps.zip (List.range ps.length)).zip s.params |>.map fun ((prm, i), t) =>
            ({ name := prm.name, slot := i, ty := t, mutable := false } : Local)
          let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env,
                             locals := locals.reverse, retTy := .void,
                             inBlock := true, selfClass := some ((n.dropEnd ".$block".length).toString) }
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
                             selfClass := some ((n.dropEnd ".$block".length).toString) }
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
  -- overloads take parameters no call fits both of (Book of Verse ch. 6)
  let sigNamed (s : Sig) : List (String × Bool × Ty) :=
    let npos := s.params.length - s.named.length
    (s.named.zip (s.params.drop npos)).map fun ((n, d), t) => (n, d.isSome, t)
  let sigsDistinct (sa sb : Sig) : Bool :=
    let pa := sa.params.take (sa.params.length - sa.named.length)
    let pb := sb.params.take (sb.params.length - sb.named.length)
    env.paramsDistinct pa pb || env.namedDistinct (sigNamed sa) (sigNamed sb)
  for (n, ms) in env.overloads do
    for (a, i) in ms.zip (List.range ms.length) do
      for b in ms.take i do
        match allSigs.find? (·.name == a), allSigs.find? (·.name == b) with
        | some sa, some sb =>
          if !sigsDistinct sa sb then
            let pos := ((tops ++ generics).findSome? fun | .fn q m .. => if m == a then some q else none | _ => none).getD { line := 0, col := 0 }
            let sh (s : Sig) := ", ".intercalate ((s.params.zip (List.range s.params.length)).map fun (t, i) =>
              let npos := s.params.length - s.named.length
              if i < npos then t.show else s!"?{((s.named.drop (i - npos)).head?.map (·.1)).getD "?"}:{t.show}")
            throw s!"{pos.show}: {n} is defined twice with parameters a call cannot tell apart, ({sh sb}) and ({sh sa}): overloads must take disjoint types"
        | _, _ => pure ()
  -- the overloads of a method a class sees take parameters no call fits two
  -- of (#106: a subclass's new overload too; an override has its method's)
  for c in env.classes do
    for (mn, ms) in env.methodOverloads do
      let vis : List (String × Sig) := ms.filterMap fun o =>
        ((env.supers c).find? fun e => allSigs.any (·.name == s!"{e}.{o}")).bind fun e =>
          (allSigs.find? (·.name == s!"{e}.{o}")).map fun sg => (s!"{e}.{o}", { sg with params := sg.params.drop 1 })
      for ((a, sa), i) in vis.zip (List.range vis.length) do
        for (b, sb) in vis.take i do
          if !sigsDistinct sa sb then
            let sh (s : Sig) := ", ".intercalate (s.params.map Ty.show)
            let owner (x : String) := (x.splitOn ".").head!
            let cp := ((cdefs.find? (·.name == c)).map (·.pos)).getD { line := 0, col := 0 }
            throw s!"{cp.show}: {c} has overloads of {mn} a call cannot tell apart, ({sh sb}) in {owner b} and ({sh sa}) in {owner a}: overloads must take disjoint types (an override has the same parameters as its method)"
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
    -- the methods' own type parameters, after their classes', renamed to the
    -- declaration's (and declared comparable alike)
    let own (sg : Sig) (cls : String) := sg.tparams.drop ((env.sparams.lookup cls).getD []).length
    let (oa, ob) := (own a ea, own b eb)
    -- (renamed apart first, so that a class's type arguments, mapped into
    -- `c`'s, cannot capture them)
    let apart (os : List (String × Bool)) : List (String × Ty) :=
      (os.zip (List.range os.length)).map fun ((x, k), i) => (x, Ty.param s!"$o{i}" k)
    let inA (t : Ty) : Ty := inC c ea (t.subst (apart oa))
    let inB (t : Ty) : Ty := inC c eb (t.subst (apart ob))
    oa.length == ob.length && (oa.map (·.2)) == (ob.map (·.2)) &&
    ((a.params.drop 1).map inA) == ((b.params.drop 1).map inB) &&
      retBelow (inA a.ret) (inB b.ret) && a.decides == b.decides &&
      a.named.map (·.1) == b.named.map (·.1)
  -- an implementation has no heap effect its declaration does not allow
  let fxOver (a b : Sig) : Option String := a.fx.find? (!b.fx.contains ·)
  for (mp, mine, theirs) in overridePairs do
    match allSigs.find? (·.name == mine), allSigs.find? (·.name == theirs) with
    | some a, some b =>
      if !sameSigIn (clsOf mine) a b then throw s!"{mp.show}: {mine} must have the signature of {theirs}, which it overrides"
      if a.suspends != b.suspends then
        throw s!"{mp.show}: {mine} must {if b.suspends then "be" else "not be"} <suspends>, as {theirs}, which it overrides, is{if b.suspends then "" else " not"} (#156)"
      if let some k := fxOver a b then
        throw s!"{mp.show}: {mine} allows the effect <{k}>, which {theirs}, which it overrides, does not"
    | _, _ => pure ()
  -- the implementation a concrete class uses has the signature of every
  -- declaration of the method above it
  for (cp, c, impl, decl) in implChecks do
    -- code generic over the declaring class or interface calls `c`'s
    -- implementation only at its own type arguments (#39, #53)
    -- (judged at the class that holds the implementation, whose Verse Core
    -- type arguments must be the declaring one's, and with the same
    -- signature at those type arguments)
    let q := clsOf decl
    let e := clsOf impl
    let atCore (cls : String) (sg : Sig) : List VTy × VTy :=
      let cenv := { env with tvars := env.coreVars cls }
      ((sg.params.drop 1).map (·.toVTy cenv), sg.ret.toVTy cenv)
    -- (at the type arguments `e` fixes, #142, the declaration's types are
    -- taken at the fixed ones)
    let pinσ : Nat → VTy := fun j => match (env.lowerPins (env.pinsOf e))[j]? with
      | some (some t) => t
      | _ => .var j
    let sigOk : Bool := match allSigs.find? (·.name == impl), allSigs.find? (·.name == decl) with
      | some a, some b =>
        let ca := atCore e a
        let cb := atCore q b
        ca.1 == cb.1.map (VTy.subst pinσ) && VTy.sub ca.2 (cb.2.subst pinσ)
      | _, _ => true
    match allSigs.find? (·.name == impl), allSigs.find? (·.name == decl) with
    | some a, some b =>
      if !sameSigIn c a b then
        throw s!"{cp.show}: in {c}, {impl} does not have the signature of {decl}"
      if let some k := fxOver a b then
        throw s!"{cp.show}: in {c}, {impl} allows the effect <{k}>, which {decl} does not"
    | _, _ => pure ()
    if !env.sameCorePinned e q then
      throw s!"{cp.show}: {c} uses {impl} for {decl}, but {e} has type parameters that {q} does not have, so code generic over {q} could not give them (#39)"
    if !sigOk then
      throw s!"{cp.show}: {c} uses {impl} for {decl}, but their types differ at {q}'s type arguments (as code generic over {q} sees them), so it could not call it (#53)"
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
    | .const _ n none (.structDef _ _ _) =>
      let nps := ((env.sparams.lookup n).getD []).map fun (v, c) => Ty.param v c
      let senv := { env with tvars := (env.sparams.lookup n).getD [] |>.map fun (v, c) => (v, Ty.param v c) }
      let ctx : Ctx := { sigs := allSigs, sigProg, types := senv, canFail := true, inDefaultCheck := true }
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
      (decides : Bool) (allowed : List String) (tps : List (String × Bool)) (body : SExpr)
      (suspends : Bool := false) (selfTps : List String := []) :
      Except String (Fn × List VTy × List (String × Ty) × Option Pos × List Refine.Lift) := do
    -- (#209) the values of `selfTps` come from the receiver's hidden
    -- fields, in slots after the hidden parameters
    let dictTps := tps.filter (fun (v, _) => !selfTps.contains v) ++ tps.filter (fun (v, _) => selfTps.contains v)
    let selfCls := (name.splitOn ".").headD ""
    let env := if selfTps.isEmpty then env else
      { env with dictOrder := dictTps.map (·.1),
                 selfWitness := selfTps.map fun v => (v, (env.witnessField? selfCls v).getD 0) }
    let locals := (ps.zip (List.range ps.length)).zip ptys |>.map fun ((prm, i), t) =>
      ({ name := prm.name, slot := i, ty := t, mutable := false } : Local)
    for (prm, i) in ps.zip (List.range ps.length) do
      if ps.take i |>.any (·.name == prm.name) then throw s!"{p.show}: duplicate parameter '{prm.name}'"
    let ctx : Ctx := { sigs := allSigs, sigProg, locals := locals.reverse, types := env,
                       canFail := decides, retTy := ret, dictBase := ps.length, suspends,
                       dictVars := dictTps.map (·.1),
                       inBlock := name.endsWith ".$block",
                       inCtor := name.endsWith "$init",
                       selfClass := match name.splitOn "." with
                         | [c, _] => some c
                         | _ => none
                       selfMethod := match name.splitOn "." with
                         | [_, m] => some m
                         | _ => none }
    let hidden := dictTps.map fun (v, c) => Ty.param v c
    let arity := ps.length + hidden.length - selfTps.length
    let ((r, _), st) ← (elabStmt ctx body (some ret)).run
      { env, nslots := ps.length + hidden.length, slotTys := (ptys ++ hidden).toArray }
    let (e, st) ← (coerce p r ret).run st
    let e := if ret == .void then Expr.seq e (.lit .void) else e
    let selfInits : List Expr := (dictTps.drop (hidden.length - selfTps.length)).map fun (v, _) =>
      .heap (.get ((env.witnessField? selfCls v).getD 0)) [.local 0]
    let inits ← match (st.slotTys.toList.drop (ps.length + hidden.length)).mapM
        (slotDefault env ps.length (ptys ++ hidden.take (hidden.length - selfTps.length)) []) with
      | .ok ds => pure (selfInits ++ ds)
      | .error msg => throw s!"{p.show}: in {name}: {msg}"
    fxCheck name allowed st
    return ({ name, arity, nslots := st.nslots, decides, writes := allowed.contains "writes",
              body := initPrefixE arity inits e },
      st.slotTys.toList.map (Ty.toVTy env), st.fnNeeds, st.errAt, st.castNeeds)
  -- (the accessors come right after the functions, #157)
  env := { env with fieldAccBase := tops.length + gsigs.size }
  let genvOf (g : Sig) : TyEnv := { env with tvars := g.tparams.map fun (v, c) => (v, Ty.param v c) }
  let mut fns : Array Fn := #[]
  let mut slotTys : Array (List VTy) := #[]
  let mut fnNeeds : List (String × Ty) := []
  -- (where each function calls `Err()`, by its index, #235)
  let mut errs : Array (Option Pos) := #[]
  let mut castNeeds : List Refine.Lift := []
  for (top, idx) in tops.zip (List.range tops.length) do
    let sig := sigs[idx]!
    match top with
    | .fn p n ps _ _ _ body =>
      let (fn, tys, needs, err, casts) ← elabFn env p n ps sig.params sig.ret sig.decides sig.fx [] body sig.suspends
      fnNeeds := fnNeeds ++ needs
      castNeeds := castNeeds ++ casts
      fns := fns.push fn
      errs := errs.push err
      slotTys := slotTys.push tys
    | .const p n _ body =>
      -- a constant is computed at each use, so it would be a new object each
      -- time (until Verse Core has global state)
      if sig.ret.holdsMutable env then
        throw s!"{p.show}: the constant {n} would hold an object with var fields or of a <unique> class, which would be a new one at each use: make it a function"
      let ctx : Ctx := { sigs := allSigs, sigProg, types := env }
      let (r, st) ← (elabStmt ctx body (some sig.ret)).run { env }
      let (e, st) ← (coerce p r.1 sig.ret).run st
      fnNeeds := fnNeeds ++ st.fnNeeds
      castNeeds := castNeeds ++ st.castNeeds
      let tys := st.slotTys.toList.map (Ty.toVTy env)
      -- slots start like a function's (a class-typed one as a placeholder)
      let inits ← match st.slotTys.toList.mapM (slotDefault env 0 [] []) with
        | .ok ds => pure ds
        | .error msg => throw s!"{p.show}: in {n}: {msg}"
      fxCheck n sig.fx st
      fns := fns.push { name := n, arity := 0, nslots := st.nslots, decides := false,
                        writes := sig.fx.contains "writes", body := initPrefixE 0 inits e }
      errs := errs.push st.errAt
      slotTys := slotTys.push tys
    | .classDef .. => pure ()   -- expanded above
  -- each generic function is elaborated once, with its type parameters
  -- opaque, as Verse checks it, into one Verse Core function whose types
  -- mention type variables; `Prog.checkTypes` checks it once, for every
  -- instantiation (`Typed.subst`)
  for (top, g) in generics.zip gsigs.toList do
    match top with
    | .fn p n ps _ _ _ body =>
      let (fn, tys, needs, err, casts) ← elabFn (genvOf g) p n ps g.params g.ret g.decides g.fx g.tparams body g.suspends
        g.selfTps
      fnNeeds := fnNeeds ++ needs
      castNeeds := castNeeds ++ casts
      fns := fns.push fn
      errs := errs.push err
      slotTys := slotTys.push tys
    | _ => pure ()
  -- (#214) functions wanted as values at types no class of theirs gives:
  -- the program is elaborated again, with classes for them, so this one,
  -- with placeholders, goes no further
  -- (#243) and branches of casts that refine type arguments, lifted into
  -- functions
  if !fnNeeds.isEmpty || !castNeeds.isEmpty then
    let casts := castNeeds.foldl (fun acc l => if acc.any (·.key == l.key) then acc else acc ++ [l]) []
    return { prog := default, sigs := { fns := [] }, slotTys := [], fnNeeds := fnNeeds.eraseDups, castNeeds := casts }
  let mainSig ← match sigs.toList.find? (·.name == (if opts.entry.isSome then "$Do" else "Main")) with
    | some s =>
      if s.isConst || !s.params.isEmpty then throw "Main must be a function with no parameters"
      pure s
    | none => throw "the program has no Main() function"
  -- with prototypes, the program starts with a prelude that allocates them
  -- and then calls `Main` (#37)
  let protoList := env.protos.map fun (_, t, vs) => (t, vs)
  let fsigs0 := sigs.toList.map (fun s => (s.params.map (Ty.toVTy env), s.ret.toVTy env)) ++
    gsigs.toList.map fun g =>
      let genv := genvOf g
      let dictTys : List Ty := (g.tparams.filter fun (vc : String × Bool) => !g.selfTps.contains vc.1).map
        fun (vc : String × Bool) => Ty.param vc.1 vc.2
      ((g.params ++ dictTys).map (Ty.toVTy genv), g.ret.toVTy genv)
  -- the class table: the fields of each class, by tag (#34); the prototypes (#37)
  -- (a parametric class's field types mention its type parameters, #39)
  -- each field as `TyEnv.fieldSrc` gives it (the topmost interface that
  -- declares it, else the topmost class in the chain that has it), in
  -- terms of the Verse Core type arguments the hierarchy shares: an
  -- `intbox := class(base(int))`'s inherited `Value` is `var 0`, as in `base`
  let mut classTable := env.classes.map fun d =>
    if env.isRefClass d then (env.fields d).map fun (f, t, _) =>
      (env.coreFieldTy d f).getD (t.toVTy { env with tvars := env.coreVars d })
    else []
  let protos := env.protos.map fun (d, t, _) => (t, (env.coreArgs d []).map (Ty.toVTy env))
  let pins := env.classes.map fun d =>
    if env.isRefClass d then env.lowerPins (env.corePins d) else []
  -- concurrency (#156): each <suspends> function `g` becomes a frame class
  -- and the functions `g$new`, `g$reset` and `g$resume` (`Suspend.lean`);
  -- `g`'s own index is `g$resume`'s, as only suspends code calls it
  -- the accessors (#157): for each (class, field), `get(Self)` and
  -- `set(Self, V)`, generic over the class's type argument positions
  let mut accSigs : Array (List VTy × VTy) := #[]
  for (d, f) in env.fieldAcc do
    let tag := env.tagOf d
    let kd := ((fieldIndex (env.fields d) f).map (·.1)).getD 0
    let m := (env.coreArgs d (((env.sparams.lookup d).getD []).map fun (v, c) => Ty.param v c)).length
    let selfTy : VTy := .ref [tag] ((List.range m).map VTy.var)
    let fTy : VTy := ((classTable[tag]?).bind (·[kd]?)).getD .int
    fns := fns.push { name := s!"{d}.$get.{f}", arity := 1, nslots := 1, decides := false, writes := false,
                      body := .heap (.get kd) [.local 0] }
    slotTys := slotTys.push [selfTy]
    accSigs := accSigs.push ([selfTy], fTy)
    fns := fns.push { name := s!"{d}.$set.{f}", arity := 2, nslots := 2, decides := false, writes := true,
                      body := .heap (.set kd) [.local 0, .local 1] }
    slotTys := slotTys.push [selfTy, fTy]
    accSigs := accSigs.push ([selfTy, fTy], fTy)
  let fsigs0 := fsigs0 ++ accSigs.toList
  let mut fsigs := fsigs0
  let mut frameClasses : Array (List VTy) := #[]
  let mut mainCall : Expr := .call mainSig.idx []
  -- (an error of the lowering names a function: with its position)
  let inFn := inFnMsg (tops ++ generics)
  -- (a refined test, #142, of classes whose pins the receiver's closed type
  -- arguments rule out can never pass, and the checker types such a test
  -- only when the pins can agree: it goes, #186)
  let S00 : Sigs := { fns := fsigs0, classes := classTable, protos, pins }
  for gi in List.range fns.size do
    let fn := fns[gi]!
    fns := fns.set! gi { fn with body := Suspend.pruneDead S00 ((slotTys[gi]?).getD []) fn.body }
  -- (#235) the functions with several values computed at their calls
  checkEager fns errs fun g => ((tops ++ generics).findSome? fun
    | .fn p n .. => if n == g then some p else none
    | _ => none)
  if usesConc then
    let (fns1, slotTys1, fsigs1, classTable1, frameClasses1, mainCall1) ←
      lowerConcurrency env sigs gsigs mainSig fsigs0 protos pins inFn fns slotTys fsigs classTable
    fns := fns1
    slotTys := slotTys1
    fsigs := fsigs1
    classTable := classTable1
    frameClasses := frameClasses1
    mainCall := mainCall1
  let mut main := mainSig.idx
  if !protoList.isEmpty || mainSig.suspends then
    main := fns.size
    fns := fns.push { name := "$Main", arity := 0, nslots := 0, decides := mainSig.decides,
                      writes := mainSig.fx.contains "writes" || mainSig.suspends,
                      body := protoPrelude protoList mainCall }
    slotTys := slotTys.push []
    fsigs := fsigs ++ [([], if mainSig.suspends then VTy.void else mainSig.ret.toVTy env)]
  let P : Prog := { fns := fns.toList, main }
  if !P.check then throw "internal error: the elaborated program does not pass Prog.check"
  if !P.checkControl then throw "internal error: the elaborated program does not pass Prog.checkControl"
  let S : Sigs := { fns := fsigs, classes := classTable ++ frameClasses.toList, protos, pins }
  if !P.checkTypes S slotTys.toList then
    -- name what fails, for a bug report
    let bad := (List.range P.fns.length).find? fun f =>
      match P.fns[f]?, S.fns[f]?, slotTys[f]? with
      | some fn, some (ps, τ), some Γ => !checkFn S fn ps τ Γ
      | _, _, _ => true
    let which := match bad with
      | some f =>
        let dump := if !opts.debug then "" else
          s!"\n-- body: {repr ((P.fns[f]?).map Fn.body)}\n-- arity: {(P.fns[f]?).map Fn.arity}" ++
          s!"\n-- slot types: {repr (slotTys[f]?)}\n-- signature: {repr (S.fns[f]?)}"
        s!" (in {((P.fns[f]?).map Fn.name).getD "?"}){dump}"
      | none => if !checkPrelude P S then " (the prototypes)" else ""
    throw s!"internal error: the elaborated program does not pass Prog.checkTypes{which}"
  return { prog := P, sigs := S, slotTys := slotTys.toList, fnNeeds := fnNeeds.eraseDups }

/-- `F$ovN` (an overload, #74) shown as `F`: every `$ov` and the digits after it removed. -/
def stripOv (msg0 : String) : String := Id.run do
  -- `K$default$F` (a default an overloaded constructor fills in) is "the default of F"
  let msg := match msg0.splitOn "$default$" with
    | [] | [_] => msg0
    | first :: rest =>
      let dropName (x : String) : String :=
        String.ofList (x.toList.reverse.dropWhile (fun (c : Char) => c.isAlphanum || c == '_')).reverse
      rest.foldl (fun acc part => dropName acc ++ "the default of " ++ part) first
  let cs := msg.toList
  let mut out : List Char := []
  let mut i := 0
  while i < cs.length do
    if cs[i]! == '$' && i + 2 < cs.length && cs[i+1]! == 'o' && cs[i+2]! == 'v' then
      i := i + 3
      while i < cs.length && cs[i]!.isDigit do i := i + 1
    else
      out := cs[i]! :: out
      i := i + 1
  return String.ofList out.reverse

/-- Elaborate a parsed program (`elabProgramCore`), with the names of the
    functions a constructor or an overload becomes shown as written: `K$init`
    is `K<constructor>`, `F$ov1` is `F` (names with `$` are never the user's). -/
def elabProgram (allTops00 : List STop) (opts : Options := {}) : Except String Compiled :=
  -- (#214) again with the functions wanted as values at closed function
  -- types: each round asks for new ones only, so a few rounds do
  let rec go (fuel : Nat) (opts : Options) : Except String Compiled := do
    let c ← elabProgramCore allTops00 opts
    -- (#243) and with the branches of casts that refine type arguments
    let casts := c.castNeeds.filter fun l => !opts.castRequests.any (·.key == l.key)
    match fuel, c.fnNeeds.filter (!opts.fnRequests.contains ·) with
    | fuel + 1, new@(_ :: _) =>
      go fuel { opts with fnRequests := opts.fnRequests ++ new, castRequests := opts.castRequests ++ casts }
    | fuel + 1, [] =>
      if casts.isEmpty then
        if c.castNeeds.isEmpty then return c
        throw "internal error: a cast that refines type arguments was asked for again (#243)"
      go fuel { opts with castRequests := opts.castRequests ++ casts }
    | 0, [] =>
      if c.castNeeds.isEmpty then return c
      throw "internal error: casts that refine type arguments still to lift after several elaborations (#243)"
    -- (a program with a placeholder left is never given out)
    | 0, _ :: _ => throw "internal error: functions still wanted as values after several elaborations (#214)"
  (go 4 opts).mapError fun msg =>
    FnValues.pretty (((stripOv (msg.replace "$init" "<constructor>")).replace "::" ".").replace "$replaceAll" "ReplaceAll")

/-- Parse and elaborate Verse source text. -/
def compileChecked (src : String) (opts : Options := {}) : Except String Compiled := do
  elabProgram (← parseProgram src) opts

/-- Parse and elaborate Verse source text. -/
def compile (src : String) (opts : Options := {}) : Except String Prog := do
  return (← compileChecked src opts).prog

/-- Compile loaded definitions (`Front.loadProgram`) with shell arguments,
    bound to `Args` when given or mentioned, and an optional `do` expression. -/
def compileTops (tops : List STop) (args : List String) (mentionsArgs : Bool) (doExpr : Option String)
    (debug : Bool := false) : Except String Prog := do
  let entry ← match doExpr with
    | some t => some <$> parseExprText t
    | none => pure none
  let useArgs := !args.isEmpty || mentionsArgs
  return (← elabProgram tops { args := if useArgs then some args else none, entry, debug }).prog

/-- Compile with shell arguments (bound to `Args` when given or used) and an
    optional `do` expression, as `openverse run FILE ARG… do EXPR` does. -/
def compileWith (src : String) (args : List String) (doExpr : Option String) : Except String Prog := do
  let entry ← match doExpr with
    | some t => some <$> parseExprText t
    | none => pure none
  let useArgs := !args.isEmpty || (src.splitOn "Args").length > 1
  compile src { args := if useArgs then some args else none, entry }

end OpenVerse.Front
