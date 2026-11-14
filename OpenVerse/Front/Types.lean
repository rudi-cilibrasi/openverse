/-
  OpenVerse front end — resolved types and the class hierarchy.

  `Ty` records the types used during elaboration; `TyEnv` records the
  program's type definitions, layouts, inheritance, views and pins. Their
  queries, generic matching and unification, comparability and prototype
  values live here, independently of expression elaboration and slot
  allocation in `Elab.lean`.
-/
import OpenVerse.Core.Typing
import OpenVerse.Front.FnValues
import OpenVerse.Front.Refine
import OpenVerse.Front.Access
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
  /-- `comparable` as a type (Book of Verse ch. 11): the type of every value
      of a comparable type, below `any`. A value is boxed when it becomes one
      (`boxValue`, `OpenVerse.Core.Comparable`), so that Verse Core's
      equality on boxes is Verse's; in Verse Core it is `dyn`. -/
  | dyn
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
  /-- `weak_map(k, v)` (Book of Verse ch. 3, "Weak Maps"): a supertype of
      `[k]v` that keeps only entry access, `W[k]` and `set W[k] = v`; no
      length, iteration, equality or conversion back to a map. In Verse
      Core it is a map, the array of its pairs: no program can tell an
      entry whose key is unreachable, so none is dropped
      (docs/research/weak-map.md). -/
  | weakMap : Ty → Ty → Ty
  /-- A type parameter of the generic function (or parametric struct) being
      elaborated, opaque there (`comparable` when declared
      `t:subtype(comparable)`). In Verse Core it is a type variable `VTy.var`. -/
  | param : String → (comparable : Bool) → Ty
  deriving Repr, Inhabited

/-- Nominal helper dependencies of an already resolved API type. Parameters
    are identities, not nominal types with the same spelling. -/
partial def Ty.helperUses : Ty → List String
  | .arr t | .opt t => t.helperUses
  | .tup ts => ts.flatMap Ty.helperUses
  | .map k v | .weakMap k v => k.helperUses ++ v.helperUses
  | .struct n ts => n :: (if (FnValues.parseName n).any (fun (_, es) => es.contains "suspends")
      then ["$suspends"] else []) ++ ts.flatMap Ty.helperUses
  | _ => []

partial def Ty.eqv : Ty → Ty → Bool
  | .int, .int | .logic, .logic | .char, .char | .char32, .char32 | .rational, .rational | .float, .float | .void, .void | .never, .never => true
  | .any, .any | .dyn, .dyn => true
  | .refine a, .refine b => a == b
  | .arr a, .arr b => a.eqv b
  | .opt a, .opt b => a.eqv b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).all fun (a, b) => a.eqv b
  | .struct a as, .struct b bs =>
    a == b && as.length == bs.length && (as.zip bs).all fun (x, y) => x.eqv y
  | .enum a, .enum b => a == b
  | .map a b, .map c d | .weakMap a b, .weakMap c d => a.eqv c && b.eqv d
  | .param a _, .param b _ => a == b
  | _, _ => false

instance : BEq Ty := ⟨Ty.eqv⟩

partial def Ty.show : Ty → String
  | .int => "int" | .logic => "logic" | .char => "char" | .char32 => "char32" | .rational => "rational" | .float => "float" | .void => "void"
  | .any => "any"
  | .dyn => "comparable"
  | .refine n => n
  | .never => "false"
  | .arr .char => "string"
  | .arr t => "[]" ++ t.show
  | .opt t => "?" ++ t.show
  | .tup ts => "tuple(" ++ ", ".intercalate (ts.map Ty.show) ++ ")"
  | .struct "$subev0" [] => "subscribable_event()"
  | .struct n [] => n
  | .struct n ts =>
    -- (a function type, #210)
    match FnValues.parseWritten n with
    | some (s, effs) => s.show ((ts.take s.arity).map Ty.show) ((ts.drop s.arity).headD .void).show effs
    | none => n ++ "(" ++ ", ".intercalate (ts.map Ty.show) ++ ")"
  | .enum n => n
  | .map k v => "[" ++ k.show ++ "]" ++ v.show
  | .weakMap k v => "weak_map(" ++ k.show ++ ", " ++ v.show ++ ")"
  | .param n _ => n

def Ty.string : Ty := .arr .char

/-- A closed type as written (#214: a function type asked for, for the
    value classes made before elaboration). -/
partial def Ty.toSTy : Ty → STy
  | .int => .name "int" | .logic => .name "logic" | .char => .name "char" | .char32 => .name "char32"
  | .rational => .name "rational" | .float => .name "float" | .void => .name "void" | .any => .name "any"
  | .dyn => .name "comparable"
  | .refine n | .enum n | .param n _ => .name n
  | .never => .name "$never"
  | .arr .char => .name "string"
  | .arr t => .arr t.toSTy
  | .opt t => .opt t.toSTy
  | .tup ts => .tup (ts.map Ty.toSTy)
  | .map k v => .map k.toSTy v.toSTy
  | .weakMap k v => .app "weak_map" [k.toSTy, v.toSTy]
  | .struct n [] => .name n
  | .struct n ts => match FnValues.parseWritten n with
    | some (s, effs) => s.toSTy ((ts.take s.arity).map Ty.toSTy) ((ts.drop s.arity).headD .void).toSTy effs
    | none => .app n (ts.map Ty.toSTy)

/-- Substitute type arguments for type parameters. -/
partial def Ty.subst (σ : List (String × Ty)) : Ty → Ty
  | .param n c => (σ.lookup n).getD (.param n c)
  | .arr t => .arr (t.subst σ)
  | .opt t => .opt (t.subst σ)
  | .tup ts => .tup (ts.map (Ty.subst σ))
  | .map k v => .map (k.subst σ) (v.subst σ)
  | .weakMap k v => .weakMap (k.subst σ) (v.subst σ)
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
  | .map k v, .map k' v' | .weakMap k v, .weakMap k' v' => do Ty.alpha (← Ty.alpha m k k') v v'
  | a, b => if a.eqv b then some m else none

/-- The variance of a class's or interface's type parameter, as the Book of
    Verse has it (ch. 10, "Instantiation and Identity"): how the parameter is
    used in the type's member signatures, inherited ones included. `co`: only
    where values come out (a field that is no `var`, a method's result), so
    `c(player)` is a `c(entity)`; `contra`: only where they go in (a method's
    parameter), so `c(entity)` is a `c(player)`; `inv`: both (or a `var`
    field), no conversion; `bi`: not used, any instance is any other.
    Verse Core has its own, over the classes' field tables
    (`Sigs.inferVariances`); a conversion needs both (`refUp`). -/
inductive SVar where
  | bi | co | contra | inv
  deriving BEq, Repr, Inhabited

/-- The more restrictive of two variances: uses in two places. -/
def SVar.join : SVar → SVar → SVar
  | .bi, v | v, .bi => v
  | .co, .co => .co
  | .contra, .contra => .contra
  | _, _ => .inv

/-- A use as a value that goes in where it comes out, and the converse. -/
def SVar.flip : SVar → SVar
  | .co => .contra
  | .contra => .co
  | v => v

/-- A use `inner` inside a type argument of variance `outer`. -/
def SVar.compose (outer inner : SVar) : SVar :=
  match outer with
  | .bi => .bi
  | .co => inner
  | .contra => inner.flip
  | .inv => if inner == .bi then .bi else .inv

def SVar.show : SVar → String
  | .bi => "bivariant"
  | .co => "covariant"
  | .contra => "contravariant"
  | .inv => "invariant"

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

/-- What an elaboration of the program asks for that only types tell, for
    the program to be elaborated again with it (`Compiled.needs`), and what
    earlier elaborations asked for (`Options.requests`): `elabProgram`
    elaborates the program in rounds until one asks for nothing new. -/
structure Requests where
  /-- Pure mutual groups that retain the eager polymorphic-recursion path. -/
  eager : List String := []
  /-- (#283) Recursive functions with several values whose values would be
      computed at the call, but something they run prints or calls
      `Err()`: taken lazily if their shape allows. -/
  lazy : List String := []
  /-- (#283) For each use `R.M` of a method several classes or interfaces
      declare apart, by its place: the root its receiver's class is below,
      whose family it takes (`Choice.rootsAt`). -/
  families : List (Pos × String) := []
  /-- (#283) For each call of an overloaded function with an overload that
      has several values, by its place: the overload it takes (`F$ovK`),
      whose own function it calls (`Choice.inlineMulti`). -/
  overloads : List (Pos × String) := []
  /-- (#283) For each consumer in a recursive group's code of a call of a
      function with several values, the types of the names it takes from
      that code and gives it (`Choice.nestKey`), which its function of its
      own (`Choice.nestFns`) is made with; and for a `for` that can fail,
      `$fails`. -/
  nested : List (String × STy) := []
  /-- (#283) The field orders of the structs and classes constructed with a
      choice point in a field in a recursive group's code
      (`TyEnv.fieldOrder`), which `inlineMulti`'s lifter takes them in. -/
  fieldOrders : List (String × List (String × Bool)) := []
  /-- (#283) The calls, by their place and the function whose code they are
      in, of a generic function with several values that a lazily taken
      group's machine takes at another instance of its type parameters than
      the one it took first: each a call of a copy of that function of its
      own (`Choice.inlineMulti`), another member of the machine. -/
  instanceCalls : List (Pos × String) := []
  /-- Functions wanted as values at closed function types no class of
      theirs gives (#214): a class for each. -/
  fns : List (String × Ty) := []
  /-- Methods wanted as values at function types their own fit only by
      variance: an adapter for each, by key. -/
  methods : List FnValues.MethodRequest := []
  /-- Canonical checked upcast dictionaries discovered by elaboration. -/
  subtypes : List STop := []
  /-- Branches of casts that refine type arguments (#243): a function for
      each, by key. -/
  casts : List Refine.Lift := []
  /-- Functions of their own for lazily taken calls whose effects need them
      (#246), the continuations, stages and helpers that consumers of
      choices are lowered with (#335), and the helpers that forward calls
      to the defaults of their named parameters: by key. -/
  loops : List Choice.FirstLift := []
  /-- Classes with a class parent that list an interface at type arguments
      that are not a prefix of their own (#351): hidden fields for all of
      their type parameters. -/
  witnesses : List String := []
  /-- The generic functions that box a value of a type mentioning one of
      their type parameters (a conversion to `comparable`, a comparison
      with a value of another type), and that parameter: the bound
      `(comparable, t)`, whose evidence is the box of a `t`, for each
      (`SubtypeEvidence.Plan.box`). -/
  boxes : List (String × String) := []
  /-- In a program that calls `ToDiagnostic`, the classes of the values
      converted to `any` and their printers (`Diagnostic.wrapperDecls`),
      by name. -/
  anys : List STop := []
  deriving Inhabited

/-- A field with accessors (Book of Verse ch. 10, "Fields with Accessors";
    `Accessors`): it has no storage, and a read of it is a call of its class's
    method `getter`, a `set` one of `setter` (`Elab/Accessors.lean`). -/
structure AccessorField where
  /-- The class or interface that declares it. -/
  owner : String
  name : String
  getter : String
  setter : String
  /-- Its type, in terms of `owner`'s type parameters (`Ty.param`). -/
  ty : Ty
  /-- Its default is `external{}`: a construction need not give it. -/
  external : Bool
  /-- The fields with storage of `owner` declared right before and right
      after it: a construction evaluates its value between theirs. -/
  prev : Option String := none
  next : Option String := none
  deriving Inhabited

/-- The user-defined types of a program. -/
structure TyEnv where
  /-- Public helper names owned by source declarations use private identities
      inside the prelude. Source types themselves keep their resolved names. -/
  concurrencyNames : List (String × String) := []
  /-- Source construction contracts, collected before helper generation.
      Compiler implementation types have no source-declared budget. -/
  constructionFx : Std.HashMap String (List String) := {}
  /-- The source's access specifiers, as the elaboration of a member reached
      through a value judges its use (`Access.Env`). -/
  access : Access.Env := {}

  /-- The `<final>` fields, each with the class or interface that declares
      it: no class below gives it another default, no construction a value. -/
  finalFields : List (String × String) := []
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
  /-- Declared nominal upper bounds, as (base, derived) relations over the
      declaration's own parameters. These govern type application validity;
      executable upcasts additionally need a typed dictionary value. -/
  sbounds : List (String × List (Ty × Ty)) := []
  /-- Relations assumed in this declaration's type scope. They do not name
      runtime slots and cannot themselves supply executable evidence. -/
  boundFacts : List (Ty × Ty) := []
  /-- Each enum: its enumerators in order. -/
  enums : List (String × List String) := []
  /-- The fields with accessors of the classes and interfaces, none of them
      among `structs`' fields (`Accessors`). -/
  accessors : List AccessorField := []
  /-- The refinement types (#136): each one's base type (int or float) and
      conditions, `_X op bound` (op `<`, `<=`, `>` or `>=`). -/
  refines : List (String × Ty × List (String × Value)) := []
  /-- The enums declared `enum<open>` (Book of Verse ch. 9): a `case` on one
      needs `_`, as it may gain values. -/
  openEnums : List String := []
  /-- The `case` arms marked `@ignore_unreachable`, by where `elabCase`
      reports an arm never reached: such an arm is kept, and never runs
      when it is never reached (Book of Verse tests, `Enum.versetest`). -/
  ignoredArms : List Pos := []
  /-- The places of the filters of every `for`, and every `first` with a
      generator, as written, each of which can fail (`forFilterPositions`,
      `elabSeqIn`). -/
  forFilters : List (Pos × String) := []
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
  /-- The interfaces referred to through views (#351): some class below
      gives one of them type arguments that are not a prefix of its own (or
      of an interface below them that does), so a reference to it relates
      its type arguments to each class's through the class's view. -/
  viewed : List String := []
  /-- (#515, `--signal-no-rollback`) Record the calls failure contexts make
      (`ESt.failCalls`). -/
  signalNoRollback : Bool := false
  /-- The variances of the classes in Verse Core, by tag and Verse Core type
      argument position (docs/research/variance.md): what the certificate
      gives (`Sigs.variances`), so that a conversion the front end makes by
      variance passes the checker's subtyping. Every class invariant until
      the classes are known (`Variance.coreVariances`). -/
  coreVariances : List (List Variance) := []
  /-- The Book's variance of each class's and interface's type parameters
      (`SVar`), by name; a type missing here is invariant in each. -/
  variances : List (String × List SVar) := []
  /-- The methods each class and interface declares, each with its parameter
      types (the receiver left out) and its result type, over the type's
      parameters: what its variances were found from, for the messages. -/
  memberSigs : List (String × List (String × List Ty × Ty)) := []
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
  /-- The fields a class re-declares at a type below the one it inherits
      (`Fields.narrowings`): its objects, and those of the classes below
      it, hold the field at that type (`TyEnv.fieldSrc`), and a read
      through a class or interface above it converts it up. -/
  narrowed : List (String × String) := []
  /-- The classes marked `<concrete>`: the values of a `concrete_subtype`
      (`TypeValues`), whose constructions `T{}` may run. -/
  concreteMarked : List String := []
  fieldAccBase : Nat := 0
  /-- (#283) The uses `R.M` whose family of methods `M` only the class of
      `R` tells (`Choice.methodFns`), by place and `M`: their elaboration
      notes the root that class is below (`ESt.needs`). -/
  familySites : List (Pos × String) := []
  /-- (#283) The methods left in their classes as a family's stub
      (`Choice.familyStub`), as functions (`C.M`): no call names one in the
      program given out, and none is a value. -/
  familyStubs : List String := []
  /-- (#283) The calls of overloaded functions whose overload decides
      whether they have several values (`Choice.inlineMulti`), by place and
      name: their elaboration notes the overload each takes (`ESt.needs`). -/
  overloadSites : List (Pos × String) := []
  /-- (#283) The consumers in recursive groups' code whose names' types this
      elaboration notes (`$noteTypes`), by `Choice.nestKey`: their groups are
      kept with one value until then (`Choice.inlineFns`). -/
  nestedSites : List String := []
  /-- (#283) The structs and classes whose field orders this elaboration notes
      (`TyEnv.fieldOrder`, `Requests.fieldOrders`): constructed with a choice
      point in a field in the code of groups kept with one value until then. -/
  fieldSites : List String := []
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
  /-- What earlier elaborations asked for (`Options.requests`): the
      functions as values, method adapters, branches of refining casts and
      helpers this one makes and calls. -/
  requests : Requests := {}
  deriving Inhabited

/-- The fields of struct `n` applied to the type arguments `args`. -/
def TyEnv.concurrencyName (env : TyEnv) (n : String) : String :=
  (env.concurrencyNames.lookup n).getD n

def TyEnv.fields (env : TyEnv) (n : String) (args : List Ty := []) : List (String × Ty × Option SExpr) :=
  let fs := (env.structs.lookup n).getD []
  match env.sparams.lookup n with
  | some ps =>
    let σ := (ps.map (·.1)).zip args
    fs.map fun (f, t, d) => (f, t.subst σ, d)
  | none => fs

/-- A struct's or class's fields in the order its constructions evaluate
    them in, each with whether its default is more than a literal: the
    lifter's view of a construction (`Choice.FieldOrder`), for the
    elaborator's and, noted by an earlier elaboration, for `inlineMulti`'s
    (#283); none for a type of no fields known. -/
def TyEnv.fieldOrder (env : TyEnv) (n : String) : List (String × Bool) :=
  if (env.structs.lookup n).isNone then [] else
    (env.fields n).map fun (f, _, d) => (f, match d with
      | some d => !Choice.stable (fun _ => true) d
      | none => false)

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

/-- The empty value as Verse Core holds it at a type that has it. Verse has
    one empty value, written `false` or `()` (Book of Verse ch. 2, "void,
    true, tuple() and false"): it is the `logic` false, the `void` and
    `tuple()` value, the empty option, and the empty array, string and map. -/
def Ty.emptyValue? : Ty → Option Value
  | .logic => some (.logic false)
  | .void | .tup [] => some .void
  | .opt _ => some .none
  | .arr _ | .map _ _ | .weakMap _ _ => some Value.emptyArray
  | _ => none

/-- `b` is `a` with `tuple()` (the Book's `true`) for some of its `void`s,
    inside a container or a tuple too: one type, as the Book has it (ch. 2,
    "void, true, tuple() and false": "the types `void`, `true` and
    `tuple()` all describe it … These are interchangeable", "?void and
    ?true interchange"; the tests, `Void.versetest` 50-80, `[]void` to
    `[]true`), and one in Verse Core, where `void` is `tuple()`. Not a
    class's or an interface's type arguments, a function type's: the
    classes a call dispatches to are those at its type's arguments
    exactly. -/
partial def Ty.unitUp : Ty → Ty → Bool
  | .void, .tup [] => true
  | .arr a, .arr b | .opt a, .opt b => a.unitUp b
  | .map k v, .map k' v' | .weakMap k v, .weakMap k' v' => k == k' && v.unitUp v'
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).all fun (a, b) => a.unitUp b
  | a, b => a == b

/-- A type given as a program's parametric type's argument: its `void`s,
    outside function types, are `true` (`tuple()`), the empty value's type
    alone. Book of Verse ch. 2, "Write the value, not the type name"
    (`02_primitives.md:1311-1316`): "A parameter declared literally `:void`
    accepts any value … It does not work when `void` reaches the parameter
    through a type parameter", and "Conversion is one-way" (`:1371-1374`):
    "A *type parameter* bound to `[]void` is invariant, though, so only
    `[]void` (or `[]true`) fits there"; the tests, `Void.versetest` 227-279. -/
partial def Ty.voidArg : Ty → Ty
  | .void => .tup []
  | .arr t => .arr t.voidArg
  | .opt t => .opt t.voidArg
  | .map k v => .map k v.voidArg
  | .tup ts => .tup (ts.map Ty.voidArg)
  | t => t

/-- The types of the empty value alone: `tuple()`, and `void`, which takes any value and makes it that one (Book of Verse
    ch. 2: "Any value converts to `void`"). -/
def Ty.isUnit : Ty → Bool
  | .void | .tup [] => true
  | _ => false

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
    -- (#53), then its other type parameters: those it gives the interface
    -- it lists with the most, of which every other one's are a prefix (an
    -- interface it lists without type arguments gives none, #276)
    -- (each at the Verse Core type arguments the interface gives its own
    -- parents in turn: `c2(t) := interface(container([]t))`'s are `[]t, t`)
    -- (also an interface without type parameters whose parents it gives
    -- some, `intI := interface(container(int))`'s `int`)
    let ias := (env.info d).ifaces.filterMap fun i =>
      let ca := env.coreArgs i ((env.iargs.lookup (d, i)).getD [])
      if ca.isEmpty then none else some ca
    match ias.foldl (fun (b : Option (List Ty)) ia => match b with
        | some b => if b.length < ia.length then some ia else some b
        | none => some ia) none with
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

/-- The name that stands for the `j`-th Verse Core type argument in a pin (#209). -/
def pinArg (j : Nat) : String := s!"$pos{j}"

/-- (#351) The Verse Core type arguments that an object of class `d` gives
    interface `n`, over its own Verse Core type arguments `X`: through the
    topmost class of `d`'s chain below `n` (which reaches it), whose places
    `d`'s share, so a class that fixes one of them (`ib := class(both(int,
    string))`) still has the view at its place. -/
partial def TyEnv.viewOf (env : TyEnv) (n d : String) (X : List Ty) : List Ty :=
  let rec top (fuel : Nat) (c : String) : String :=
    match fuel, (env.info c).parent with
    | f + 1, some q => if env.isSub q n then top f q else c
    | _, _ => c
  let r := top (env.classes.length + 1) d
  let vars := env.coreVars r
  let rargs := ((env.sparams.lookup r).getD []).map fun (v, _) => match vars.findIdx? (·.1 == v) with
    | some j => X.getD j Ty.void
    | none => Ty.void
  -- (a part that is one of the class's Verse Core type arguments, which it
  -- fixes to a compound of its own, is that one's place: the view of `i0` at
  -- `c1(t) := class(i2(tuple(t, int)))` is its first, `X 0`, not
  -- `tuple(X 1, int)`, so that a reference with only that first one, an
  -- `i2(…)`, fits it, #351)
  let rec hasParam : Ty → Bool
    | .param .. => true
    | .arr u | .opt u => hasParam u
    | .tup us | .struct _ us => us.any hasParam
    | .map k v | .weakMap k v => hasParam k || hasParam v
    | _ => false
  let places := ((env.coreArgs r rargs).zipIdx.filter fun (t, _) =>
    (match t with | .param .. => false | _ => true) && hasParam t).map fun (t, j) => (t, X.getD j Ty.void)
  let rec back (t : Ty) : Ty := match places.find? (·.1 == t) with
    | some (_, x) => x
    | none => match t with
      | .arr u => .arr (back u)
      | .opt u => .opt (back u)
      | .tup us => .tup (us.map back)
      | .struct m us => .struct m (us.map back)
      | .map k v => .map (back k) (back v)
      | .weakMap k v => .weakMap (back k) (back v)
      | u => u
  (env.coreArgs n (env.upArgs r rargs n)).map back

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
    class `d`'s Verse Core layout: the nearest class of `d`'s chain that
    re-declares it at a narrower type (`narrowed`), else the topmost
    interface above `d` that declares it (#53), else the topmost class in
    `d`'s chain that has it. Two unrelated interfaces may both declare it:
    the first `d` lists. -/
def TyEnv.fieldSrc (env : TyEnv) (d f : String) : Option String :=
  -- (the nearest class of `d`'s chain that re-declares it at a narrower
  -- type, `narrowed`, holds it at that type, as the classes below it do)
  let chain0 := (env.supers d).filter fun x => !(env.info x).isIface
  if let some n := (if env.narrowed.isEmpty then none else chain0.find? (fun x => env.narrowed.contains (x, f))) then some n else
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
      -- (an interface referred to through views is not at a prefix of the
      -- object's type arguments: its own are those `d` gives it, #351)
      let dArgs := if env.viewed.contains D && D != d then env.upArgs d (env.argsAt T targs d) D
        else env.argsAt T targs D
      let σ := (((env.sparams.lookup D).getD []).map (·.1)).zip dArgs
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

/-- The variances of the classes in Verse Core (`Sigs.var` of the
    certificate the front end gives). -/
def TyEnv.coreVar (env : TyEnv) : Variances := ({ fns := [], variances := env.coreVariances } : Sigs).var

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
  | .map k v | .weakMap k v => k.holdsMutable env seen || v.holdsMutable env seen
  | .struct n ts =>
    if env.classes.contains n then
      -- an object below `n`, or one its fields reach (by instantiation, #39;
      -- one that grows without end is taken to: a large one inside a
      -- smaller one, not a large one by itself)
      let key := (Ty.struct n ts).show
      if seen.length > 16 || (key.length > 400 && seen.any (·.length < key.length)) then true
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
  | .map k v | .weakMap k v => k.structNames ++ v.structNames
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

/-- The interface every value converted to `any` is an object below, in a
    program that calls `ToDiagnostic` (`Front/Diagnostic.lean`). -/
def anyInterfaceName : String := "$anything"

/-- Whether an `any` keeps what it needs to print itself: in a program
    that calls `ToDiagnostic`, whose helpers define `$anything`, a value
    converted to `any` is an object below it (`Diagnostic`, `convert`), and
    an `any` is that interface's reference in Verse Core; elsewhere it is
    `void`, a value becoming one by being evaluated. -/
def TyEnv.anyWraps (env : TyEnv) : Bool := env.classes.contains anyInterfaceName

/-- The Verse Core type of a front-end type (`false`, the bottom type, has
    no values; slots and signatures never have it). -/
partial def Ty.toVTy (env : TyEnv) : Ty → VTy
  | .int | .char32 => .int
  | .any => if env.anyWraps then Ty.toVTy env (.struct anyInterfaceName []) else VTy.void
  | .dyn => .dyn
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
    -- (an interface referred to through views, #351: each class below, with
    -- the interface's Verse Core type arguments over its own)
    if env.viewed.contains n then
      let ents := (env.concreteBelow n ++ env.phs.filter (env.isSub · n)).map fun d =>
        let X := (List.range (env.coreVars d).length).map fun j => Ty.param (pinArg j) false
        (env.tagOf d, (env.viewOf n d X).map (Ty.toVTy { env with tvars := X.zipIdx.map fun (x, j) => (pinArg j, x) }))
      .vref ents ((env.coreArgs n ts).map (Ty.toVTy env))
    else if env.isRefClass n then .ref (env.refTags n) ((env.coreArgs n ts).map (Ty.toVTy env))
    else if env.classes.contains n then
      -- one option per concrete class at or below `n`
      .tup ((env.concreteBelow n).map fun d =>
        .opt (.tup ((env.fields d (if d == n then ts else [])).map fun (_, t, _) => t.toVTy env)))
    else .tup ((env.fields n ts).map fun (_, t, _) => t.toVTy env)
  | .enum _ => .int
  -- (a weak map is held as a map, docs/research/weak-map.md)
  | .map k v | .weakMap k v => .arr (.tup [k.toVTy env, v.toVTy env])
  -- the j-th type parameter of the generic function being elaborated
  | .param n _ => match env.tvars.findIdx? (·.1 == n) with
    | some j => .var j
    | none => VTy.void

/-- Field `f`'s type in class `d`'s Verse Core layout, the class table's,
    over the Verse Core type arguments the hierarchy shares. -/
def TyEnv.coreFieldTy (env : TyEnv) (d f : String) : Option VTy := do
  let D ← env.fieldSrc d f
  let (_, t, _) ← (env.fields D).find? (·.1 == f)
  -- (#351) an interface referred to through views is not at a prefix of the
  -- class's type arguments: its type parameters are the class's view of it
  if env.viewed.contains D && d != D && !(env.info d).isIface then
    let X := (List.range (env.coreVars d).length).map fun j => Ty.param (pinArg j) false
    let view := env.viewOf D d X
    let σ := (env.coreVars D).zipIdx.filterMap fun ((v, _), j) =>
      if v.startsWith "$arg" then none else some (v, view.getD j Ty.void)
    return (t.subst σ).toVTy { env with tvars := X.zipIdx.map fun (x, j) => (pinArg j, x) }
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
  | .map k v | .weakMap k v => k.params ++ v.params
  | _ => []

/-- The interfaces `i(args)` reaches through the parent interfaces it lists,
    with their resolved type arguments (#53): itself first. -/
partial def TyEnv.ifaceInstances (env : TyEnv) (i : String) (args : List Ty) : List (String × List Ty) :=
  let σ := (((env.sparams.lookup i).getD []).map (·.1)).zip args
  (i, args) :: (env.info i).ifaces.flatMap fun p =>
    env.ifaceInstances p (((env.iargs.lookup (i, p)).getD []).map (·.subst σ))

/-- How many of class `d`'s Verse Core type arguments its root class
    gives: as many as the interface with the fewest type parameters that is
    at or above it or above a class below it (#53, #276), else all of its
    own. The others are type parameters added below the root, or not given
    by some interface, which a dispatch from it opens; every class of the
    hierarchy agrees on them, so a subclass may implement an interface
    that gives fewer than its parent's (#209). -/
partial def TyEnv.rootArgCount (env : TyEnv) (d : String) : Nat :=
  match (env.info d).parent with
  | some q => env.rootArgCount q
  | none =>
    let own := (env.coreArgs d (((env.sparams.lookup d).getD []).map fun (v, k) => Ty.param v k)).length
    let subtree := env.classes.filter fun c => env.rootOf c == d
    -- (an interface above a class below the root counts only when one of
    -- the root's type arguments it does not give is still a type parameter
    -- there: one the class fixes is given by its pins, #276)
    subtree.foldl (fun m c =>
      let ca := env.coreArgs c (((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k)
      ((env.supers c).filter (env.info · |>.isIface)).foldl (fun m i =>
        let k := ((env.sparams.lookup i).getD []).length
        if c == d || ((ca.take own).drop k).any (!·.params.isEmpty) then min m k else m) m) own

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

/-- The pins of class `d` as Verse Core has them: `corePins`, and for a
    class below an interface referred to through views, `none` on the rest
    of its Verse Core type arguments, so that a dispatch through a view
    opens them (`Typed.dispatch_view`, #351). A dispatch tests classes
    whose Verse Core pins agree, so it groups them by these. -/
def TyEnv.dispatchPins (env : TyEnv) (d : String) : List (Option Ty) :=
  if !(env.info d).isIface && !env.phs.contains d && env.viewed.any (env.isSub d ·) then
    -- (its own pins, also when nothing else makes it pinned: they relate
    -- its type arguments, `c3(t) := class(c0(t, t), …)`'s second to its
    -- first, which the view alone may not give)
    let ps := env.pinsOf d
    let n := (env.coreArgs d (((env.sparams.lookup d).getD []).map fun (v, c) => Ty.param v c)).length
    ps ++ List.replicate (n - ps.length) none
  else env.corePins d

/-- Code generic over `T` can treat a `d` below it under the refinement
    its pins give (#142, #209): `d`'s pins determine its Verse Core type
    arguments (`pinsOf`), and are on all of them, so an object has those
    beyond `T`'s too, which a dispatch on a `T` opens (`Typed.dispatch`). -/
def TyEnv.sameCorePinned (env : TyEnv) (d T : String) : Bool :=
  let core (c : String) := env.coreArgs c (((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k)
  (core T).length ≤ (core d).length

/-- Whether `false` (the bottom type) occurs in a type. -/
partial def Ty.hasNever : Ty → Bool
  | .never => true
  | .arr t | .opt t => t.hasNever
  | .tup ts => ts.any Ty.hasNever
  | .map k v | .weakMap k v => k.hasNever || v.hasNever
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
  -- (a map is a weak map, Book of Verse ch. 3)
  | .weakMap pk pv, .map ak av | .weakMap pk pv, .weakMap ak av => do
    Ty.matchArg env (← Ty.matchArg env σ pk ak) pv av
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
    | .map k v, .map k' v' | .weakMap k v, .weakMap k' v' => Ty.unifyEqs fieldsOf σ ((k, k') :: (v, v') :: rest)
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
        | .map k v | .weakMap k v => [k, v]
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
  -- (a weak map is not, Book of Verse ch. 3: "no coercion to `comparable`")
  | .weakMap .. => false
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

/-- Disjoint overload domains (Book ch. 6 and `IndistinctOverloads.versetest`).
    Types that both have the empty value (`Ty.emptyValue?`: a logic, an
    option, an array, a string, a map, `tuple()`) overlap; `void`, which
    takes any value, and unknown types overlap every type. A nonempty tuple
    separates from an array if one element does, from a map if its key is
    disjoint from int, and from an option if its element is disjoint from int.
    Function types cannot separate from arrays or maps, regardless of their
    signatures; this is an admission rule, not a container/function coercion.
    Class/interface and numeric overlap rules are unchanged. -/
private def TyEnv.disjointStep (env : TyEnv) (apart : Ty → Ty → Bool) (a b : Ty) : Bool :=
  -- (two types that both have the empty value have that value in common:
  -- `false` is an empty array, map, option, string, a logic and `()`)
  if a.emptyValue?.isSome && b.emptyValue?.isSome then false else
  match a, b with
  | .void, _ | _, .void | .param .., _ | _, .param .. | .never, _ | _, .never => false
  -- (every value is an any, #138)
  | .any, _ | _, .any => false
  -- (every comparable value is a comparable, Book of Verse ch. 11: `F(:int)`
  -- and `F(:comparable)` are not distinct, `F(:c)` of a class that is not
  -- `<unique>` and `F(:comparable)` are)
  -- (`<unique>` classes and interfaces too, values or not)
  | .dyn, b | b, .dyn => match b with
    | .struct n _ => if env.classes.contains n then !env.isUnique n else !b.comparable env
    | _ => !b.comparable env
  -- (a refinement overlaps what its base does, #136)
  | .refine n, b => match env.refines.lookup n with
    | some (base, _) => apart base b
    | none => false
  | a, .refine n => match env.refines.lookup n with
    | some (base, _) => apart a base
    | none => false
  -- (an int is also a rational, #116)
  | .int, .rational | .rational, .int => false
  | .tup as, .tup bs => as.length != bs.length || (as.zip bs).any fun (a, b) => apart a b
  | .tup ts, .arr t => ts.any (apart · t)
  | .arr t, .tup ts => ts.any (apart t ·)
  | .tup ts, .map k _ | .tup ts, .weakMap k _ => !ts.isEmpty && apart .int k
  | .map k _, .tup ts | .weakMap k _, .tup ts => !ts.isEmpty && apart k .int
  | .tup ts, .opt t => !ts.isEmpty && apart .int t
  | .opt t, .tup ts => !ts.isEmpty && apart t .int
  | .struct n _, .arr _ | .arr _, .struct n _ |
    .struct n _, .map .. | .map .., .struct n _ |
    .struct n _, .weakMap .. | .weakMap .., .struct n _ => (FnValues.parseName n).isNone
  | .struct a as, .struct b bs =>
    let isCls (x : String) := env.classes.contains x
    let iface (x : String) := isCls x && (env.info x).isIface
    if isCls a && isCls b then
      -- one parametric class at disjoint type arguments
      if a == b && !iface a then as.length == bs.length && (as.zip bs).any fun (x, y) => apart x y
      else if iface a || iface b then
        -- a <final> class, which nothing is below, and an interface it does
        -- not implement (#100)
        let finalNot (c i : String) : Bool := !iface c && (env.info c).isFinal && !env.isSub c i
        (iface a && finalNot b a) || (iface b && finalNot a b)
      else !(env.isSub a b || env.isSub b a)
    else if isCls a || isCls b then true
    else a != b || (as.length == bs.length && (as.zip bs).any fun (x, y) => apart x y)
  | .enum a, .enum b => a != b
  | .int, .int | .logic, .logic | .char, .char | .char32, .char32 | .rational, .rational | .float, .float => false
  | _, _ => true

partial def TyEnv.disjoint (env : TyEnv) (a b : Ty) : Bool :=
  env.disjointStep env.disjoint a b

/-- Compare two independently quantified domains. Each side may use its own
    upper bounds, even when the signatures spell their formals alike. Any
    separating upper view suffices; missing views and cycles do not prove
    separation. The ordinary nominal/interface overlap rules still apply. -/
partial def TyEnv.disjointUnder (env : TyEnv) (aBounds bBounds : List (Ty × Ty)) (a b : Ty) : Bool :=
  go (aBounds.length + bBounds.length + 1) a b
where
  go (fuel : Nat) (a b : Ty) : Bool :=
    env.disjointStep (go fuel) a b || match fuel with
    | 0 => false
    | fuel + 1 =>
      aBounds.any (fun (upper, lower) => lower == a && go fuel upper b) ||
      bBounds.any (fun (upper, lower) => lower == b && go fuel a upper)

/-- Whether two overloads (their positional parameters, then named ones:
    name, has a default, type) are distinct: their positional parameters
    are, or a call cannot give both what they need, as some named parameter
    one of them requires is missing from the other or takes disjoint types in
    the two (Book of Verse ch. 6: order and defaults do not distinguish). -/
def TyEnv.namedDistinct (env : TyEnv) (na nb : List (String × Bool × Ty))
    (aBounds bBounds : List (Ty × Ty) := []) : Bool :=
  let req := ((na.filter (!·.2.1)).map (·.1)) ++ ((nb.filter (!·.2.1)).map (·.1))
  !(req.all fun x => match na.find? (·.1 == x), nb.find? (·.1 == x) with
    | some (_, _, ta), some (_, _, tb) => !env.disjointUnder aBounds bBounds ta tb
    | _, _ => false)

/-- Two overloads' parameters: no call fits both. Compare a single explicit
    tuple with the other signature's flattened types, including their domains,
    rather than treating equal flattened arity alone as ambiguity. -/
def TyEnv.paramsDistinct (env : TyEnv) (as bs : List Ty)
    (aBounds bBounds : List (Ty × Ty) := []) : Bool :=
  let apartTy := env.disjointUnder aBounds bBounds
  let flat (xs : List Ty) : List Ty := match xs with
    | [.tup ts] => ts
    | [.void] => []
    | _ => xs
  let apart (cmp : Ty → Ty → Bool) (xs ys : List Ty) :=
    xs.length != ys.length || (xs.zip ys).any fun (a, b) => cmp a b
  -- Both the original argument and its flattened fields are admitted.
  -- Keep the direct overlap of void, arrays and opaque type parameters.
  let packedApart (cmp : Ty → Ty → Bool) (xs ys : List Ty) := match xs with
    | [t] => if ys.length > 1 then cmp t (.tup ys) else
      match t with
      | .param .. => !ys.isEmpty || cmp t .void
      | _ => true
    | _ => true
  -- A call can also supply one tuple containing the positional arguments.
  -- In particular, tuple(int) both unpacks to int and packs into
  -- tuple(tuple(int)). Compare that actual input shape with the other
  -- formal, rather than applying the broader tuple/container admission
  -- rules to a synthetic tuple (which would conflate int with ?int).
  let tupleInputApart (cmp : Ty → Ty → Bool) (xs ys : List Ty) := match ys with
    | [t] => match t with
      | .tup ts => apart cmp xs ts
      | .arr t => xs.isEmpty || xs.any (cmp · t)
      | .param .. | .dyn => cmp (.tup xs) t
      | .void | .any => false
      | _ => true
    | _ => true
  [as, flat as].all fun xs => [bs, flat bs].all fun ys =>
    apart apartTy xs ys && packedApart apartTy xs ys && packedApart (flip apartTy) ys xs &&
      tupleInputApart apartTy xs ys && tupleInputApart (flip apartTy) ys xs

/-- A type built from the primitive comparable types (#214). -/
partial def Ty.plainComparable : Ty → Bool
  | .int | .logic | .char | .char32 | .rational | .float => true
  | .arr t | .opt t => t.plainComparable
  | .tup ts => ts.all Ty.plainComparable
  | .map k v => k.plainComparable && v.plainComparable
  | _ => false

/-- The array or map inside a map key type, through its options, tuples and
    a struct's fields, if any: comparable as they are, neither may be a map
    key, but `string` may (Book of Verse ch. 3: "neither may serve as a map
    key … The one exception is `string`"; `?[]int` and `tuple(int, []int)`
    "are rejected for the array buried inside them"; "The restriction
    travels with the array"), a parametric struct's at its type arguments.
    A class's fields are not its key: a `<unique>` object is compared by
    identity. -/
partial def Ty.keyContainer? (env : TyEnv) (seen : List String := []) : Ty → Option Ty
  | .arr .char => none
  | t@(.arr _) => some t
  | t@(.map ..) => some t
  | .opt t => t.keyContainer? env seen
  | .tup ts => ts.findSome? (·.keyContainer? env seen)
  | .struct n ts =>
    if env.classes.contains n || seen.contains n then none
    else (env.fields n ts).findSome? fun (_, ft, _) => ft.keyContainer? env (n :: seen)
  | _ => none

/-- Whether every map key type inside `t` is comparable. -/
partial def Ty.mapKeysOK (env : TyEnv) : Ty → Bool
  | .map k v | .weakMap k v => k.comparable env && k.mapKeysOK env && v.mapKeysOK env
  | .arr t | .opt t => t.mapKeysOK env
  | .tup ts | .struct _ ts => ts.all (Ty.mapKeysOK env)
  | _ => true

/-- `t` with each part that is one of `ps`'s first types replaced by its
    second, outermost first (`Ctx.unrefine`, #209). -/
partial def Ty.unrefine (ps : List (Ty × Ty)) (t : Ty) : Ty :=
  match ps.find? (·.1 == t) with
  | some (_, r) => r
  | none => match t with
    | .arr u => .arr (u.unrefine ps)
    | .opt u => .opt (u.unrefine ps)
    | .tup ts => .tup (ts.map (Ty.unrefine ps))
    | .struct n ts => .struct n (ts.map (Ty.unrefine ps))
    | .map k v => .map (k.unrefine ps) (v.unrefine ps)
    | .weakMap k v => .weakMap (k.unrefine ps) (v.unrefine ps)
    | u => u

/-- (#351) The type arguments of class `d` (as its type parameters) for one
    of its objects that is an `n(args)` for interface `n`, referred to
    through views: those that make `d`'s view of `n` `args`, at `d`'s pins;
    any others `void`. None when no object of `d` is one (its pins fix one
    that differs, or, `rigid`, one of `args` is a type parameter of the code
    there, which no fixed one equals). -/
def TyEnv.viewArgs? (env : TyEnv) (n d : String) (args : List Ty) (rigid : Bool := true) : Option (List Ty) :=
  let vars := env.coreVars d
  let X := (List.range vars.length).map fun j => Ty.param s!"$vw{j}" false
  let atX := X.zipIdx.map fun (x, j) => (pinArg j, x)
  let pinEqs := (X.zip (env.dispatchPins d)).filterMap fun (x, pin) => pin.map fun pt => (x, pt.subst atX)
  let coreFields (m : String) (ts : List Ty) : Option (List Ty) :=
    if env.classes.contains m then none else some ((env.fields m ts).map (·.2.1))
  match Ty.unifyEqs coreFields [] ((env.viewOf n d X).zip args ++ pinEqs) with
  | some μ =>
    if rigid && !μ.all (·.1.startsWith "$vw") then none else
    let rest := X.filterMap fun | .param x _ => some (x, Ty.void) | _ => none
    some (((env.sparams.lookup d).getD []).map fun (v, _) => match vars.findIdx? (·.1 == v) with
      | some j => ((X.getD j Ty.void).subst μ).subst rest
      | none => Ty.void)
  | none => none

/-- The value of a prototype's field of type `t`: its type's default, or a
    reference to a prototype already allocated (`done`: class, address). -/
partial def protoValue (env : TyEnv) (done : List (String × Nat)) : Ty → Option Value
  | .int | .char32 | .enum _ => some (.int 0)
  | .rational => some (.tup [.int 0, .int 1])
  | .float => some (.float 0)
  | .dyn => some .void
  | .any => if env.anyWraps then protoValue env done (.struct anyInterfaceName []) else some .void
  | .refine n => match env.refines.lookup n with
    | some (.float, _) => some (.float 0)
    | _ => some (.int 0)
  | .logic => some (.logic false)
  | .char => some (.char 0)
  | .void | .never => some .void
  | .arr _ | .map _ _ | .weakMap _ _ => some (.arr #[])
  | .opt _ => some .none
  | .tup ts => (ts.mapM (protoValue env done)).map .tup
  | t@(.struct n ts) =>
    if env.isRefClass n then
      ((env.concreteBelow n).findSome? fun d =>
        -- (through a view, its arguments as the class gives them, #351)
        if (if env.viewed.contains n then env.viewOf n d (env.coreArgs d []) else env.coreArgs d []) ==
            env.coreArgs n ts then (done.lookup d).map Value.ref else none)
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

/-- The type parameters a type mentions, with whether each is comparable. -/
partial def Ty.paramsC : Ty → List (String × Bool)
  | .param n c => [(n, c)]
  | .arr t | .opt t => t.paramsC
  | .tup ts | .struct _ ts => ts.flatMap Ty.paramsC
  | .map k v | .weakMap k v => k.paramsC ++ v.paramsC
  | _ => []

/-- The unknown parameter bounds needed to make this type comparable.
    Unique references need no bound on their arguments; value structs follow
    the same argument/field rule as `Ty.comparable`. -/
partial def Ty.comparableNeeds? (env : TyEnv) : Ty → Option (List String)
  | .param n false => some [n]
  | .param _ true => some []
  | .arr t | .opt t => t.comparableNeeds? env
  | .tup ts => ts.foldlM (fun ns t => do return (ns ++ (← t.comparableNeeds? env)).eraseDups) []
  | .map k v => do return ((← k.comparableNeeds? env) ++ (← v.comparableNeeds? env)).eraseDups
  | .weakMap .. => none
  | .struct n ts =>
    if env.isRefClass n then if env.isUnique n then some [] else none
    else if env.classes.contains n then none else
      (ts ++ (env.fields n ts).map (·.2.1)).foldlM
        (fun ns t => do return (ns ++ (← t.comparableNeeds? env)).eraseDups) []
  | .any | .never => none
  | _ => some []

/-- Comparable bounds declared by a class/interface, at these arguments. -/
def TyEnv.comparableArgs (env : TyEnv) (n : String) (args : List Ty) : List Ty :=
  (((env.sparams.lookup n).getD []).zip args).filterMap fun ((_, cmp), t) => if cmp then some t else none

/-- Preserve known comparable facts through type equations, then add only
    the bounds implied by the selected target's constrained arguments.
    Boolean evidence changes no type identity or Verse Core representation. -/
def TyEnv.refineComparable? (env : TyEnv) (μ : List (String × Ty)) (required : List Ty) :
    Option (List (String × Ty)) := do
  let known := env.tvars.flatMap fun (_, t) => t.paramsC.filterMap fun (n, cmp) =>
    if cmp then some (Ty.param n true) else none
  let names ← (known ++ required).foldlM (fun ns t => do
    let needs ← (t.subst μ).comparableNeeds? env
    return (ns ++ needs).eraseDups) []
  let bounds := names.map fun n => (n, Ty.param n true)
  let μ := μ.map fun (n, t) => (n, t.subst bounds)
  return μ ++ bounds.filter fun (n, _) => !μ.any (·.1 == n)

/-- Bounds guaranteed by both values of the same type identity. A branch
    join cannot provide a stronger bound merely because its first arm does. -/
partial def Ty.commonBounds : Ty → Ty → Ty
  | .param n a, .param _ b => .param n (a && b)
  | .arr a, .arr b => .arr (a.commonBounds b)
  | .opt a, .opt b => .opt (a.commonBounds b)
  | .tup as, .tup bs => .tup ((as.zip bs).map fun (a, b) => a.commonBounds b)
  | .map a b, .map c d => .map (a.commonBounds c) (b.commonBounds d)
  | .weakMap a b, .weakMap c d => .weakMap (a.commonBounds c) (b.commonBounds d)
  | .struct n as, .struct _ bs => .struct n ((as.zip bs).map fun (a, b) => a.commonBounds b)
  | a, _ => a

/-- Restore an outer scope's parameter bounds without reinterpreting
    already-resolved parameter identities as lexical type aliases. -/
partial def Ty.withParamBounds (bounds : List (String × Bool)) : Ty → Ty
  | .param n _ => .param n ((bounds.lookup n).getD false)
  | .arr t => .arr (t.withParamBounds bounds)
  | .opt t => .opt (t.withParamBounds bounds)
  | .tup ts => .tup (ts.map (Ty.withParamBounds bounds))
  | .map k v => .map (k.withParamBounds bounds) (v.withParamBounds bounds)
  | .weakMap k v => .weakMap (k.withParamBounds bounds) (v.withParamBounds bounds)
  | .struct n ts => .struct n (ts.map (Ty.withParamBounds bounds))
  | t => t

/-- Merge repeated parameter requirements, retaining the strongest bound
    without changing the parameter order. -/
def Ty.mergeParamBounds (xs : List (String × Bool)) : List (String × Bool) :=
  xs.foldl (fun acc (n, cmp) => if acc.any (·.1 == n) then
    acc.map fun (m, old) => (m, old || (m == n && cmp)) else acc ++ [(n, cmp)]) []

/-- `a` is `b` or a subtype a call converts to it at a parameter or a
    result (#214): `int` to `rational`, a class to one above it, and a
    function type to one whose shape is above its own at the same
    arguments (#503). -/
def TyEnv.convertsAt (env : TyEnv) (a b : Ty) : Bool :=
  a == b || (a == .int && b == .rational) || match a, b with
    | .struct x [], .struct y [] => x != y && env.isSub x y
    -- (a map is a weak map of its key and value types, the same value,
    -- Book of Verse ch. 3)
    | .map k v, .weakMap k' v' => k == k' && v == v'
    | .struct x xs, .struct y ys =>
      match FnValues.parse x, FnValues.parse y with
      | some s, some t => s.within t && s.select t xs == ys
      | _, _ => false
    | _, _ => false

/-- A value of function type `own` (a shape's interface at its arguments)
    fits function type `t` by variance (#231): a shape above its own (the
    same positional parameters, effects among `t`'s, names it has, #503),
    contravariant parameters and a covariant result. -/
def fnTyFits (env : TyEnv) (own t : Ty) : Bool :=
  match own, t with
  | .struct om ots, .struct tm tts =>
    match FnValues.parse om, FnValues.parse tm with
    | some os, some ts =>
      let subAt := env.convertsAt
      let ots := os.select ts ots
      os.within ts && ots.length == tts.length &&
        ((tts.take ts.arity).zip (ots.take ts.arity)).all (fun (q, p) => subAt q p) &&
        subAt ((ots.drop ts.arity).headD .void) ((tts.drop ts.arity).headD .void)
    | _, _ => false
  | _, _ => false

/-- The Verse Core type of the fields of class `d`, as a front-end type. -/
def classRepTy (env : TyEnv) (d : String) (args : List Ty := []) : Ty :=
  .tup ((env.fields d args).map (·.2.1))

/-- Values of `t` are their own boxes (`Code.id`, arrays and options of
    such): an int, a float, a logic, a char, a string, a refinement, a
    `comparable`, `()`, a `<unique>` object. -/
partial def Ty.boxId (env : TyEnv) : Ty → Bool
  | .int | .float | .logic | .char | .refine _ | .dyn | .void | .never | .tup [] => true
  | .arr t | .opt t => t.boxId env
  -- (a class: a reference, compared by identity; one with no concrete
  -- class below has no values)
  | .struct n _ => env.classes.contains n
  | _ => false

/-- Converting a value of `a` to `b` is the identity on values: `b` is `a`
    with `comparable` in places where `a` has a type whose values are their
    own boxes (`[]int` to `[]comparable`). -/
partial def Ty.boxIdTo (env : TyEnv) : Ty → Ty → Bool
  | .dyn, .dyn => true
  | a, .dyn => a.boxId env && a.comparable env
  | .arr a, .arr b | .opt a, .opt b => a.boxIdTo env b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).all fun (a, b) => a.boxIdTo env b
  | .map k v, .map k' v' => k.boxIdTo env k' && v.boxIdTo env v'
  | a, b => a == b

/-- The Book's variance of class or interface `n` at each of its type
    parameters (`SVar`); invariant where none is known. -/
def TyEnv.varianceOf (env : TyEnv) (n : String) : List SVar :=
  -- (a function type's shape is invariant here: a function value converts
  -- to another function type by an adapter made for it, #214, as its class
  -- fixes the shape's type arguments)
  if (FnValues.parse n).isSome then ((env.sparams.lookup n).getD []).map fun _ => .inv else
  match env.variances.lookup n with
  | some vs => vs
  | none => ((env.sparams.lookup n).getD []).map fun _ => .inv

mutual
/-- `a` is a reference class below the class or interface `b`, or an array
    or option of such: the same value has both types. A class's type
    arguments fit the other's by the Book's variance of the class above
    (`TyEnv.argsFit`), and Verse Core's subtyping (by its classes'
    variances, `TyEnv.coreVar`) must agree, as the value is not converted. -/
partial def refUp (env : TyEnv) (a b : Ty) (nested : Bool := false) : Bool :=
  match a, b with
  -- `false` (no value) is below every type; inside a container, where
  -- Verse Core has `void` for it, only below `void` and `any`, which it
  -- has as `void` too (#290)
  | .never, b => !nested || b == .void || b == .any
  | .struct S as, .struct T bs =>
    env.isRefClass S && env.isRefClass T && env.isSub S T &&
      (let us := env.upArgs S as T
       us == bs || (env.argsFit T us bs &&
         VTy.sub env.coreVar ((Ty.struct S as).toVTy env) ((Ty.struct T bs).toVTy env)))
  | .arr a, .arr b | .opt a, .opt b => refUp env a b true
  -- tuples pointwise, maps in their values (Core subtyping is covariant there)
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).all fun (a, b) => a == b || refUp env a b true
  | .map k a, .map k' b => k == k' && (a == b || refUp env a b true)
  -- (a map is a weak map, held alike, Book of Verse ch. 3)
  | .map k a, .weakMap k' b | .weakMap k a, .weakMap k' b => k == k' && (a == b || refUp env a b true)
  | _, _ => false
/-- A value of type argument `a` is one of `b` as it is (a class's type
    argument changes no value: `refUp`, a value that is its own box to
    `comparable`, a refinement to its base). -/
partial def TyEnv.argFits (env : TyEnv) (a b : Ty) : Bool :=
  a == b || refUp env a b true || a.boxIdTo env b ||
    match a, b with
    | .refine n, _ => (env.refines.lookup n).any (·.1 == b)
    -- (a class or interface with no object below it, below another: no value
    -- to hold either way; Verse Core's subtyping of the classes whose type
    -- arguments these are decides when they hold objects, `refUp`)
    | .struct S as, .struct T bs =>
      env.classes.contains S && env.classes.contains T && env.isSub S T && (env.concreteBelow S).isEmpty &&
        env.argsFit T (env.upArgs S as T) bs
    | _, _ => false
/-- Type arguments `us` of class or interface `T` fit `bs` by its variances:
    equal where it is invariant, below where covariant, above where
    contravariant, any where bivariant. -/
partial def TyEnv.argsFit (env : TyEnv) (T : String) (us bs : List Ty) : Bool :=
  us.length == bs.length &&
    ((env.varianceOf T).zip (us.zip bs)).all (fun (v, u, b) => match v with
      | .inv => u == b
      | .co => env.argFits u b
      | .contra => env.argFits b u
      | .bi => true) &&
    -- (past the parameters the variances know, equal)
    ((us.zip bs).drop (env.varianceOf T).length).all fun (u, b) => u == b
end

/-- A failed join is ambiguous only when two incomparable instantiated
    interfaces remain. A common name at incompatible arguments is not a
    common supertype: `box(int)` and `box(string)` can still join at `any`. -/
def ambiguousJoin (env : TyEnv) : Ty → Ty → Bool
  | .struct a as, .struct b bs =>
    if !env.classes.contains a || !env.classes.contains b then false else
    let common := (env.supers a).filter fun c =>
      env.isSub b c && env.argsAt a as c == env.argsAt b bs c
    if common.any (fun c => !(env.info c).isIface) then false else
    (common.filter fun c => !common.any (fun d => c != d && env.isSub d c)).length > 1
  | _, _ => false

/-- Nominal ancestry at exact projected arguments. This is a type relation,
    including uninhabited interfaces, independent of their representation. -/
def TyEnv.nominalSubtype (env : TyEnv) (derived base : Ty) : Bool :=
  derived == base || match derived, base with
    | .struct source args, .struct target targets =>
      env.classes.contains source && env.classes.contains target && env.isSub source target &&
        args.length == ((env.sparams.lookup source).getD []).length &&
        env.upArgs source args target == targets
    | _, _ => false

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

/-- A refinement may widen to its numeric base, an existing numeric upper,
    or a containing refinement of the same base. Literal membership is not
    a general subtype relation from the base back into a refinement. -/
def TyEnv.refinementSubtype (env : TyEnv) (source : String) (target : Ty) : Bool :=
  match env.refines.lookup source with
  | some (base, conditions) =>
    (base == .int || base == .float) &&
      (target == base || (base == .int && target == .rational) || match target with
        | .refine name => match env.refines.lookup name with
          | some (other, bounds) => base == other && intervalWithin (refineInterval conditions) (refineInterval bounds)
          | none => false
        | _ => false)
  | none => false

/-- Direct declaration subtyping, including bottom, the ordinary checked
    numeric embedding, and discarding to any/void. This stays separate from nominal ancestry
    used to choose a class/interface member view. -/
def TyEnv.directBoundSubtype (env : TyEnv) (derived base : Ty) : Bool :=
  env.nominalSubtype derived base || derived == .never ||
    (derived == .int && base == .rational) || base == .any || base == .void ||
    match derived with
    | .refine source => env.refinementSubtype source base
    | _ => false

/-- Entail a declaration constraint. Static facts permit
    type applications; they never authorize an executable unchecked cast. -/
partial def TyEnv.boundSubtype (env : TyEnv) (derived base : Ty) : Bool :=
  go [] derived base
where
  go (seen : List (Ty × Ty)) (current target : Ty) : Bool :=
    env.directBoundSubtype current target ||
      (!seen.contains (current, target) && Id.run do
        let seen := (current, target) :: seen
        let structural := match current, target with
          | .arr c, .arr a | .opt c, .opt a => go seen c a
          | .map k c, .map l a | .map k c, .weakMap l a | .weakMap k c, .weakMap l a =>
              isComparable env k && isComparable env l && go seen k l && go seen c a
          | .tup cs, .tup bases => cs.length == bases.length &&
              (cs.zip bases).all (fun (c, a) => go seen c a)
          | .tup cs, .arr a => !cs.isEmpty && cs.all (fun c => go seen c a)
          | _, _ => false
        return structural || env.boundFacts.any fun (upper, lower) =>
          go seen current lower && go seen upper target)

/-- Check this application's own bounds after its arguments are resolved. -/
def Ty.checkBoundHead (env : TyEnv) : Ty → Except String Unit
  | .struct name args => do
    let σ := (((env.sparams.lookup name).getD []).map (·.1)).zip args
    for (base, derived) in (env.sbounds.lookup name).getD [] do
      let base := base.subst σ
      let derived := derived.subst σ
      unless env.boundSubtype derived base do
        throw s!"type argument {derived.show} of {name} does not satisfy subtype({base.show})"
  | _ => pure ()

/-- Validate a previously resolved type tree, without revisiting nominal
    field layouts. Initial type resolution checks only each head once. -/
partial def Ty.checkBounds (env : TyEnv) : Ty → Except String Unit
  | .arr t | .opt t => t.checkBounds env
  | .tup ts => ts.forM (Ty.checkBounds env)
  | .map k v | .weakMap k v => do k.checkBounds env; v.checkBounds env
  | ty@(.struct _ args) => do
    args.forM (Ty.checkBounds env)
    ty.checkBoundHead env
  | _ => pure ()

end OpenVerse.Front
