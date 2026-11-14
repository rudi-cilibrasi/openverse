/-
  OpenVerse front end — the surface syntax tree of the supported Verse subset.
-/
import Std.Data.HashSet

namespace OpenVerse.Front

structure Pos where
  line : Nat
  col  : Nat
  /-- The file, for a definition imported from another file (#27). -/
  file : String := ""
  deriving Repr, Inhabited, BEq

def Pos.show (p : Pos) : String :=
  if p.file.isEmpty then s!"{p.line}:{p.col}" else s!"{p.file}:{p.line}:{p.col}"

/-- A qualified name `(q:)x` as written: its qualifier and its name (`q` may
    be a path whose segments are qualified themselves, `/a/(/b:)c`: the name
    is what follows the last `:)`). -/
def splitQual? (n : String) : Option (String × String) :=
  if !n.startsWith "(" then none else
  match (n.drop 1).toString.splitOn ":)" with
  | [] | [_] => none
  | parts => some (":)".intercalate parts.dropLast, parts.getLast!)

/-- A definition's name as a program can use it bare: `X` for `(q:)X`. -/
def bareName (n : String) : String := ((splitQual? n).map (·.2)).getD n

/-- A marker that the source writes a qualifier `(q:)` other than
    `(super:)`: `resolveModules` then reads the program's names, as it does
    those of a program with modules. -/
def qualifierMarker : String := "$uses:qualifiers"

/-- `n` after `pre`, when it starts with it: what a marker `pre…` marks. -/
def afterPrefix? (pre n : String) : Option String :=
  if n.startsWith pre then some (n.drop pre.length).toString else none

/-- A module's marker, `$module:A::B`: a constant the parser writes where
    the module `A::B` is defined, with the module's specifiers, and
    `resolveModules` reads and takes out. -/
def modulePrefix : String := "$module:"
def moduleMarker (path : String) : String := modulePrefix ++ path
def moduleMarker? (n : String) : Option String := afterPrefix? modulePrefix n

/-- A qualified definition's marker, `$qual:A::F|q` for `(q:)F` in module
    `A`, written before it: `resolveModules` checks that `q` names where
    `F` is, and takes it out. -/
def qualPrefix : String := "$qual:"
def qualMarker (name q : String) : String := s!"{qualPrefix}{name}|{q}"
def qualMarker? (n : String) : Option (String × String) := do
  let [name, q] := (← afterPrefix? qualPrefix n).splitOn "|" | none
  return (name, q)

/-- A `using{M}`'s marker, `$open:A::|M` for one written in module `A`:
    `resolveModules` opens `M` there, and takes it out. -/
def openPrefix : String := "$open:"
def openMarker (scope path : String) : String := s!"{openPrefix}{scope}|{path}"
def openMarker? (n : String) : Option (String × String) := do
  let [scope, path] := (← afterPrefix? openPrefix n).splitOn "|" | none
  return (scope, path)

/-- A constructor function's specifier, `$constructor:c` for
    `F<constructor>(…) := c{…}`, the class `c` it constructs: the classes'
    phases make it one of `c`'s constructors (`classMethods`). -/
def constructorPrefix : String := "$constructor:"
def constructorSpec (c : String) : String := constructorPrefix ++ c
def constructorSpec? (sp : String) : Option String := afterPrefix? constructorPrefix sp

/-- A constructor's delegation `D<constructor>(…)` to a constructor of the
    class `D` or one above it: the call of `$ctor:D` (`parseCtorItem`). -/
def delegationPrefix : String := "$ctor:"
def delegationHead (d : String) : String := delegationPrefix ++ d
def delegationHead? (n : String) : Option String := afterPrefix? delegationPrefix n

/-- Surface types. -/
inductive STy where
  /-- `int`, `logic`, `char`, `string`, `void` -/
  | name : String → STy
  /-- `[]t` -/
  | arr  : STy → STy
  /-- `?t` -/
  | opt  : STy → STy
  /-- `tuple(t₁, …)` -/
  | tup  : List STy → STy
  /-- `[k]v` -/
  | map  : STy → STy → STy
  /-- `name(t₁, …)`: a parametric struct applied to type arguments. -/
  | app  : String → List STy → STy
  /-- `type{_(:t₁, …)<effects>:r}` or `t₁->r`: a function type (#210), its
      parameter types, effect specifiers and result type. A named parameter
      `?N:t` comes last, as `STy.namedParam` (#503). -/
  | fn   : List STy → List String → STy → STy
  deriving Repr, Inhabited, BEq

/-- A function type's named parameter `?N:t`, or `?N:t = …` when a caller
    may omit it (`optional`), is an application of `?N` (`?N=`) to `t`
    (#503): every traversal of types sees `t`, and two function types'
    parameters match only by name. The default written in a type is not
    part of it (Book of Verse ch. 6). -/
def STy.namedParam (n : String) (optional : Bool) (t : STy) : STy :=
  .app ("?" ++ n ++ if optional then "=" else "") [t]

/-- A named parameter of a function type: its name, whether a caller may
    omit it, its type. -/
def STy.asNamedParam? : STy → Option (String × Bool × STy)
  | .app h [t] =>
    if h.startsWith "?" then
      let optional := h.endsWith "="
      some (((h.drop 1).dropEnd (if optional then 1 else 0)).toString, optional, t)
    else none
  | _ => none

/-- A type's immediate parts, in the order written: an array's or an
    option's element, a tuple's elements, a map's key then value, an
    application's arguments (not its head), a function type's parameters
    then result. -/
def STy.children : STy → List STy
  | .name _ => []
  | .arr t | .opt t => [t]
  | .tup ts | .app _ ts => ts
  | .map k v => [k, v]
  | .fn ps _ r => ps ++ [r]

/-- `t` with `f` applied to each of its immediate parts, the ones
    `children` lists, in that order; everything else is kept. -/
def STy.mapChildrenM [Monad m] (f : STy → m STy) : STy → m STy
  | .name n => pure (.name n)
  | .arr t => return .arr (← f t)
  | .opt t => return .opt (← f t)
  | .tup ts => return .tup (← ts.mapM f)
  | .map k v => return .map (← f k) (← f v)
  | .app n ts => return .app n (← ts.mapM f)
  | .fn ps es r => return .fn (← ps.mapM f) es (← f r)

/-- Fold over written type names in source order, including application
    heads (`box` in `box(t)`) and function parameter and result types. -/
partial def STy.foldNames (f : α → String → α) (init : α) : STy → α
  | .name n => f init n
  | .app n ts => ts.foldl (STy.foldNames f) (f init n)
  | t => t.children.foldl (STy.foldNames f) init

/-- All written type names, in source order, retaining repetitions. -/
def STy.allNames (t : STy) : List String :=
  (t.foldNames (fun names n => n :: names) []).reverse

/-- Written type names in order of first occurrence. Each name is visited
    once; the set tracks duplicates without depending on its iteration order. -/
def STy.names (t : STy) : List String :=
  let (_, names) := t.foldNames (fun (seen, names) n =>
    if seen.contains n then (seen, names) else (seen.insert n, n :: names))
    (({} : Std.HashSet String), ([] : List String))
  names.reverse

/-- Whether a type mentions `n` as a plain type name, including inside
    function types. Application heads are excluded: `box(t)` mentions `t`. -/
partial def STy.mentions (t : STy) (n : String) : Bool := match t with
  | .name m => m == n
  | t => t.children.any (·.mentions n)

/-- Whether a type mentions any of `vs` as plain type names, with the same
    treatment of application heads as `mentions`. -/
partial def STy.mentionsAny (vs : List String) : STy → Bool
  | .name n => vs.contains n
  | t => t.children.any (STy.mentionsAny vs)

/-- A type parameter from a `where` clause (`t:type` or
    `t:subtype(comparable)`), or of a parametric struct `name(t:type) := struct`. -/
structure TParam where
  pos  : Pos
  name : String
  /-- The constraint as written: `type`, or the argument of `subtype(…)`. -/
  constraint : String
  /-- A non-comparable upper bound, retained as a type rather than a name:
      it may be qualified, parametric, or refer to another type parameter. -/
  upperBound : Option STy := none
  deriving Repr, Inhabited, BEq

/-- The interface every `<castable>` class and interface is below when a
    program writes a `castable_subtype(…)` bound (`UpperBounds.markCastable`):
    the bound's castability is a subtype relation, with checked evidence. -/
def castableClassMarker : String := "$castableClass"

/-- A metatype written as a type parameter's bound, `t:castable_subtype(c)`
    or `t:concrete_subtype(c)`: the upper bound `c`, and the metatype kept
    as its constraint. -/
def TParam.withMetatype (p : Pos) (name kind : String) (bound : STy) : TParam :=
  { pos := p, name, constraint := kind, upperBound := some bound }

/-- Keep the established type/comparable spelling while retaining the full
    source type of other bounds. Admission is the elaborator's responsibility. -/
def TParam.withUpperBound (p : Pos) (name : String) (bound : STy) : TParam :=
  match bound with
  | .name "comparable" => { pos := p, name, constraint := "comparable" }
  | .name n | .app n _ => { pos := p, name, constraint := n, upperBound := some bound }
  | _ => { pos := p, name, constraint := "bound", upperBound := some bound }

mutual
inductive SExpr where
  | int      : Pos → Int → SExpr
  | char     : Pos → Nat → SExpr
  /-- A `0u` char32 literal. -/
  | char32   : Pos → Nat → SExpr
  /-- A float literal (#127): its canonical bits. -/
  | float    : Pos → UInt64 → SExpr
  | str      : Pos → List SPart → SExpr
  | ident    : Pos → String → SExpr
  /-- `e(args)` (`bracket = false`) or `e[args]` (`bracket = true`). -/
  | app      : Pos → SExpr → List SExpr → Bool → SExpr
  | member   : Pos → SExpr → String → SExpr
  | query    : Pos → SExpr → SExpr
  | neg      : Pos → SExpr → SExpr
  | notE     : Pos → SExpr → SExpr
  /-- `+ - * /` -/
  | bin      : Pos → String → SExpr → SExpr → SExpr
  /-- A comparison chain `a op₁ b op₂ c …`. -/
  | cmp      : Pos → SExpr → List (String × SExpr) → SExpr
  | andE     : Pos → SExpr → SExpr → SExpr
  | orE      : Pos → SExpr → SExpr → SExpr
  | range    : Pos → SExpr → SExpr → SExpr
  | tuple    : Pos → List SExpr → SExpr
  /-- A block: a sequence that opens a scope; its value is the last element. -/
  | block    : Pos → List SExpr → SExpr
  | arrayLit : Pos → List SExpr → SExpr
  | optionLit : Pos → SExpr → SExpr
  | logicLit : Pos → SExpr → SExpr
  /-- `if (conds) then t else e` (conditions in order). -/
  | ite      : Pos → List SExpr → SExpr → Option SExpr → SExpr
  /-- `for (clauses) body`. -/
  | forE     : Pos → List SExpr → SExpr → SExpr
  /-- A generator clause `X : src` or `I -> X : src` (only inside `for`). -/
  | gen      : Pos → String → Option String → SExpr → SExpr
  | loop     : Pos → SExpr → SExpr
  | brk      : Pos → SExpr
  | ret      : Pos → Option SExpr → SExpr
  /-- `case (e): p => v …`; `none` is the pattern `_`. -/
  | caseE    : Pos → SExpr → List (Option SExpr × SExpr) → SExpr
  /-- `X:t = e`, `X := e` (`isVar = false`) or `var X:t = e`. -/
  | decl     : Pos → String → Option STy → Bool → SExpr → SExpr
  /-- `set lhs = e` or `set lhs op= e`. -/
  | set      : Pos → SExpr → Option String → SExpr → SExpr
  /-- `struct<specs>: fields`, and the type parameters of a parametric
      struct `name(t:type) := struct: …`. -/
  | structDef : Pos → List TParam → List String → List SField → SExpr
  /-- `enum:` (closed) or `enum<open>:`, which may gain values (Book of Verse ch. 9). -/
  | enumDef  : Pos → List String → (isOpen : Bool) → SExpr
  /-- `type{_X:t where c₁, c₂, …}`: a refinement type (Book of Verse ch. 11):
      the variable, the base type and the conditions. -/
  | refineDef : Pos → String → STy → List SExpr → SExpr
  /-- `t` in `name := t` or `name(u:type, …) := t`, at the top level or in a
      module: a type alias, a name for the type `t`, with its parameters (Book
      of Verse ch. 10, "Aliases"; ch. 11, "Type Aliases"). `Aliases.expand`
      writes `t` wherever the name is used, before elaboration. -/
  | typeAlias : Pos → List TParam → STy → SExpr
  /-- `Name{F := e, …}` or `name(t₁, …){F := e, …}`: a struct value. -/
  | construct : Pos → String → List STy → List SExpr → SExpr
  /-- `map{k => v, …}`. -/
  | mapLit   : Pos → List (SExpr × SExpr) → SExpr
  deriving Repr, Inhabited, BEq
inductive SPart where
  | text : String → SPart
  | code : SExpr → SPart
  deriving Repr, Inhabited, BEq
/-- A field of a class, an interface or a struct, `var<varSpecs>
    name<specs>:ty = default` (Book of Verse ch. 9, 10, 12). -/
structure SField where
  name : String
  ty : STy
  default : Option SExpr := none
  isVar : Bool := false
  /-- The specifiers on its name: its (read) access, `<override>`, `<final>`. -/
  specs : List String := []
  /-- The specifiers on its `var`: its write access (Book of Verse ch. 12,
      "Separating Read and Write Access"). -/
  varSpecs : List String := []
  deriving Repr, Inhabited, BEq
end

/-- A field that gives an inherited field a new default, `X<override>:t = e`. -/
def SField.isOverride (f : SField) : Bool := f.specs.contains "override"

def SExpr.pos : SExpr → Pos
  | .int p _ | .char p _ | .char32 p _ | .float p _ | .str p _ | .ident p _ | .app p _ _ _ | .member p _ _
  | .query p _ | .neg p _ | .notE p _ | .bin p _ _ _ | .cmp p _ _ | .andE p _ _
  | .orE p _ _ | .range p _ _ | .tuple p _ | .block p _ | .arrayLit p _
  | .optionLit p _ | .logicLit p _ | .ite p _ _ _ | .forE p _ _ | .gen p _ _ _
  | .loop p _ | .brk p | .ret p _ | .caseE p _ _ | .decl p _ _ _ _ | .set p _ _ _
  | .structDef p _ _ _ | .enumDef p _ _ | .refineDef p _ _ _ | .typeAlias p _ _ | .construct p _ _ _
  | .mapLit p _ => p

/-- Where an expression's text starts: a call's, an index's, a member's, a
    query's, a binary operation's and a comparison's at their first operand
    (the parser places them at the operator). -/
def SExpr.start : SExpr → Pos
  | .app _ f _ _ | .member _ f _ | .query _ f | .bin _ _ f _ | .cmp _ f _ => f.start
  | e => e.pos

/-- Immediate expression children, in source order, including call heads,
    construction field bindings and case patterns. Type definitions are
    leaves: analyses of their field defaults or refinement conditions must
    handle those explicitly. Constructions may evaluate their fields in a
    different order. -/
def SExpr.children : SExpr → List SExpr
  | .str _ ps => ps.filterMap fun | .code c => some c | _ => none
  | .app _ g as _ => g :: as
  | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x
  | .gen _ _ _ x | .decl _ _ _ _ x => [x]
  | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => [a, b]
  | .cmp _ a r => a :: r.map (·.2)
  | .tuple _ es | .block _ es | .arrayLit _ es | .construct _ _ _ es => es
  | .ite _ cs t e => cs ++ [t] ++ e.toList
  | .forE _ cs b => cs ++ [b]
  | .ret _ x => x.toList
  | .caseE _ sc arms => sc :: arms.flatMap fun (pt, v) => pt.toList ++ [v]
  | .mapLit _ kvs => kvs.flatMap fun (k, v) => [k, v]
  | .int .. | .char .. | .char32 .. | .float .. | .ident .. | .brk ..
  | .structDef .. | .enumDef .. | .refineDef .. | .typeAlias .. => []

/-- `e` with `f` applied to each of its immediate children, the ones
    `children` lists, in that order; everything else is kept. -/
def SExpr.mapChildrenM [Monad m] (f : SExpr → m SExpr) (e : SExpr) : m SExpr :=
  match e with
  | .str p ps => return .str p (← ps.mapM fun | .code c => do return .code (← f c) | t => pure t)
  | .app p g as b => return .app p (← f g) (← as.mapM f) b
  | .member p x m => return .member p (← f x) m
  | .query p x => return .query p (← f x)
  | .neg p x => return .neg p (← f x)
  | .notE p x => return .notE p (← f x)
  | .optionLit p x => return .optionLit p (← f x)
  | .logicLit p x => return .logicLit p (← f x)
  | .loop p x => return .loop p (← f x)
  | .gen p x i src => return .gen p x i (← f src)
  | .decl p n t v x => return .decl p n t v (← f x)
  | .bin p o a b => return .bin p o (← f a) (← f b)
  | .andE p a b => return .andE p (← f a) (← f b)
  | .orE p a b => return .orE p (← f a) (← f b)
  | .range p a b => return .range p (← f a) (← f b)
  | .set p l o r => return .set p (← f l) o (← f r)
  | .cmp p a r => return .cmp p (← f a) (← r.mapM fun (o, b) => do return (o, ← f b))
  | .tuple p es => return .tuple p (← es.mapM f)
  | .block p es => return .block p (← es.mapM f)
  | .arrayLit p es => return .arrayLit p (← es.mapM f)
  | .construct p n ts es => return .construct p n ts (← es.mapM f)
  | .ite p cs t u => return .ite p (← cs.mapM f) (← f t) (← u.mapM f)
  | .forE p cs b => return .forE p (← cs.mapM f) (← f b)
  | .ret p x => return .ret p (← x.mapM f)
  | .caseE p sc arms => return .caseE p (← f sc) (← arms.mapM fun (pt, v) => do return (← pt.mapM f, ← f v))
  | .mapLit p kvs => return .mapLit p (← kvs.mapM fun (k, v) => do return (← f k, ← f v))
  | .int .. | .char .. | .char32 .. | .float .. | .ident .. | .brk ..
  | .structDef .. | .enumDef .. | .refineDef .. | .typeAlias .. => return e

/-- The type an expression writes when its names are types' names: a name,
    `M.c`, or a name applied to such (`box(int)`; `c()` is `c`). A definition
    `X := e` at the top level or in a module whose `e` is one is a type alias
    when it is a type (`Aliases.writesType`). -/
partial def SExpr.asType? : SExpr → Option STy
  | .ident _ n => some (.name n)
  -- (`(M:)c`, as `M.c`)
  | .member _ (.ident _ "Self") m => match splitQual? m with
    | some (q, c) => if q == "local" || q.startsWith "/" then none else some (.name s!"{q}.{c}")
    | none => some (.name s!"Self.{m}")
  | .member _ x m =>
    if m.startsWith "(" then none else match x.asType? with
      | some (.name q) => some (.name s!"{q}.{m}")
      | _ => none
  | .app _ f args false => match f.asType? with
    | some (.name n) => if args.isEmpty then some (.name n) else (args.mapM SExpr.asType?).map (.app n)
    | _ => none
  | _ => none

/-- A definition's value that names a type, a scope or a module in a form
    openverse does not take yet (`union{…}`, `scoped{…}`, `import(…)`,
    `subtype(t)` and its kin): `X := e` with such an `e` is no data, so the
    rule that a module's data states its type (Book of Verse ch. 16) leaves it
    to the refusal of its form. -/
def SExpr.isTypeLikeForm : SExpr → Bool
  | .app _ (.ident _ h) _ _ | .construct _ h _ _ =>
    ["union", "scoped", "import", "subtype", "castable_subtype", "concrete_subtype", "type"].contains h
  | _ => false

/-- `e` with each identifier that `σ` names replaced by its expression
    (Verse has no shadowing, so a name means one thing in `e`). -/
partial def SExpr.substIdents (σ : List (String × SExpr)) (e : SExpr) : SExpr :=
  if σ.isEmpty then e else match e with
    | .ident _ n => (σ.lookup n).getD e
    | e => Id.run (e.mapChildrenM fun c => pure (c.substIdents σ))

/-- `e` with its children (`children`) replaced by `cs`, in order. -/
def SExpr.withChildren (e : SExpr) (cs : List SExpr) : SExpr :=
  let next (c : SExpr) : StateM (List SExpr) SExpr := modifyGet fun
    | c' :: rest => (c', rest)
    | [] => (c, [])
  (e.mapChildrenM next).run' cs

structure SParam where
  name : String
  ty   : STy
  /-- `?Name:t`: passed by name, as `?Name := e`. -/
  named : Bool := false
  /-- `?Name:t = e`: the value when the call omits it. -/
  default : Option SExpr := none
  /-- Compiler-only type-value argument. Its dummy value can initialize
      slots, but cannot establish an executable subtype relation. -/
  typeValue : Bool := false
  deriving Repr, Inhabited

/-- A top-level definition, each with the specifiers written on it. A
    function's are those of its name and its effects; its type parameters
    are those of its `where` clause (`F(X:t where t:type):t`), and a function
    with any is generic. -/
inductive STop where
  | fn    : Pos → String → List SParam → List TParam → List String → STy → SExpr → STop
  /-- `name<specs>:ty = value`, or `name<specs> := value`: a constant, or a
      struct, enum, refinement type or type alias, whose value says which.
      A module's marker `$module:A` has the module's specifiers. -/
  | const : Pos → String → (specs : List String) → Option STy → SExpr → STop
  /-- `name<nameSpecs>(t:type, …) := class<specs>(parents): fields and
      methods`, or `name := interface(parents): methods`: the specifiers of
      its name (its access) and of the class itself (its constructor's
      access, `<abstract>`, …). Each method is an `fn`; an abstract one (no
      body) has the effect `$abstract`. A field `Name<override>:t = e` gives
      an inherited field a new default. A parent is a type: `base(t)` for a
      parametric one (#39). -/
  | classDef : Pos → String → (nameSpecs : List String) → List TParam → (specs : List String) →
      (parents : List STy) → (isInterface : Bool) → (fields : List SField) → (methods : List STop) → STop
  deriving Repr, Inhabited

/-- The code of a definition, in the order it is written: a function's
    parameters' defaults, then its body; a constant's value, or a struct's
    fields' defaults; a class's or an interface's fields' defaults, then its
    methods' code. -/
partial def STop.code : STop → List SExpr
  | .fn _ _ ps _ _ _ body => ps.filterMap (·.default) ++ [body]
  | .const _ _ _ _ (.structDef _ _ _ fs) => fs.filterMap (·.default)
  | .const _ _ _ _ e => [e]
  | .classDef _ _ _ _ _ _ _ fs ms => fs.filterMap (·.default) ++ ms.flatMap STop.code

/-- The name of the constant that holds a default a function type writes
    (`?N:t = e`) after the definition that writes it, `$typeDefault:N`: the
    elaborator checks it at `t` and drops it (#503). -/
def typeDefaultPrefix : String := "$typeDefault:"

/-- The head of an attribute both called and given fields, `@a(…){…}`:
    `$attrCall(a(…), a{…})`, which `Attributes.apply` refuses. -/
def attrCallHead : String := "$attrCall"

/-- The name an attribute's expression starts with: `deprecated` of
    `deprecated{…}`, `a.bb` of `@a.bb`. -/
partial def SExpr.attrHead : SExpr → String
  | .ident _ n => n
  | .member _ x m => x.attrHead ++ "." ++ m
  | .app _ (.ident _ h) (c :: _) _ => if h == attrCallHead then c.attrHead else h
  | .app _ h _ _ => h.attrHead
  | .construct _ n _ _ => n
  | _ => ""

/-- The forms openverse parses and has no meaning for, each with why it
    refuses it. The parser writes each where it is: an expression as
    `refusedForm`, a pointer type `^t` as the type `$pointer(t)`
    (`pointerType`); `Attributes.apply` refuses the first, before anything
    else reads the program, so that a program the Book's tests only parse
    parses. -/
inductive Refused where
  /-- `(X) => e` (`parseRange`). -/
  | lambda
  /-- `e^` (`parsePostfix`). -/
  | pointerDeref
  /-- `^t`, refused where the definition that writes it is. -/
  | pointerType
  /-- `@h …` on an expression or a local definition (`parseExpr`). -/
  | exprAttribute (h : String)
  /-- `kw<sp>`, a specifier on a macro (`parsePrimary`). -/
  | macroSpecifier (sp kw : String)
  /-- `F(…):t` with no body (`parseTopsIn`). -/
  | declaredFunction (name : String)
  /-- `X:t` with no value (`parseTopsIn`). -/
  | declaredData (name : String)

def Refused.message : Refused → String
  | .lambda => "a lambda (…) => … is a nested function, which openverse does not have (#492; the Book's ch. 6 marks nested functions as an unreleased feature; docs/research/closure-design.md)"
  | .pointerDeref => "a pointer's dereference e^: the Book's chapters define no pointers, and openverse has none (Book of Verse tests, Pointers.versetest)"
  | .pointerType => "a pointer type ^t: the Book's chapters define no pointers, and openverse has none (Book of Verse tests, Pointers.versetest)"
  | .exprAttribute h => s!"@{h} is on an expression or a local definition: attributes go on the definitions of a module, a class, an interface, a struct or an enum, and on an expression only @ignore_unreachable (Book of Verse ch. 12)"
  | .macroSpecifier sp kw => s!"<{sp}> on {kw}: a macro takes no specifier (class and struct take their construction's effects) (Book of Verse tests, InvalidAttributeLocations.versetest: 3604)"
  | .declaredFunction n => s!"{n}(…) has no body: a declaration of a function defined elsewhere, which openverse has none of (native functions are not supported, #494)"
  | .declaredData n => s!"{n}:t has no value: a declaration of data defined elsewhere, which openverse has none of"

/-- A form openverse parses and refuses, `$refused(msg, e…)`: the refusal's
    message, then the parts the form was written with. -/
def refusedHead : String := "$refused"
def refusedForm (p : Pos) (r : Refused) (es : List SExpr) : SExpr :=
  .app p (.ident p refusedHead) (.str p [.text r.message] :: es) false

/-- The refusal `refusedForm` wrote, and where. -/
def SExpr.refused? : SExpr → Option (Pos × String)
  | .app p (.ident _ h) (.str _ [.text msg] :: _) _ => if h == refusedHead then some (p, msg) else none
  | _ => none

/-- The type `^t` (`Refused.pointerType`), `$pointer(t)`. -/
def pointerTypeHead : String := "$pointer"

/-- A marker of the `case` arms marked `@ignore_unreachable`: a constant
    whose value is a block of one name at each arm's place (`TyEnv.ignoredArms`). -/
def ignoredArmsMarker : String := "$uses:ignoredArms"

/-- The name of the record of an attribute (Book of Verse ch. 12,
    "Annotations and Metadata"), after the definition it is on: `$attr:L_C`,
    whose specifiers are where it is and what, and whose value is the
    attribute as written (`Attributes.apply` reads and removes it). -/
def attrPrefix : String := "$attr:"

/-- The name of a constant that holds an attribute's value, or a field's,
    `$attrCheck:N@a` for the attribute `@a`, of its type: the elaborator checks it there,
    as it does a function type's default, and drops it (`Attributes`). -/
def attrCheckPrefix : String := "$attrCheck:"

/-- Whether a definition holds a default a function type writes, or an
    attribute's value: checked at its type and dropped. -/
def STop.isTypeDefault : STop → Bool
  | .const _ n .. =>
    let last := (n.splitOn "::").getLast?.getD n
    last.startsWith typeDefaultPrefix || last.startsWith attrCheckPrefix
  | _ => false

/-- Whether a definition is a marker the parser writes beside a definition,
    not one: the marker of its qualifier (`qualMarker`) or of a `using`
    (`openMarker`), a default its function types write
    (`typeDefaultPrefix`), the record of an attribute (`attrPrefix`) and the
    check of its value (`attrCheckPrefix`). An attribute is on the first
    definition after its markers (`attachAttrs`, `Attributes.apply`). (It
    reads the last part of the name, after `::`.) -/
def STop.isBesideMarker : STop → Bool
  | .const _ n .. =>
    let last := (n.splitOn "::").getLast?.getD n
    last.startsWith qualPrefix || last.startsWith openPrefix || last.startsWith typeDefaultPrefix ||
      last.startsWith attrPrefix || last.startsWith attrCheckPrefix
  | _ => false

/-- Names no definition may take, at any scope (a module's, a class's, a
    function's parameters and locals). The Book of Verse says it of `_`
    (ch. 1: "The single underscore `_` is reserved and cannot be used as an
    identifier"); its tests reserve the others: the names of
    `Tests/NamesReservedForFuture.versetest` for the future (with `first`,
    `assert` and `let`, which openverse also reads as macros before `{` or
    `(`, and `using`, one of the parser's `keywords`, which no name can be
    anyway), and the built-in names `Self`, `subtype`, `castable_subtype`
    and `local` (`Self.versetest`, `Subtype.versetest`,
    `QualifiedIdentifier.versetest`), `true` and `false` (`Enum.versetest`
    refuses `(m:)true:=enum{a}`), `of` and `at`, which call a function
    (`F of X`, `F at X`; "The 'at' reserved word", `SemicolonsVsCommas.versetest:52`),
    and the effects' names, which are built-in
    classes (`Effects.versetest` refuses `(m:)suspends := class{}`); a
    qualifier does not lift it. -/
def reservedNames : List String :=
  ["_", "Self", "subtype", "castable_subtype", "local", "true", "false",
   "suspends", "decides", "varies", "reads", "writes", "allocates", "computes", "converges", "transacts",
   "abstracts", "as", "assert", "backslash", "bag", "char8", "char16", "collection", "contravariant",
   "covariant", "element", "embargo", "ensure", "fails", "find", "first", "float16", "float32", "float64",
   "float128", "fold", "function", "given", "guard", "implies", "instance", "int8", "int16", "int32",
   "int64", "interacts", "introspects", "invariant", "iterates", "known", "last", "let", "markup",
   "permutation", "nat", "nat8", "nat16", "nat32", "nat64", "over", "provided", "random", "repeat",
   "sequence", "string8", "string16", "string32", "subclass", "succeeds", "syntax", "throws", "trait",
   "truth", "try", "union", "using", "verify", "when", "while", "of", "at"]

/-- The prefix of an extension method's function's name (`extensionName`). -/
def extensionPrefix : String := "$ext:"

/-- The function an extension method `(R:t).M(…)` is (Book of Verse ch. 6,
    "Extension Methods"): `$ext:M`, whose first parameter is the receiver,
    a name no program can write, so that `M(X)` does not reach it and `M`
    names no value of it. A call `X.M(…)` that finds `$ext:M` in scope is
    the call `$ext:M(X, …)` (`resolveModules`). -/
def extensionName (m : String) : String := extensionPrefix ++ m

/-- The receiver of a bare call `M(…)` in a method that may be an extension
    method's call with `Self` (`resolveModules`): `$implicitSelf:F`, where
    `F` is what `M` names as written, the call's other reading. -/
def implicitSelfPrefix : String := "$implicitSelf:"

/-- The method name of an extension method's function, `$ext:M` at the top
    level, `A::B::$ext:M` in a module, `$ext:M$ov1` as an overload, a
    class's `c.$ext:M`: `M`. -/
def extensionMethod? (n : String) : Option String :=
  let last := ((n.splitOn "::").getLast?.getD n).splitOn "." |>.getLast?.getD n
  if last.startsWith extensionPrefix then
    some (((last.drop extensionPrefix.length).toString.splitOn "$ov").headD "")
  else none

/-- A function defined in a module or a class with the name of a function of
    a scope around it (`checkNoShadowing`, `checkSignatures`): where the inner one is, its
    signatures' name (`A::F`, `c.F`), the outer one's and where it is, and
    the qualifier that would say which one the inner one is. -/
structure ScopePair where
  pos : Pos
  inner : String
  outer : String
  outerPos : Pos
  qualifier : String
  deriving Inhabited

/-- Why a type's name is not one (`resolveTy`, and a type alias's names). -/
def unknownTypeMessage (n : String) : String :=
  s!"unknown type '{n}' (supported: int, logic, char, string, void, []t, ?t, tuple(…), and structs and enums)"

/-- The names a definition introduces as written, each where it is written:
    its own (the last part of a module member's `A::B::F`), its type
    parameters and parameters, a struct's or class's fields and methods, and
    the locals and generators of its bodies and defaults, each by the name a
    use may write bare (`X` for `(local:)X`). A qualified method `(c:)F`, a
    named argument `?X := e`, a construction's `F := e` and the compiler's
    `$` names are not definitions. -/
partial def SExpr.definedNames : SExpr → List (Pos × String)
  | .decl p n _ _ x => (if n.startsWith "?" then [] else [(p, bareName n)]) ++ x.definedNames
  | .gen p x k s => (p, bareName x) :: (k.toList.map (p, ·)) ++ s.definedNames
  | .construct _ _ _ fs => fs.flatMap fun
    | .decl _ _ _ _ x => x.definedNames
    | f => f.definedNames
  | .structDef p tps _ fs => tps.map (fun tp => (tp.pos, tp.name)) ++
      fs.flatMap fun f => (p, bareName f.name) :: (f.default.map SExpr.definedNames).getD []
  | .typeAlias _ tps _ => tps.map fun tp => (tp.pos, tp.name)
  | e => e.children.flatMap SExpr.definedNames

partial def STop.definedNames : STop → List (Pos × String)
  | .fn p n ps tps _ _ body =>
    (if n.startsWith "(" then [] else [(p, n)]) ++ tps.map (fun tp => (tp.pos, tp.name)) ++
      ps.flatMap (fun prm => (p, bareName prm.name) :: (prm.default.map SExpr.definedNames).getD []) ++ body.definedNames
  | .const p n _ _ body =>
    -- (a module's marker, `$module:A::B`, defines `B`)
    [(p, (moduleMarker? n).getD n)] ++ body.definedNames
  | .classDef p n _ tps _ _ _ fs ms =>
    (p, n) :: tps.map (fun tp => (tp.pos, tp.name)) ++
      fs.flatMap (fun f => (p, bareName f.name) :: (f.default.map SExpr.definedNames).getD []) ++
      ms.flatMap STop.definedNames

/-- Type aliases mentioned as bare names; applications keep declaration heads. -/
partial def STy.bareNames : STy → List String
  | .name n => [n]
  | t => t.children.flatMap STy.bareNames

/-- Substitute type names: a parent's type parameters by the type arguments
    a subclass gives it (#39). -/
partial def STy.substNames (σ : List (String × STy)) : STy → STy
  | .name n => (σ.lookup n).getD (.name n)
  -- The typed method prefix records this value's static result as an alias.
  -- Materialize it when a lifted body's type substitution carries that alias.
  | .app "$methodResult" [.name receiver] =>
    (σ.lookup receiver).getD (.app "$methodResult" [.name receiver])
  | t => Id.run (t.mapChildrenM fun c => pure (c.substNames σ))

/-- Rename binders and every peer-parameter reference in their upper bounds
    together. Renaming just the binder changes a dependent constraint. -/
def TParam.rename (tp : TParam) (names : List (String × String)) : TParam :=
  { tp with
    name := (names.lookup tp.name).getD tp.name
    upperBound := tp.upperBound.map (·.substNames (names.map fun (a, b) => (a, STy.name b))) }

/-- Inlined generic calls retain complete bounds in their private parameter
    protocol. Type/comparable parameters keep their established two-item form.
    The extra type packet is metadata, never an executable construction. -/
def TParam.marker (tp : TParam) (p : Pos) : SExpr :=
  .tuple p ([.ident p tp.name, .ident p tp.constraint] ++
    (tp.upperBound.toList.map fun bound => .construct p "$upperBound" [bound] []))

def TParam.ofMarker : SExpr → Except String TParam
  | .tuple p [.ident _ name, .ident _ constraint] => pure { pos := p, name, constraint }
  | .tuple p [.ident _ name, .ident _ constraint,
      .construct _ "$upperBound" [bound] []] =>
    pure { pos := p, name, constraint, upperBound := some bound }
  | e => .error s!"{e.pos.show}: internal: malformed generic constraint metadata"

end OpenVerse.Front
