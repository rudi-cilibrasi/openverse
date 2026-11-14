/-
  OpenVerse front end — modules (#112, Book of Verse ch. 16) and qualified
  names (Book of Verse ch. 9, 10 and 16; the rules are pinned in
  docs/research/qualified-names.md).

  The parser flattens `name := module:` into definitions of qualified names
  (`A::B::F`) and leaves markers: `$module:A::B` (with the module's
  specifiers), `$open:A::|M` (a `using{M}` written in module `A`) and
  `$qual:A::F|q` (a definition written `(q:)F`). This pass rewrites every reference to a

  module member to its qualified name, before elaboration, which then sees
  an ordinary flat program:

  - a bare name resolves from the definition's module outward (its own
    members, then the enclosing modules'), then among the public members of
    the modules opened with `using{…}` in scope (two of them giving the name
    is ambiguous), then as a global;
  - `M.F` and `A.B.F` (and the type `M.c`) name a member of the module `M`,
    found from the scope outward; it must be `<public>` unless the use is
    inside that module (the default is `<internal>`).

  Verse forbids shadowing, so a local may not have a name a resolution
  would rewrite (a member of the module or of an open one): that is refused
  here (elaboration's own check sees only the flat names).

  A qualifier `(q:)` names a scope, and every one written goes through one
  resolver (`Qual`, `Resolver.qualifier`): `q` is found as a name is (a
  module, then its submodules, or a class, interface, struct or enum),
  `local` is the locals of the code it is written in, `super` the
  implementation above a method, and the path `/Verse.org/Verse` openverse's
  built-in types. A qualified name is looked up in exactly that scope: `(M:)F`
  is `M`'s `F`, `(local:)X` a local, `(e:)v` the enum's value; a class's
  `(c:)M` is left for the elaboration of classes, which knows what each
  class introduces. A qualified definition's qualifier names where it is
  defined: its module, its class (or, for an override, what introduces the
  member), its enum or struct, or `local` for a local or a parameter, which
  may then take the name of a definition outside the code (the anti-shadowing
  rule's way out, Book ch. 16, "Local Qualifiers"); a bare use of that name
  is then ambiguous.
-/
import OpenVerse.Front.Access
import Std.Data.HashSet

namespace OpenVerse.Front

/-- A qualified name's parts: `A::B::F` is `[A, B, F]`. -/
def qualParts (n : String) : List String := n.splitOn "::"

def qualJoin (ps : List String) : String := "::".intercalate ps

partial def STy.mapNamesM (f : String → Except String String) : STy → Except String STy
  | .name n => return .name (← f n)
  | .app n ts => return .app (← f n) (← ts.mapM (·.mapNamesM f))
  | t => t.mapChildrenM (·.mapNamesM f)

def TParam.mapBoundNamesM (tp : TParam) (f : String → Except String String) : Except String TParam := do
  return { tp with upperBound := ← tp.upperBound.mapM (·.mapNamesM f) }

/-- The names an expression `A.B.C` is a chain of. -/
partial def SExpr.identPath : SExpr → Option (List String)
  | .ident _ n => some [n]
  | .member _ e m => (e.identPath).map (· ++ [m])
  | _ => none


/-- What a qualifier `(q:)` names (docs/research/qualified-names.md). -/
inductive Qual where
  /-- A module, by its parts: its members (`start`: how many of the parts
      the first name found reaches, which need no visibility check). -/
  | module (path : List String) (start : Nat)
  /-- A class, interface, struct or enum (or an alias of one), by its
      qualified name: its members, which the elaboration of classes knows. -/
  | type (name : String)
  /-- `(local:)`: the locals of the code it is written in. -/
  | locals
  /-- `(super:)`: the implementation above a method (the elaborator's). -/
  | super
  /-- `/Verse.org/Verse`: the built-in types. -/
  | builtins

/-- How the names of one scope resolve: values, binders (refused when they
    would shadow a member), type names, paths `A.B.F`, qualifiers, and the
    locals the code so far has defined. -/
structure Resolver where
  val  : Pos → String → Except String String
  bind : Pos → String → Except String Unit
  ty   : Pos → String → Except String String
  qual : Pos → List String → Except String (Option String)
  /-- The extension method a call `X.M(…)` names here, as a value's name
      resolves: `$ext:M`, qualified (Book of Verse ch. 6). -/
  ext  : Pos → String → Except String (Option String) := fun _ _ => pure none
  /-- In a method, the extension method a bare call `M(…)` may name with
      `Self` as its receiver, as `ext`. -/
  selfExt : Pos → String → Except String (Option String) := fun _ _ => pure none
  /-- What a qualifier names from this scope (a renamer that only maps
      names takes it as a type's). -/
  qualifier : Pos → String → Except String Qual := fun p q => do return .type (← ty p q)
  /-- The module a chain of names `A.B` is, from this scope, if it is one
      (with `Qual.module`'s `start`). -/
  modulePath : Pos → List String → Except String (Option (List String × Nat)) := fun _ _ => pure none
  /-- A module's member `F`, as a qualified name, checked to exist and to
      be visible here (after the module's first `start` parts). -/
  memberOf : Pos → List String → Nat → String → Except String String :=
    fun _ path _ f => pure (qualJoin (path ++ [f]))
  /-- Whether a bare name names a definition outside the code: a module's
      member, a top-level one, a member of the class whose code it is. -/
  outer : Pos → String → Bool := fun _ _ => false
  /-- The class whose method or default this is. -/
  selfClass : Option String := none
  /-- Whether a type's qualified name is an enum's. -/
  isEnum : String → Bool := fun _ => false
  /-- `c` declares the field `F` itself, and is the class `selfClass` or
      above it, where no other class or interface declares an `F`. -/
  selfField : String → String → Bool := fun _ _ => false
  /-- The members `selfClass` and the classes above it define qualified
      with their own class, `(c:)x`, each with that class. -/
  selfQualified : List (String × String) := []
  /-- Whether a bare name names a definition outside every class: a
      module's member or a top-level one. -/
  global : Pos → String → Bool := fun _ _ => false
  /-- The type parameters in scope. -/
  tparams : List String := []
  /-- The locals in scope, innermost first: each name as a bare use writes
      it, and whether `(local:)` defined it. -/
  locals : List (String × Bool) := []

/-- A method name: `(i:)M`'s interface `i` (or `M.i`) resolved as a type. -/
def Resolver.method (r : Resolver) (p : Pos) (m : String) : Except String String := do
  if let some (q, x) := splitQual? m then return s!"({← r.ty p q}:){x}"
  return m

/-- A binder of the code: its name as the elaboration sees it (`(local:)X`
    for `(local:)X`, which no other name spells, so it shadows nothing), and
    the resolver of the code after it. `(local:)X` may take the name of a
    definition outside the code, not of another local in scope nor of a type
    parameter (Book of Verse ch. 16, "Local Qualifiers"; tests,
    `QualifiedIdentifier.versetest`); a plain one may take none
    (`Resolver.bind`). -/
def Resolver.binder (r : Resolver) (p : Pos) (n : String) : Except String (String × Resolver) := do
  match splitQual? n with
  | some (q, x) =>
    match ← r.qualifier p q with
    | .locals =>
      if r.locals.any (·.1 == x) then
        throw s!"{p.show}: '{x}' is already defined here, by a local of the enclosing code: (local:) does not let a local be defined again (Book of Verse ch. 16, \"Local Qualifiers\")"
      if r.tparams.contains x then
        throw s!"{p.show}: '{x}' is already defined, as a type parameter: (local:) qualifies a local only"
      return (s!"(local:){x}", { r with locals := (x, true) :: r.locals })
    | _ =>
      throw s!"{p.show}: ({q}:){x}: a local is defined in the code it is written in, so its qualifier is (local:); a qualifier names where the definition is"
  | none =>
    if n.startsWith "?" then return (n, r)
    r.bind p n
    if r.locals.any (· == (n, true)) then
      throw s!"{p.show}: '{n}' is already defined here, as (local:){n}"
    return (n, { r with locals := (n, false) :: r.locals })

mutual
/-- Rewrite the names of an expression (see `Resolver`). -/
partial def SExpr.mapNamesM (r : Resolver) : SExpr → Except String SExpr := fun e =>
  let go := SExpr.mapNamesM r
  let goT (p : Pos) := STy.mapNamesM (r.ty p)
  -- (a construction's `Field := v`: a field's name, not a binder)
  let goField : SExpr → Except String SExpr := fun
    | .decl p n ty v x => do return .decl p n (← ty.mapM (goT p)) v (← go x)
    | a => go a
  match e with
  | .ident p n => do
    -- (`D<constructor>(…)`, a delegation: `D` or `M.D`)
    if let some d := delegationHead? n then
      if d.contains '.' then
        match ← r.qual p (d.splitOn ".") with
        | some qd => return .ident p (delegationHead qd)
        | none => throw s!"{p.show}: unknown constructor {d}"
      return .ident p (delegationHead (← r.val p d))
    -- (a local `(local:)X`, bare: it, unless a definition outside the code
    -- is named so too, Book of Verse tests, FN41.00-FirstAdded.versetest)
    if r.locals.lookup n == some true then
      if r.outer p n then
        throw s!"{p.show}: '{n}' is ambiguous here: the local (local:){n} and a definition outside this code are both named so; write (local:){n} for the local (Book of Verse ch. 16, \"Local Qualifiers\")"
      return .ident p s!"(local:){n}"
    -- (a member `(c:)x` of the class whose code this is, bare, where a
    -- definition outside the class is named so too: Book of Verse ch. 10,
    -- "Methods with Same Name"; tests, ModuleDefinitions.versetest)
    if r.locals.lookup n == none then
      if let some c := r.selfQualified.lookup n then
        if r.global p n then
          throw s!"{p.show}: '{n}' is ambiguous here: the member ({c}:){n} and a definition outside the class are both named so; qualify it, ({c}:){n} for the member"
    return .ident p (← r.val p n)
  | .member p x m => do
    if let some (q, f) := splitQual? m then
      if let .ident _ "Self" := x then
        -- `(q:)f`, parsed as `Self.(q:)f`: `f` in the scope `q` names
        match ← r.qualifier p q with
        | .module path start => return .ident p (← r.memberOf p path start f)
        | .locals =>
          match r.locals.lookup f with
          | some true => return .ident p s!"(local:){f}"
          | some false => return .ident p f
          | none => throw s!"{p.show}: (local:){f}: there is no local {f} here (a parameter, or a definition before this use in the enclosing code)"
        | .builtins =>
          if builtinTypeNames.contains f then return .ident p f
          throw s!"{p.show}: ({q}:){f}: openverse stands in for {q} with its built-in types ({", ".intercalate builtinTypeNames}) only"
        | .super => return .member p x m
        | .type c =>
          -- (an enum's value, `e.v`; a field of `Self` its class, or one
          -- above it, declares)
          if r.isEnum c then return .member p (.ident p c) f
          if r.selfField c f then return .member p x f
          return .member p x s!"({c}:){f}"
      -- `X.(q:)f`: a member of `X` as `q` has it; `M.(M:)F` is `M.F`
      -- (Book of Verse ch. 16: `MyModule.(MyModule:)Last(X)`)
      if let some comps := x.identPath then
        if let some (path, start) ← r.modulePath p comps then
          match ← r.qualifier p q with
          | .module qp _ =>
            if qp != path then
              throw s!"{p.show}: {".".intercalate comps}.({q}:){f}: {q} is not the module {".".intercalate comps}"
            return .ident p (← r.memberOf p path start f)
          | _ => throw s!"{p.show}: {".".intercalate comps}.({q}:){f}: a module's member is qualified with the module"
      match ← r.qualifier p q with
      | .type c => return .member p (← go x) s!"({c}:){f}"
      | .super => return .member p (← go x) m
      | .locals => throw s!"{p.show}: X.(local:){f}: (local:) qualifies a local, not a member of a value"
      | _ => throw s!"{p.show}: X.({q}:){f}: a member of a value is qualified with a class or an interface"
    if let some comps := x.identPath then
      if let some qn ← r.qual p (comps ++ [m]) then return .ident p qn
    return .member p (← go x) m
  -- `X.(M:)F(…)`, `M` a module: `M`'s extension method `F`, `$ext:F(X, …)`
  -- (a qualifier selects among the extension methods in scope as among
  -- other names)
  | .app p (.member mp x m) args b => do
    if let some (q, f) := splitQual? m then
      if !(x matches .ident _ "Self") then
        let ofModule ← match x.identPath with
          | some comps => do pure (← r.modulePath mp comps).isSome
          | none => pure false
        if !ofModule then
          if let .module path start ← r.qualifier mp q then
            let fn ← r.memberOf mp path start (extensionName f)
            return .app p (.ident mp fn) ((← go x) :: (← args.mapM go)) b
    -- `X.M(…)` whose name an extension method in scope has: the call
    -- `$ext:M(X, …)` of it (Book of Verse ch. 6, "Extension Methods"), which
    -- takes `X`'s own member `M` instead where `X`'s type has one (`elabApp`)
    let f ← go (.member mp x m)
    let args ← args.mapM go
    if let .member _ x _ := f then
      if !(x matches .ident _ "(super:)") then
        if let some q ← r.ext mp m then return .app p (.ident mp q) (x :: args) b
    return .app p f args b
  -- in a method, a bare call `M(…)` whose name an extension method in scope
  -- has: the call `$ext:M(Self, …)` of it, or `M(…)` as written, whichever
  -- the call fits (`elabApp`; Book of Verse tests, `SOL-3515`)
  | .app p f@(.ident ip n) args b => do
    let f ← go f
    let args ← args.mapM go
    if let .ident _ n' := f then
      if !n.startsWith "$" then
        if let some q ← r.selfExt ip n then
          return .app p (.ident ip q) (.ident ip (implicitSelfPrefix ++ n') :: args) b
    return .app p f args b
  | .gen .. | .decl .. => do return (← SExpr.mapItemM r e).1
  | .block p items => return .block p (← SExpr.mapSeqM r items).1
  -- (an `if`'s conditions and a `for`'s clauses are a sequence whose
  -- definitions its branch or body sees)
  | .ite p cs t u => do
    let (cs, r') ← SExpr.mapSeqM r cs
    return .ite p cs (← t.mapNamesM r') (← u.mapM go)
  | .forE p cs b => do
    let (cs, r') ← SExpr.mapSeqM r cs
    return .forE p cs (← b.mapNamesM r')
  -- (a struct's field types and defaults, which `children` leaves out)
  | .structDef p tps specs fs =>
    let own := tps.map (·.name)
    let inner : Resolver := { r with ty := fun q n => if own.contains n then pure n else r.ty q n }
    return .structDef p (← tps.mapM (·.mapBoundNamesM (inner.ty p))) specs
      (← fs.mapM fun f => do
        return { f with ty := ← f.ty.mapNamesM (inner.ty p), default := ← f.default.mapM (·.mapNamesM inner) })
  -- (a type alias's type, its own parameters excepted)
  | .typeAlias p tps t =>
    let own := tps.map (·.name)
    let inner : Resolver := { r with ty := fun q n => if own.contains n then pure n else r.ty q n }
    return .typeAlias p (← tps.mapM (·.mapBoundNamesM (inner.ty p))) (← t.mapNamesM (inner.ty p))
  | .enumDef .. | .refineDef .. => return e
  | .construct p n ts fs => return .construct p (← r.ty p n) (← ts.mapM (goT p)) (← fs.mapM goField)
  | e => e.mapChildrenM go

/-- A sequence's items (a block's, an `if`'s conditions, a `for`'s clauses),
    each seeing the locals those before it define, and the resolver after
    them. -/
partial def SExpr.mapSeqM (r : Resolver) (es : List SExpr) : Except String (List SExpr × Resolver) := do
  let mut r := r
  let mut out : Array SExpr := #[]
  for e in es do
    let (e', r') ← SExpr.mapItemM r e
    out := out.push e'
    r := r'
  return (out.toList, r)

/-- An item of a sequence, and the resolver after it: a definition's local
    is seen by what follows it, not by its own value. -/
partial def SExpr.mapItemM (r : Resolver) : SExpr → Except String (SExpr × Resolver)
  | .decl p n ty v x => do
    let (n', r') ← r.binder p n
    return (.decl p n' (← ty.mapM (STy.mapNamesM (r.ty p))) v (← x.mapNamesM r), r')
  | .gen p x k s => do
    let (x', r1) ← r.binder p x
    let (k', r2) ← match k with
      | some k => do let (k', r2) ← r1.binder p k; pure (some k', r2)
      | none => pure (none, r1)
    return (.gen p x' k' (← s.mapNamesM r), r2)
  | e => do return (← e.mapNamesM r, r)
end

/-- What the renaming knows of a class's names. -/
structure ClassNames where
  /-- Its parents, by their qualified names. -/
  parents : List String
  /-- Its own members, unqualified: the anti-shadowing check reads them. -/
  own : List String
  /-- All its members, as a bare use names them. -/
  all : List String
  /-- The fields it declares itself (not those it overrides). -/
  declared : List String
  /-- The members it defines qualified with its own name, `(c:)x`. -/
  ownQualified : List String
  /-- Its extension methods, `$ext:M`, which its methods' calls find. -/
  exts : List String

/-- The specifiers a definition writes, each with the place it is written
    at: its name's, its type's own, its fields' and their `var`s', its
    methods'. -/
def STop.specPlaces : STop → List (EffectPolicy.Place × List String)
  | .fn _ _ _ _ specs .. => [(.function, specs)]
  | .const _ _ specs _ (.structDef _ _ sspecs fs) =>
    [(.definition, specs), (.structType, sspecs)] ++ fs.flatMap fun f => [(.structField, f.specs), (.var, f.varSpecs)]
  | .const _ _ specs .. => [(.definition, specs)]
  | .classDef _ _ ns _ specs _ isI fs ms =>
    [(.definition, ns), (if isI then .interfaceType else .classType, specs)] ++
      fs.flatMap (fun f => [(.field, f.specs), (.var, f.varSpecs)]) ++
      ms.filterMap fun | .fn _ _ _ _ s .. => some (.method, s) | _ => none

/-- A parsed program with every access level written out (Book of Verse
    ch. 12, "Scoped"): the modules of `<scoped{A, B.C}>` found from where it
    is written, a name `<S>` or `<M.S>` of an access level `S := scoped{…}`
    replaced by the level it names, both as `scoped{A::B|C}`
    (`Access.scopedLevel`); the access levels' definitions, which are no
    values, removed. A scope names modules of the program: a package's path
    is refused, as is a specifier that is no keyword openverse knows and
    names no access level (`<intrinsic>`). Each place then has at most one
    access level where one may go (`EffectPolicy.checkPlace`). -/
def resolveSpecifiers (tops : List STop) : Except String (List STop) := do
  let scopeDef? : STop → Option (Pos × String × List String × List String) := fun
    | .const p n specs none (.app _ (.ident _ h) refs false) =>
      if h != scopeHead then none else
      some (p, n, specs, refs.filterMap fun | .ident _ r => some r | _ => none)
    | _ => none
  let scopes := tops.filterMap scopeDef?
  let needed := !scopes.isEmpty || tops.any fun t => t.specPlaces.any fun (_, specs) =>
    specs.any fun sp => sp.startsWith "scoped{" || !(sp.startsWith "$" || EffectPolicy.known sp)
  if !needed then return tops
  let scopeOf (n : String) : List String := (qualParts n).dropLast
  let modules : Std.HashSet String := Std.HashSet.ofList (tops.filterMap fun
    | .const _ n .. => moduleMarker? n
    | _ => none)
  -- a module `r` (`A.B`) from scope `sc`: its first name found from `sc`
  -- outward, as a module's name is
  let moduleAt (sc : List String) (p : Pos) (r : String) : Except String (List String) := do
    if r.startsWith "/" then
      throw s!"{p.show}: scoped\{{r}}: {r} is a package's path, and openverse has no packages: a scope names modules of the program (Book of Verse ch. 12)"
    let comps := r.splitOn "."
    for k in (List.range (sc.length + 1)).reverse do
      let base := sc.take k ++ [comps.headD r]
      if modules.contains (qualJoin base) then
        let path := base ++ comps.drop 1
        if modules.contains (qualJoin path) then return path
        break
    throw s!"{p.show}: scoped\{{r}}: unknown module {r}: a scope names modules of the program (Book of Verse ch. 12)"
  let canonical (sc : List String) (p : Pos) (sp : String) : Except String String := do
    let refs := ((((sp.drop "scoped{".length).dropEnd 1).toString).splitOn ",").filter (· != "")
    return Access.scopedLevel (← refs.mapM (moduleAt sc p))
  -- each access level a module defines: what it grants, and its own access
  let mut levels : Std.HashMap String (String × Option String) := {}
  for (p, n, specs, refs) in scopes do
    let own ← specs.mapM fun sp => if sp.startsWith "scoped{" then canonical (scopeOf n) p sp else pure sp
    levels := levels.insert n (Access.scopedLevel (← refs.mapM (moduleAt (scopeOf n) p)), Access.levelOf own)
  -- the access level `r` (`S`, `M.S`) names from scope `sc`: from `sc`
  -- outward, then among those of the modules opened there that allow `sc`
  let opens : List (List String × String) := tops.filterMap fun
    | .const _ n .. => (openMarker? n).map fun (s, m) => ((qualParts s).filter (· != ""), m)
    | _ => none
  let admits (n : String) (sc : List String) : Bool :=
    ((Access.audience (levels[n]?.bind (·.2)) (scopeOf n)).admits (fun _ _ => false) { module := sc })
  let levelAt (sc : List String) (p : Pos) (r : String) : Except String (Option String) := do
    let comps := r.splitOn "."
    if comps.length > 1 then
      let path ← moduleAt sc p (".".intercalate comps.dropLast)
      let n := qualJoin (path ++ [comps.getLastD r])
      return if levels.contains n && admits n sc then some n else none
    for k in (List.range (sc.length + 1)).reverse do
      let n := qualJoin (sc.take k ++ [r])
      if levels.contains n then return some n
    for (osc, m) in opens do
      if Access.isPrefix osc sc then
        if let .ok path := moduleAt osc p (m.replace "::" ".") then
          let n := qualJoin (path ++ [r])
          if levels.contains n && admits n sc then return some n
    return none
  let resolve (sc : List String) (p : Pos) (place : EffectPolicy.Place) (specs : List String) :
      Except String (List String) := do
    let out ← specs.mapM fun sp => do
      if sp.startsWith "scoped{" then return ← canonical sc p sp
      if sp.startsWith "$" || EffectPolicy.known sp then return sp
      match ← levelAt sc p sp with
      | some n => return (levels[n]?.map (·.1)).getD sp
      | none =>
        throw s!"{p.show}: unknown or unsupported specifier <{sp}> on {place.what}: no specifier openverse knows, nor an access level scoped\{…} that the program defines (#494)"
    EffectPolicy.checkPlace p place out
    return out
  let resolveFields (sc : List String) (p : Pos) (place : EffectPolicy.Place) (fs : List SField) :
      Except String (List SField) :=
    fs.mapM fun f => do
      let f := { f with specs := ← resolve sc p place f.specs, varSpecs := ← resolve sc p .var f.varSpecs }
      EffectPolicy.checkOverrideAccess p f.name f.specs f.varSpecs
      return f
  tops.filterMapM fun t => do
    if (scopeDef? t).isSome then return none
    match t with
    | .fn p n ps tps specs ret body => return some (.fn p n ps tps (← resolve (scopeOf n) p .function specs) ret body)
    | .const p n specs ty body =>
      let sc := scopeOf ((moduleMarker? n).getD n)
      let body ← match body with
        | .structDef bp tps sspecs fs => do
          pure (SExpr.structDef bp tps (← resolve sc p .structType sspecs) (← resolveFields sc p .structField fs))
        | b => pure b
      return some (.const p n (← resolve sc p .definition specs) ty body)
    | .classDef p c ns tps specs parents isI fs ms =>
      let sc := scopeOf c
      let ms ← ms.mapM fun
        | .fn mp mn mps mtps mspecs mret mbody => do
          let mspecs ← resolve sc mp .method mspecs
          EffectPolicy.checkOverrideAccess mp mn mspecs []
          return STop.fn mp mn mps mtps mspecs mret mbody
        | m => pure m
      return some (.classDef p c (← resolve sc p .definition ns) tps
        (← resolve sc p (if isI then .interfaceType else .classType) specs) parents isI (← resolveFields sc p .field fs) ms)

/-- Resolve the modules and the qualified names of a parsed program (see
    the file's header). -/

def resolveModules (tops : List STop) : Except String (List STop) := do
  let markers {α : Type} (marked? : String → Option α) : List (Pos × α) := tops.filterMap fun
    | .const p n _ _ _ => (marked? n).map (p, ·)
    | _ => none
  let isMarker (n : String) := n.startsWith modulePrefix || n.startsWith openPrefix ||
    n.startsWith qualPrefix || n == qualifierMarker
  let real := tops.filter fun
    | .const _ n _ _ _ => !isMarker n
    | _ => true
  let modules := (markers moduleMarker?).map (·.2)
  -- (extension methods, which calls `X.M(…)` find: Book of Verse ch. 6)
  let isExt (n : String) : Bool := (extensionMethod? n).isSome
  let hasExt := real.any fun
    | .fn _ n .. => isExt n
    | .classDef _ _ _ _ _ _ _ _ ms => ms.any fun | .fn _ n .. => isExt n | _ => false
    | _ => false
  if modules.isEmpty && (markers openMarker?).isEmpty && (markers (afterPrefix? qualifierMarker)).isEmpty && !hasExt then
    return real
  -- (the access levels written on the definitions and modules, Book of
  -- Verse ch. 12: `Access`)
  let levels := Access.Levels.of tops
  let defs : List String := real.map fun
    | .fn _ n .. | .const _ n .. | .classDef _ n .. => n
  let defsS : Std.HashSet String := Std.HashSet.ofList defs
  let modsS : Std.HashSet String := Std.HashSet.ofList modules
  let shown (n : String) : String := ".".intercalate (qualParts n)
  let shownP (ps : List String) : String := ".".intercalate ps
  -- (a module may be defined in parts, which are one module; their access
  -- levels agree: the Book of Verse's tests, `Modules/PartialModuleDefinitions.versetest`
  -- 157-176, 3623)
  let mut seenM : Std.HashMap String (Option String) := {}
  for t in tops do
    let .const p n specs _ _ := t | continue
    let some m := moduleMarker? n | continue
    if defsS.contains m then throw s!"{p.show}: {shown m} is defined twice (a module and a definition)"
    let level := Access.levelOf specs
    if let some first := seenM[m]? then
      if first != level then
        let say (l : Option String) : String := match l with | some l => s!"<{l}>" | none => "internal"
        throw s!"{p.show}: the parts of module {shown m} have different access levels, {say first} and {say level}: every part of a module has the same (Book of Verse tests, PartialModuleDefinitions.versetest)"
    seenM := seenM.insert m level
  -- (one name's overloads share their access)
  let fnLevels : Std.HashMap String (List (Option String)) := real.foldl (fun m t => match t with
    | .fn _ n _ _ specs .. => m.insert n (Access.levelOf specs :: m.getD n [])
    | _ => m) {}
  for t in real do
    if let .fn p n _ _ specs .. := t then
      let ls := fnLevels.getD n []
      if n.contains ':' && ls.any (· != Access.levelOf specs) then
        if Access.levelOf specs == some "public" then
          throw s!"{p.show}: the overloads of {shown n} must all be <public> or all internal"
        if !ls.contains (some "public") then
          throw s!"{p.show}: the overloads of {shown n} must all have one access level"

  let inside (sc m : List String) : Bool := m.length ≤ sc.length && sc.take m.length == m
  -- whether code in module `sc` may name the definition or module `lvl`
  -- (whose own module is `lvl.dropLast`): its access level admits it
  let admitsAt (sc lvl : List String) : Bool :=
    (Access.audience levels[qualJoin lvl]? lvl.dropLast).admits (fun _ _ => false) { module := sc }
  -- the definition or module a name gives from scope `sc`, the innermost
  -- (`true`: a module)
  let lookup (sc : List String) (n : String) : Option (Bool × List String) := Id.run do
    for k in (List.range (sc.length + 1)).reverse do
      let cand := sc.take k ++ [n]
      if defsS.contains (qualJoin cand) then return some (false, cand)
      if modsS.contains (qualJoin cand) then return some (true, cand)
    return none
  -- each level of `path` after its first `start` parts, used from `sc`, is
  -- visible: public, or used inside its owner
  let checkVis (sc : List String) (p : Pos) (path : List String) (start : Nat) : Except String Unit := do
    for k in [start + 1 : path.length + 1] do
      let lvl := path.take k
      let owner := lvl.dropLast
      if !admitsAt sc lvl then
        match Access.audience levels[qualJoin lvl]? owner with
        | .within _ => throw s!"{p.show}: {shownP lvl} is internal to {shownP owner}: mark it <public> to use it outside"
        | a => throw s!"{p.show}: {a.refusal (shownP lvl)}"
  -- the modules opened, each with the scope it is open in
  let mut opens : List (List String × List String) := []
  for (p, sc0, path) in markers openMarker? do
    let sc := (qualParts sc0).filter (· != "")
    let comps := qualParts path
    let head := comps.headD ""
    -- (`using{(A:)B}`: the module `B` of the module `A`, as `using{A.B}`;
    -- a module's using is a module's, Book of Verse tests,
    -- QualifiedIdentifier.versetest)
    let (head, comps) ← match splitQual? head with
      | some (q, m) =>
        if q == "local" then
          throw s!"{p.show}: using\{(local:){m}}: (local:) qualifies a function's locals, and a using names a module"
        if q.startsWith "/" then
          throw s!"{p.show}: using\{({q}:){m}}: openverse has no module at the path {q}"
        let qs := q.splitOn "."
        pure (qs.headD q, qs.drop 1 ++ m :: comps.drop 1)
      | none => pure (head, comps.drop 1)
    -- (the head: a module in scope, or a public submodule of a module
    -- opened before, in scope)
    let viaOpen : Option (List String) := opens.findSome? fun (osc, m) =>
      if inside sc osc && modsS.contains (qualJoin (m ++ [head])) &&
          admitsAt sc (m ++ [head]) then some (m ++ [head]) else none
    let base ← match lookup sc head, viaOpen with
      | some (true, b), _ => pure b
      | none, some b => pure b
      | _, _ => throw s!"{p.show}: unknown module {shownP (head :: comps)}"
    let mut cur := base
    for c in comps do
      if !modsS.contains (qualJoin (cur ++ [c])) then throw s!"{p.show}: unknown module {shownP (head :: comps)}"
      cur := cur ++ [c]
    checkVis sc p cur base.length
    opens := opens ++ [(sc, cur)]
  -- the definition or module a name gives from scope `sc`: at each level,
  -- innermost first, the level's own definitions, then the members of the
  -- modules opened there (two of them giving it: ambiguous) (`true`: a module)
  let find (sc : List String) (p : Pos) (n : String) : Except String (Option (Bool × List String)) := do
    for k in (List.range (sc.length + 1)).reverse do
      let pre := sc.take k
      let cand := pre ++ [n]
      if defsS.contains (qualJoin cand) then return some (false, cand)
      if modsS.contains (qualJoin cand) then return some (true, cand)
      let here : List (Bool × List String) := ((opens.filter (·.1 == pre)).filterMap fun (_, m) =>
        let c := m ++ [n]
        let q := qualJoin c
        if !admitsAt sc c then none

        else if defsS.contains q then some (false, c)
        else if modsS.contains q then some (true, c)
        else none).eraseDups
      match here with
      | [x] => return some x
      | (_, a) :: (_, b) :: _ => throw s!"{p.show}: '{n}' is ambiguous: both {shownP a} and {shownP b} are open"
      | [] => pure ()
    return none
  let resolve (what : String) (sc : List String) (p : Pos) (n : String) : Except String String := do
    match ← find sc p n with
    | some (true, cand) => throw s!"{p.show}: {shownP cand} is a module, not a {what}"
    | some (false, cand) => return qualJoin cand
    | none => return n
  -- a binder: refused if it would shadow a module, or a member of a module
  -- (the top level's names are the elaborator's to check)
  let bind (sc : List String) (p : Pos) (n : String) : Except String Unit := do
    let hit : Option (List String) := match ← find sc p n with
      | some (true, cand) => some cand
      | some (false, cand) => if cand.length > 1 then some cand else none
      | none => none
    if let some cand := hit then
      throw s!"{p.show}: '{n}' is already defined (as {shownP cand}); Verse does not allow shadowing"
  -- a module's member `last`, from scope `sc`: it exists, and each level
  -- after the first `start` parts is visible
  let memberOf (sc : List String) (p : Pos) (path : List String) (start : Nat) (last : String) :
      Except String String := do
    let qn := path ++ [last]
    if !defsS.contains (qualJoin qn) then
      if modsS.contains (qualJoin qn) then throw s!"{p.show}: module {shownP qn} is not a value"
      throw s!"{p.show}: module {shownP path} has no member {last}"
    checkVis sc p qn start
    return qualJoin qn
  -- the module a chain of names is, from scope `sc` (and how many of its
  -- parts the first name found), if it is one
  let modulePath (sc : List String) (p : Pos) (comps : List String) : Except String (Option (List String × Nat)) := do
    let some (true, base) ← find sc p (comps.headD "") | return none
    let mut path := base
    for c in comps.drop 1 do
      if !modsS.contains (qualJoin (path ++ [c])) then return none
      path := path ++ [c]
    return some (path, base.length)
  -- a path (module parts, then a member), from scope `sc`
  let qual (sc : List String) (p : Pos) (comps : List String) : Except String (Option String) := do
    match comps with
    | _ :: _ :: _ =>
      -- (a value's name: `X.F` is its field; `M.v.F`: the field `F` of the
      -- member `M.v`, resolved as a prefix)
      let some (path, start) ← modulePath sc p comps.dropLast | return none
      return some (← memberOf sc p path start comps.getLast!)
    | _ => return none
  let tyName (sc excl : List String) (p : Pos) (n : String) : Except String String := do
    if excl.contains n then return n
    if n.contains '.' then
      match ← qual sc p (n.splitOn ".") with
      | some qn => return qn
      | none => throw s!"{p.show}: unknown type '{n}'"
    resolve "type" sc p n
  -- what a qualifier names from scope `sc`: `local`, `super`, the path of
  -- the built-ins, else a module (then its submodules) or a type, found as
  -- a name is
  let qualifier (sc excl : List String) (p : Pos) (q : String) : Except String Qual := do
    if q == "local" then return .locals
    if q == "super" then return .super
    if q.startsWith "/" then
      if q == "/Verse.org/Verse" then return .builtins
      throw s!"{p.show}: ({q}:): openverse has no module at the path {q}: it stands in for /Verse.org/Verse with its built-in types, and for no other package (a module of the program is named by its name, M or A.B, not by a path)"
    if let some (path, start) ← modulePath sc p (q.splitOn ".") then return .module path start
    return .type (← tyName sc excl p q)
  -- a type written with a path qualifier, `(/Verse.org/Verse:)int`
  let tyNameQ (sc excl : List String) (p : Pos) (n : String) : Except String String := do
    if let some (q, c) := splitQual? n then
      match ← qualifier sc excl p q with
      | .builtins =>
        if builtinTypeNames.contains c then return c
        throw s!"{p.show}: ({q}:){c}: openverse stands in for {q} with its built-in types ({", ".intercalate builtinTypeNames}) only"
      | _ => throw s!"{p.show}: ({q}:){c}: a type is qualified with the module that defines it"
    tyName sc excl p n
  let scopeOf (n : String) : List String := (qualParts n).dropLast
  -- the extension method `X.M(…)` names from scope `sc`, `$ext:M` found as
  -- a value's name is (none: `X`'s member `M`)
  let extAt (sc : List String) (p : Pos) (m : String) : Except String (Option String) := do
    if !hasExt || m.startsWith "(" || m.startsWith "$" then return none
    match ← find sc p (extensionName m) with
    | some (false, cand) => return some (qualJoin cand)
    | _ => return none
  -- the type a qualifier names through aliases (`a := c`, which the type
  -- aliases' pass writes out later: a qualifier may name a class through
  -- one, docs/research/type-aliases.md), for the comparisons below
  let aliasOf : List (String × String) := real.filterMap fun
    | .const p n _ none body =>
      let named : Option String := match body with
        | .typeAlias _ [] (.name x) => some x
        | .typeAlias .. => none
        | e => match e.asType? with
          | some (.name x) => some x
          | _ => none
      named.bind fun x => match tyName (scopeOf n) [] p x with
        | .ok c => if c == n then none else some (n, c)
        | .error _ => none
    | _ => none
  let canon (c : String) : String := Id.run do
    let mut c := c
    for _ in [0:aliasOf.length] do
      match aliasOf.lookup c with
      | some d => c := d
      | none => break
    return c
  -- each class's names (`ClassNames`)
  let classInfo : List (String × ClassNames) ← real.filterMapM fun
    | .classDef p n _ tps _ parents _ fields methods => do
      let ps ← parents.mapM fun t => do
        match ← t.mapNamesM (tyNameQ (scopeOf n) (tps.map (·.name)) p) with
        | .name q | .app q _ => pure q
        | _ => pure ""
      let own := fields.map (·.name) ++ methods.filterMap fun
        | .fn _ mn .. => if mn.startsWith "(" || mn.startsWith "$" then none else some mn
        | _ => none
      let all := fields.map (bareName ·.name) ++ methods.filterMap fun
        | .fn _ mn .. => if mn.startsWith "$" then none else some (bareName mn)
        | _ => none
      let declared := fields.filter (!·.isOverride) |>.map (bareName ·.name)
      -- (the members written `(n:)x`, `n` the class itself)
      let ownQualified ← (fields.map (·.name) ++ methods.filterMap fun
          | .fn _ mn .. => some mn
          | _ => none).filterMapM fun x => do
        let some (q, y) := splitQual? x | return none
        match qualifier (scopeOf n) (tps.map (·.name)) p q with
        | .ok (.type c) => return if canon c == n then some y else none
        | _ => return none
      let exts := methods.filterMap fun
        | .fn _ mn .. => if isExt mn then some mn else none
        | _ => none
      return some (n, { parents := ps, own, all, declared, ownQualified, exts })
    | _ => return none
  let budget := 1 + classInfo.foldl (fun a (_, i) => a + i.parents.length + 1) 0
  -- the classes and interfaces `c` is below, itself first
  let above (c : String) : List String := Id.run do
    let mut seen : List String := []
    let mut todo := [c]
    for _ in [0:budget] do
      match todo with
      | [] => break
      | x :: rest =>
        todo := rest
        if !seen.contains x then
          seen := seen ++ [x]
          if let some (_, i) := classInfo.find? (·.1 == x) then todo := todo ++ i.parents
    return seen
  let infoOf (c : String) : Option ClassNames := (classInfo.find? (·.1 == c)).map (·.2)
  -- (`what` of each class at or above `c`)
  let ofClasses (what : ClassNames → List String) (c : String) : List String :=
    ((above c).flatMap fun x => ((infoOf x).map what).getD []).eraseDups
  let membersOf := ofClasses (·.own)
  let allMembersOf := ofClasses (·.all)
  let declares (c f : String) : Bool := ((infoOf c).map (·.declared.contains f)).getD false
  let enums : Std.HashSet String := Std.HashSet.ofList (real.filterMap fun
    | .const _ n _ _ (.enumDef ..) => some n
    | _ => none)
  let rAt (sc excl : List String) (self : Option String := none) : Resolver :=
    let members := (self.map allMembersOf).getD []
    { val := resolve "value" sc, bind := bind sc, ty := tyNameQ sc excl, qual := qual sc, ext := extAt sc,
      qualifier := qualifier sc excl,
      modulePath := modulePath sc, memberOf := memberOf sc,
      outer := fun p n => members.contains n || match find sc p n with
        | .ok (some _) => true
        | .ok none => false
        | .error _ => true,
      selfClass := self, isEnum := fun c => enums.contains (canon c),
      selfField := fun c f => match self with
        | some n => (above n).filter (declares · f) == [canon c]
        | none => false,
      selfQualified := (self.map fun n => (above n).flatMap fun x =>
        (((infoOf x).map (·.ownQualified)).getD []).map (·, shown x)).getD [],
      global := fun p n => match find sc p n with
        | .ok (some _) => true
        | .ok none => false
        | .error _ => true,
      tparams := excl }
  -- the parameters, and the resolver of the body, which sees them
  let params (r : Resolver) (p : Pos) (ps : List SParam) : Except String (List SParam × Resolver) := do
    let mut r' := r
    let mut names : Array String := #[]
    for prm in ps do
      let (n', r'') ← r'.binder p prm.name
      names := names.push n'
      r' := r''
    let ps ← (ps.zip names.toList).mapM fun (prm, n') => do
      return { prm with name := n', ty := ← prm.ty.mapNamesM (r.ty p), default := ← prm.default.mapM (·.mapNamesM r) }
    return (ps, r')
  -- a qualified definition's qualifier names where it is: its module
  -- (Book of Verse ch. 10, "Nested Module Qualification"; ch. 16)
  for (p, n, q) in markers qualMarker? do
    let sc := scopeOf n
    let x := (qualParts n).getLastD n
    if sc.isEmpty then
      throw s!"{p.show}: ({q}:){x}: {x} is defined at the top level, which has no name or path in openverse; a definition's qualifier names where it is defined: write {x}"
    match ← qualifier sc [] p q with
    | .module path _ =>
      if path != sc then
        throw s!"{p.show}: ({q}:){x}: {x} is defined in the module {shownP sc}, not in {shownP path}: a definition's qualifier names where it is defined"
    | .locals => throw s!"{p.show}: (local:){x}: (local:) qualifies a function's locals, and {x} is a member of the module {shownP sc}"
    | _ => throw s!"{p.show}: ({q}:){x}: {x} is defined in the module {shownP sc}, and {q} is no module: a definition's qualifier names where it is defined"
  -- a member's name as written in type `n`: `(q:)x`'s qualifier names `n`
  -- (its enum's value, its struct's field) (Book of Verse ch. 9, "Explicit
  -- Qualification")
  let ownName (n what : String) (p : Pos) (x : String) : Except String String := do
    let some (q, y) := splitQual? x | return x
    match ← qualifier (scopeOf n) [] p q with
    | .type c => if canon c == n then return y
                 throw s!"{p.show}: ({q}:){y}: {y} is {what} of {shown n}, not of {q}: a definition's qualifier names where it is defined"
    | .locals => throw s!"{p.show}: (local:){y}: (local:) qualifies a function's locals, and {y} is {what} of {shown n}"
    | _ => throw s!"{p.show}: ({q}:){y}: {y} is {what} of {shown n}: a definition's qualifier names where it is defined"
  real.mapM fun t => do
    match t with
    | .fn p n ps tps effs ret body =>
      let r := rAt (scopeOf n) (tps.map (·.name))
      let tps ← tps.mapM (·.mapBoundNamesM (r.ty p))
      let (ps, rb) ← params r p ps
      let isCtor := effs.any (constructorSpec? · |>.isSome)
      let effs ← effs.mapM fun e => match constructorSpec? e with
        | some c => do return constructorSpec (← r.ty p c)
        | none => pure e
      -- (a constructor's `F := e` items initialise fields: not binders)
      let body ← match isCtor, body with
        | true, .block bp items => do
          let items ← items.mapM fun
            | .decl dp dn ty v x => do return .decl dp dn (← ty.mapM (·.mapNamesM (r.ty dp))) v (← x.mapNamesM rb)
            | it => it.mapNamesM rb
          pure (SExpr.block bp items)
        | _, _ => body.mapNamesM rb
      return .fn p n ps tps effs (← ret.mapNamesM (r.ty p)) body
    | .const p n cspecs ty body =>
      let r := rAt (scopeOf n) []
      let body ← match body with
        | .enumDef ep vs specs => do pure (SExpr.enumDef ep (← vs.mapM (ownName n "a value" p)) specs)
        | .structDef sp tps specs fs => do
          pure (SExpr.structDef sp tps specs (← fs.mapM fun f => do return { f with name := ← ownName n "a field" sp f.name }))
        | b => pure b
      return .const p n cspecs (← ty.mapM (·.mapNamesM (r.ty p))) (← body.mapNamesM r)
    | .classDef p n nsp tps specs parents isI fields methods =>
      let r := rAt (scopeOf n) (tps.map (·.name)) (some n)
      let tps ← tps.mapM (·.mapBoundNamesM (r.ty p))
      for m in membersOf n do r.bind p m
      let parents ← parents.mapM (·.mapNamesM (r.ty p))
      -- (what the classes above have: a member qualified with its own class
      -- introduces a name none of them has, Book of Verse ch. 10)
      let inherited := ((above n).drop 1).flatMap fun x => ((infoOf x).map (·.all)).getD []
      -- a member's name as written: `(q:)x`, `q` its own class (the name
      -- is then `x`, unless a class above has an `x`: a second `x`, the
      -- elaboration of classes' to refuse), or what introduces the member
      -- it overrides (`(i:)M<override>`, #70; the elaboration of classes
      -- checks it); `(local:)` qualifies no member
      let memberName (mp : Pos) (x : String) (field : Bool) : Except String String := do
        let some (q, y) := splitQual? x | return x
        match ← r.qualifier mp q with
        | .type c =>
          let c := canon c
          if c == n then
            if !inherited.contains y then return y
            if field then
              throw s!"{mp.show}: ({q}:){y}: a field {y} beside the one {shown n} inherits: openverse does not support two fields of one name in a class"
            return s!"({c}:){y}"
          if field then
            if (above n).contains c && declares c y then return y
            throw s!"{mp.show}: ({q}:){y}: {q} is not {shown n}, nor a class or interface above it that declares the field {y}"
          return s!"({c}:){y}"
        | .locals => throw s!"{mp.show}: (local:){y}: (local:) qualifies a function's locals, and {y} is a member of {shown n}"
        | .super => throw s!"{mp.show}: (super:){y}: (super:) qualifies a call of the implementation above, not a definition"
        | _ => throw s!"{mp.show}: ({q}:){y}: a member's qualifier names its class, or, for an override, the class or interface that introduces it"
      let fields ← fields.mapM fun f => do
        return { f with name := ← memberName p f.name true, ty := ← f.ty.mapNamesM (r.ty p),
                        default := ← f.default.mapM (·.mapNamesM r) }

      let methods ← methods.mapM fun m => do
        match m with
        | .fn mp mn mps mtps meffs mret mbody =>
          let rm := rAt (scopeOf n) (tps.map (·.name) ++ mtps.map (·.name)) (some n)
          -- (the class's extension methods first: methods of `Self`)
          let exts := ofClasses (·.exts) n
          let ext (q : Pos) (x : String) : Except String (Option String) :=
            if exts.contains (extensionName x) then pure (some (extensionName x)) else rm.ext q x
          let rm := { rm with ext, selfExt := ext }
          let mtps ← mtps.mapM (·.mapBoundNamesM (rm.ty mp))
          let (mps, rmb) ← params rm mp mps
          return .fn mp (← memberName mp mn false) mps mtps meffs (← mret.mapNamesM (rm.ty mp)) (← mbody.mapNamesM rmb)
        | m => pure m
      return .classDef p n nsp tps specs parents isI fields methods

end OpenVerse.Front
