/-
  OpenVerse front end — type aliases (Book of Verse ch. 10, "Aliases"; ch. 11,
  "Type Aliases"; the rules are pinned in docs/research/type-aliases.md).

  `name := t` at the top level or in a module, where `t` is a type, names
  `t`: `name` is a type alias. `name(u:type, …) := t` is a parametric one, a
  function from types to types. The parser marks an alias whose type is
  written as only a type can be (`?int`, `[]t`, `int->int`, `tuple(…)`,
  `type{_(…):t}`: `SExpr.typeAlias`). `name := c` and `name := box(int)`
  could also be constants; once the modules' names are resolved, this pass
  decides by what `c` and `box` are: a definition is an alias when its value
  is a type's name (a built-in type, a class, interface, struct, enum,
  refinement type or alias), or a parametric type's applied to as many types
  as it has parameters (`writesType`): `X := c(Y)`, a cast of a constant,
  stays a constant.

  It then writes, in every other definition, the type an alias names
  wherever the alias is used (its type arguments for its parameters) and
  drops the aliases' definitions. The elaborator sees the program as if each
  type had been written out: nothing after this pass knows aliases exist, and
  an alias is the type it names everywhere, in overloads, casts and messages.
  Where a value, a construction or a qualifier names a class, struct, enum,
  interface or refinement type (`a{}`, `f.E0`, `a[X]`, `(a:)M`), an alias of
  that type stands for it.

  An alias is used only after its definition, in the order the program's
  definitions are loaded (an imported file's first), and names no alias
  defined after it, nor itself: writing it out always ends.
-/
import OpenVerse.Front.Modules
import OpenVerse.Front.PreludeNeeds

namespace OpenVerse.Front.Aliases

/-- An alias: where it is defined, its parameters, and the type it names,
    the aliases in it written out. -/
structure Alias where
  pos : Pos
  params : List String
  body : STy

/-- A qualified name as a program writes it: `A.B.c` for `A::B::c`. -/
def shown (n : String) : String := ".".intercalate (n.splitOn "::")

/-- The aliases a definition can use: those defined before it (`known`),
    out of all the program's (`all`). -/
structure Scope where
  known : Std.HashMap String Alias := {}
  all : Std.HashSet String := {}

/-- `n` is not an alias defined after the definition being written out. -/
def Scope.notLater (s : Scope) (p : Pos) (n : String) : Except String Unit := do
  if s.all.contains n && !s.known.contains n then
    throw s!"{p.show}: the type alias {shown n} is used before its definition: an alias must be defined before it is used (Book of Verse ch. 11, \"Type Aliases\")"

/-- `t` with each alias written out, its type arguments for its parameters. -/
partial def Scope.ty (s : Scope) (p : Pos) : STy → Except String STy
  | .name n => do
    s.notLater p n
    match s.known[n]? with
    | some a =>
      if a.params.isEmpty then pure a.body
      else throw s!"{p.show}: {shown n} is parametric: write {shown n}(…) with {a.params.length} type argument(s)"
    | none => pure (.name n)
  | .app n ts => do
    let ts ← ts.mapM (s.ty p)
    s.notLater p n
    match s.known[n]? with
    | some a =>
      if a.params.length != ts.length then
        throw s!"{p.show}: {shown n} takes {a.params.length} type argument(s), found {ts.length}"
      pure (a.body.substNames (a.params.zip ts))
    | none => pure (.app n ts)
  | .arr t => return .arr (← s.ty p t)
  | .opt t => return .opt (← s.ty p t)
  | .tup ts => return .tup (← ts.mapM (s.ty p))
  | .map k v => return .map (← s.ty p k) (← s.ty p v)
  | .fn ps es r => return .fn (← ps.mapM (s.ty p)) es (← s.ty p r)

/-- Where a value, a qualifier or a constructor names a type `n`: the type
    an alias names, when it is a name (`c` for `a := c`). -/
def Scope.typeName (s : Scope) (p : Pos) (n : String) : Except String String := do
  s.notLater p n
  match s.known[n]? with
  | some { params := [], body := .name c, .. } => pure c
  | some _ => throw s!"{p.show}: {shown n} is a type alias: a type, not a value"
  | none => pure n

/-- A method's name as written: `(q:)M`'s qualifier `q` as `typeName`. -/
def Scope.method (s : Scope) (p : Pos) (m : String) : Except String String := do
  if m.startsWith "(" then
    if let [q, x] := (m.drop 1).toString.splitOn ":)" then return s!"({← s.typeName p q}:){x}"
  return m

/-- A construction's type, `n(ts)`, with an alias written out: a struct's or
    a class's. -/
def Scope.construct (s : Scope) (p : Pos) (n : String) (ts : List STy) : Except String (String × List STy) := do
  if !s.all.contains n then return (n, ← ts.mapM (s.ty p))
  match ← s.ty p (if ts.isEmpty then .name n else .app n ts) with
  | .name c => pure (c, [])
  | .app c args => pure (c, args)
  | _ => throw s!"{p.show}: {shown n} is a type alias of a type that is not a struct or a class: it cannot be constructed"

def Scope.tparam (s : Scope) (tp : TParam) : Except String TParam := do
  return { tp with upperBound := ← tp.upperBound.mapM (s.ty tp.pos) }

/-- An expression with each alias written out. -/
partial def Scope.expr (s : Scope) : SExpr → Except String SExpr
  | .ident p n => do
    -- (`$ctor:D`, a delegation to class `D`'s constructor)
    if n.startsWith "$ctor:" then
      return .ident p s!"$ctor:{← s.typeName p (n.drop "$ctor:".length).toString}"
    return .ident p (← s.typeName p n)
  | .member p x m => return .member p (← s.expr x) (← s.method p m)
  | .decl p n t v x => return .decl p n (← t.mapM (s.ty p)) v (← s.expr x)
  | .construct p n ts fs => do
    let (n, ts) ← s.construct p n ts
    return .construct p n ts (← fs.mapM s.expr)
  | .structDef p tps specs fs =>
    return .structDef p (← tps.mapM s.tparam) specs
      (← fs.mapM fun f => do return { f with ty := ← s.ty p f.ty, default := ← f.default.mapM s.expr })
  | .refineDef p v base cs => return .refineDef p v (← s.ty p base) (← cs.mapM s.expr)
  | e => e.mapChildrenM s.expr

/-- A class's field with each alias written out. -/
def Scope.field (s : Scope) (p : Pos) (f : SField) : Except String SField := do
  return { f with ty := ← s.ty p f.ty, default := ← f.default.mapM s.expr }

/-- A definition with each alias written out. -/
partial def Scope.top (s : Scope) : STop → Except String STop
  | .fn p n ps tps effs ret body => do
    let ps ← ps.mapM fun prm => do
      return { prm with ty := ← s.ty p prm.ty, default := ← prm.default.mapM s.expr }
    let effs ← effs.mapM fun e =>
      if e.startsWith "$constructor:" then do
        return s!"$constructor:{← s.typeName p (e.drop "$constructor:".length).toString}"
      else pure e
    return .fn p (← s.method p n) ps (← tps.mapM s.tparam) effs (← s.ty p ret) (← s.expr body)
  | .const p n cspecs t e => return .const p n cspecs (← t.mapM (s.ty p)) (← s.expr e)
  | .classDef p n nsp tps specs parents isI fields methods =>
    return .classDef p n nsp (← tps.mapM s.tparam) specs (← parents.mapM (s.ty p)) isI
      (← fields.mapM (s.field p)) (← methods.mapM s.top)


/-- Whether `t`, written as a value could be (`SExpr.asType?`), is a type:
    a type's name, or a parametric type's name applied to as many types as
    it has parameters. `arity n` is `none` when `n` is no type's name, and
    `some none` for the prelude's types, whose arities are its own. So
    `box(int)` is a type, and `c(X)`, the cast of a constant to a class,
    and `any(X)` are not. -/
partial def writesType (arity : String → Option (Option Nat)) : STy → Bool
  | .name n => (arity n).isSome
  | .app n ts => match arity n with
    | some none => ts.all (writesType arity)
    | some (some k) => k == ts.length && ts.all (writesType arity)
    | none => false
  | _ => true

/-- Each name in an alias's type, its aliases written out, is a type's or a
    parameter's, applied to as many type arguments as it takes. -/
partial def checkNames (p : Pos) (arity : String → Option (Option Nat)) (params : List String) :
    STy → Except String Unit
  | .name n => do
    if params.contains n || n.startsWith "$" then return
    match arity n with
    | none => throw s!"{p.show}: {unknownTypeMessage (shown n)}"
    | some (some k) =>
      if k > 0 then throw s!"{p.show}: {shown n} is parametric: write {shown n}(…) with {k} type argument(s)"
    | some none => pure ()
  | .app n ts => do
    -- (`?N`: a function type's named parameter, #503)
    if !n.startsWith "?" && !n.startsWith "$" then
      match arity n with
      | none => throw s!"{p.show}: {unknownTypeMessage (shown n)}"
      | some (some k) =>
        if k != ts.length then throw s!"{p.show}: {shown n} takes {k} type argument(s), found {ts.length}"
      | some none => pure ()
    ts.forM (checkNames p arity params)
  | .arr t | .opt t => checkNames p arity params t
  | .tup ts => ts.forM (checkNames p arity params)
  | .map k v => do checkNames p arity params k; checkNames p arity params v
  | .fn ps _ r => do ps.forM (checkNames p arity params); checkNames p arity params r

/-- The program's definitions, modules resolved, with every type alias
    written out where it is used and the aliases' definitions dropped (see
    the file's header). -/
def expand (tops : List STop) : Except String (List STop) := do
  -- the types the program defines, with their numbers of type parameters
  let defined : Std.HashMap String Nat := Std.HashMap.ofList (tops.filterMap fun
    | .classDef _ n _ tps .. | .const _ n _ none (.structDef _ tps ..) => some (n, tps.length)
    | .const _ n _ none (.enumDef ..) | .const _ n _ none (.refineDef ..) => some (n, 0)
    | _ => none)
  let typeArity (aliases : Std.HashMap String Nat) (n : String) : Option (Option Nat) :=
    if builtinTypes.contains n || n == "comparable" then some (some 0)
    else if let some k := defined[n]? then some (some k)
    else if let some k := aliases[n]? then some (some k)
    else if PreludeNeeds.names.contains n then some none
    else none
  -- the definitions `name := e` that may be aliases: the type each writes,
  -- its number of parameters, and whether the parser knows it is one
  let written : List (String × STy × Nat × Bool) := tops.filterMap fun
    | .const _ n _ none (.typeAlias _ tps t) => some (n, t, tps.length, true)
    | .const _ n _ none e => e.asType?.map (n, ·, 0, false)
    | _ => none
  if written.isEmpty then return tops
  -- (one whose value is a type that names aliases is one too, wherever they
  -- are defined: `b := a` and `a := int`, in either order)
  let mut aliases : Std.HashMap String Nat := Std.HashMap.ofList
    (written.filterMap fun (n, _, k, explicit) => if explicit then some (n, k) else none)
  for _ in [0:written.length] do
    let more := written.filter fun (n, t, _, _) => !aliases.contains n && writesType (typeArity aliases) t
    if more.isEmpty then break
    aliases := more.foldl (fun s (n, _, k, _) => s.insert n k) aliases
  -- no definition, at any scope, takes a top-level alias's name (a module's
  -- are `resolveModules`' to check, as its other members')
  let global := aliases.keys.filter fun n => (qualParts n).length == 1
  for t in tops do
    let own := match t with
      | .fn _ n .. | .const _ n .. | .classDef _ n .. => n
    for (p, n) in t.definedNames do
      if n != own && global.contains n then
        throw s!"{p.show}: '{n}' is already defined (as a type alias); Verse does not allow shadowing"
  let mut scope : Scope := { all := Std.HashSet.ofList aliases.keys }
  let mut out : Array STop := #[]
  -- (in an alias's type, its aliases written out: no alias, and `comparable`
  -- is no type yet)
  let bodyArity (n : String) : Option (Option Nat) := if n == "comparable" then none else typeArity {} n
  for t in tops do
    if let .const p n _ none e := t then

      if aliases.contains n then
        let (tps, ty) := match e with
          | .typeAlias _ tps ty => (tps, ty)
          | e => ([], e.asType?.getD (.tup []))
        let last := (qualParts n).getLastD n
        if (builtinTypes ++ ["comparable", "type"]).contains last then
          throw s!"{p.show}: {last} is a built-in type"
        if let some tp := tps.find? (·.constraint != "type") then
          throw s!"{tp.pos.show}: a parameter of a type alias is written {tp.name}:type (a bound on one is not supported)"
        if ty.allNames.contains n then
          throw s!"{p.show}: the type alias {shown n} names itself, so writing it out would never end (Book of Verse ch. 10, \"Disallowed: Direct Type Alias Recursion\"); a class can hold a value of its own type"
        let body ← scope.ty p ty
        -- (an alias's type is checked where it is used, as written there;
        -- its names, and their numbers of type arguments, where it is defined)
        let params := tps.map (·.name)
        checkNames p bodyArity params body
        scope := { scope with known := scope.known.insert n { pos := p, params, body } }
        continue
      -- (a module's data states its type, Book of Verse ch. 16: the parser
      -- leaves `X := c` to this pass, as `c` may be a type)
      if (qualParts n).length > 1 && !(qualParts n).any (·.startsWith "$") && e.asType?.isSome then
        throw s!"{p.show}: a constant in a module needs its type: write {(qualParts n).getLastD n}:t = …"
    out := out.push (← if aliases.isEmpty then pure t else scope.top t)
  return out.toList

end OpenVerse.Front.Aliases
