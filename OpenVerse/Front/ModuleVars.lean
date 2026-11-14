import OpenVerse.Front.Types
import OpenVerse.Front.TypeValues

/-!
# Module-scoped `var`s: one object's `var` fields

A `var X:weak_map(k, v) = map{}` at the top level or in a module (Book of
Verse ch. 3, "Module-Scoped weak_map Variables"; ch. 16, "Module-Scoped
Variables"; ch. 18, "Persistent Variables"; the rules are pinned in
docs/research/weak-map.md) is a variable of the program, read and written one
entry at a time.

openverse holds the program's module-scoped variables as the `var` fields of
one object of a hidden class, `$module_state`. A class without type
parameters has a prototype, which `Main`'s prelude makes before `Main` runs
(#37), and Verse Core types a reference literal to a prototype anywhere: the
module state is that prototype. Each use `X[k]` is written
`$moduleState.X[k]`, whose root the elaborator reads as the literal
(`stateRef?`), so a `set X[k] = v` writes the object's field in place, and a
failure context undoes it as it undoes any field's write. The prototype's
fields start as their types' defaults, the empty map, so a module-scoped
`var` starts as `map{}`, as the Book's do. No change to Verse Core, the
binary format or the C runtime.

`desugar` takes the parser's module-scoped `var`s (constants whose
specifiers include `moduleVarSpec`, `STop.moduleVar?`), after the modules
are resolved and the aliases written out, checks the Book's rules, adds the
class and rewrites the uses. Its two names, `stateClass` and `stateName`,
are markers no program can write (they start with `$`).
-/

namespace OpenVerse.Front.ModuleVars

/-- The hidden class whose prototype holds the module-scoped variables. -/
def stateClass : String := "$module_state"

/-- The name the rewritten uses read the module state by. -/
def stateName : String := "$moduleState"

/-- The prototype of the module state among the prototypes (its address),
    if the program has module-scoped variables. -/
def stateRef? (env : TyEnv) : Option Nat :=
  env.protos.findIdx? (·.1 == stateClass)

/-- The test runner's limit on module-scoped `var weak_map`s whose keys are
    `<persistent>` ("Set to 4 for VerseTestScriptCmd", `weak_map.versetest`
    623-664). -/
def persistentLimit : Nat := 4

/-- A type as written, for a message, a module's member `M.c`. -/
def showSTy (t : STy) : String := (TypeValues.writtenTy t).replace "::" "."


/-- A definition's name as written, `M.X` for `M::X`. -/
def shown (n : String) : String := showSTy (.name n)

/-- What the program defines that the rules ask about: each class's
    specifiers, and the `<persistable>` structs and enums. -/
structure Defs where
  classSpecs : List (String × List String)
  persistable : List String

def Defs.of (tops : List STop) : Defs where
  classSpecs := tops.filterMap fun
    | .classDef _ n _ _ specs _ _ _ _ => some (n, specs)
    | _ => none
  persistable := tops.filterMap fun
    | .const _ n _ none (.structDef _ [] specs _) | .const _ n _ none (.enumDef _ _ specs) =>
      if specs.contains "persistable" then some n else none
    | _ => none

/-- Whether values of a type persist (Book of Verse ch. 17, "Built-in
    Persistable Types" and "Custom Persistable Types"), as openverse reads
    it for a `<persistable>` struct's fields (`typeEnvironment`): the
    primitive types but `rational`, containers of persisting types, and the
    `<persistable>` structs and enums (ch. 17: "Enums without
    `<persistable>` specifier cannot be used"). openverse has no
    `<persistable>` classes (#11), and a `weak_map` does not persist. -/
partial def Defs.persists (d : Defs) : STy → Bool
  | .name n => ["int", "float", "logic", "string", "char", "char32"].contains n ||
      d.persistable.contains n
  | .app .. | .fn .. => false
  -- (a container persists when its parts do)
  | t => t.children.all d.persists

/-- A module-scoped variable: where and what it is. -/
structure Var where
  pos : Pos
  name : String
  ty : STy
  init : SExpr
  deriving Inhabited

/-- Why the uses of a module-scoped variable are one entry at a time. -/
def entryOnly (name : String) : String :=
  s!"the module-scoped var {showSTy (.name name)} is read and written one entry at a time, {showSTy (.name name)}[Key] (Book of Verse ch. 3: \"The complete map can neither be read nor replaced, while reading and writing one entry at a time is allowed\")"

/-- The Book's rules for the module-scoped variables `vs` (each a 3502 of its
    tests; docs/research/weak-map.md, "The rules, pinned"). -/
def check (d : Defs) (vs : List Var) : Except String Unit := do
  let mut persistent : List (Var × Bool) := []
  for v in vs do
    let shown := showSTy (.name v.name)
    -- (1) a weak_map (ch. 16: "Direct `var` declarations of simple types
    -- (like `var X:int = 0`) are not allowed at module scope"; ch. 18: "A
    -- module-scoped `var` of any other type is rejected outright")
    let .app "weak_map" [k, val] := v.ty
      | throw s!"{v.pos.show}: the module-scoped var {shown} has the type {showSTy v.ty}: a module-scoped var must be a weak_map keyed by a class with <module_scoped_var_weak_map_key> (Book of Verse ch. 16: \"Direct `var` declarations of simple types (like `var X:int = 0`) are not allowed at module scope\"; ch. 18)"
    -- (2) its key a class with <module_scoped_var_weak_map_key>
    let keySpecs : Option (List String) := match k with
      | .name c => d.classSpecs.lookup c
      | _ => none
    let some ks := keySpecs.filter (·.contains "module_scoped_var_weak_map_key")
      | throw s!"{v.pos.show}: the module-scoped var {shown} is keyed by {showSTy k}, which is not a class with <module_scoped_var_weak_map_key> (Book of Verse ch. 3: \"The key type must carry the `<module_scoped_var_weak_map_key>` specifier\")"
    -- (3) with a <persistent> key, a persistable value
    if ks.contains "persistent" then
      if !d.persists val then
        throw s!"{v.pos.show}: the module-scoped var {shown} is keyed by the <persistent> class {showSTy k}, so its value type must be persistable, and {showSTy val} is not (Book of Verse ch. 3: \"The value type must be persistable\"; ch. 17)"
      persistent := persistent ++ [(v, match val with
        | .name c => (d.classSpecs.lookup c).isSome
        | _ => false)]
    -- (it starts as the empty map, the prototype's field; one declared with
    -- no value, `Refused.declaredVariable`, `Attributes.apply` refused)
    match v.init with
    | .mapLit _ [] => pure ()
    | e => throw s!"{e.pos.show}: the module-scoped var {shown} starts as map\{} in openverse: an initial value with entries is not supported yet"
  -- (5) at most `persistentLimit` with <persistent> keys, and at the limit
  -- one of them with a class value (the tests' 3502s, 624-664)
  if persistent.length > persistentLimit then
    let (v, _) := persistent[persistentLimit]!
    throw s!"{v.pos.show}: the module-scoped var {showSTy (.name v.name)} is one of {persistent.length} weak_maps keyed by <persistent> classes, and a program may have {persistentLimit} (Book of Verse tests, weak_map.versetest 623-664: \"Limited number of persistent `var` `weak_map`s per island. Set to 4 for VerseTestScriptCmd.\")"
  if persistent.length == persistentLimit && !persistent.any (·.2) then
    let (v, _) := persistent.getLast!
    throw s!"{v.pos.show}: the module-scoped var {showSTy (.name v.name)} is the {persistentLimit}th weak_map keyed by a <persistent> class, and at that limit one of them must have a class value (Book of Verse tests, weak_map.versetest 630-645: \"Fail due to none of the value types being a class\")"

/-- `e` with each use of a module-scoped variable `X[k]` written as one
    through the module state, `$moduleState.X[k]`; any other use of `X` is
    refused (the whole map is neither read nor replaced). -/
partial def rewrite (names : List String) (e : SExpr) : Except String SExpr :=
  match e with
  -- (a local named like one, which Verse refuses as shadowing, as it refuses
  -- one named like a constant; one of a module's, `resolveModules` refuses)
  | .decl p n _ _ _ | .gen p n none _ =>
    if names.contains n then throw s!"{p.show}: '{n}' is already the name of a module-scoped var" else e.mapChildrenM (rewrite names)
  | .gen p n (some i) _ =>
    if names.contains n || names.contains i then throw s!"{p.show}: '{if names.contains n then n else i}' is already the name of a module-scoped var"
    else e.mapChildrenM (rewrite names)
  | .app p (.ident q n) [k] true =>
    if names.contains n then
      return .app p (.member q (.ident q stateName) n) [← rewrite names k] true
    else e.mapChildrenM (rewrite names)
  | .ident p n => if names.contains n then throw s!"{p.show}: {entryOnly n}" else pure e
  -- (a struct's field defaults, which `children` leaves out)
  | .structDef p tps specs fs => do
    return .structDef p tps specs (← fs.mapM fun f => do return { f with default := ← f.default.mapM (rewrite names) })
  | _ => e.mapChildrenM (rewrite names)

def rewriteTop (names : List String) : STop → Except String STop
  | .fn p n ps tps specs r body => do
    if let some q := ps.find? (names.contains ·.name) then
      throw s!"{p.show}: the parameter '{q.name}' of {shown n} is already the name of a module-scoped var"
    let ps ← ps.mapM fun q => do return { q with default := ← q.default.mapM (rewrite names) }
    return .fn p n ps tps specs r (← rewrite names body)
  | .const p n specs t e => do return .const p n specs t (← rewrite names e)
  | .classDef p n ns tps specs parents iface fs ms => do
    -- (a member is named in its methods' bodies as a variable is)
    if let some f := fs.find? (names.contains ·.name) then
      throw s!"{p.show}: the field '{f.name}' of {shown n} is already the name of a module-scoped var"
    for m in ms do
      if let .fn q mn .. := m then
        if names.contains mn then throw s!"{q.show}: the method '{mn}' of {shown n} is already the name of a module-scoped var"
    let fs ← fs.mapM fun f => do return { f with default := ← f.default.mapM (rewrite names) }
    return .classDef p n ns tps specs parents iface fs (← ms.mapM (rewriteTop names))

/-- The program with its module-scoped variables taken out: checked, held as
    the `var` fields of `$module_state` (added last, so that no class's tag
    changes), and every use rewritten. A program without any is returned as
    it is. -/
def desugar (tops : List STop) : Except String (List STop) := do
  let vs : List Var := tops.filterMap fun top =>
    top.moduleVar?.map fun (pos, name, _, ty, init) => { pos, name, ty, init }
  if vs.isEmpty then return tops
  check (Defs.of tops) vs
  let names := vs.map (·.name)
  let rest := tops.filter fun
    | .const _ n _ _ _ => !names.contains n
    | _ => true
  let rest ← rest.mapM (rewriteTop names)
  let fields : List SField := vs.map fun v =>
    { name := v.name, ty := v.ty, default := some v.init, isVar := true }
  let p := (vs.head?.map (·.pos)).getD { line := 0, col := 0 }
  return rest ++ [.classDef p stateClass [] [] [] [] false fields []]

end OpenVerse.Front.ModuleVars
