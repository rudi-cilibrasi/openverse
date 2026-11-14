/- Source effect admission before function-value and continuation lowering. -/
import OpenVerse.Front.UpperBounds

namespace OpenVerse.Front.EffectPolicy

/-- The implemented source effect vocabulary. No annotation proves termination
    or supplies a prediction/foreign-code execution model. -/
def supported : List String :=
  ["computes", "reads", "writes", "allocates", "transacts", "decides", "suspends"]

def effectNames : List String := supported ++
  ["converges", "predicts", "no_rollback", "dictates", "diverges", "succeeds", "fails", "varies"]

def metadata : List String :=
  ["public", "internal", "private", "protected", "epic_internal", "override", "final", "abstract", "constructor"]

def reject (p : Pos) (message : String) : Except String Unit :=
  .error s!"{p.show}: {message}"

def checkUnsupported (p : Pos) (specs : List String) : Except String Unit := do
  for sp in specs do
    match sp with
    | "predicts" => reject p "<predicts> is unsupported: prediction call propagation and client/server execution are not implemented (#494; unreleased in the pinned Book)"
    | "converges" => reject p "<converges> is unsupported: termination contracts are not checked (#494); execution fuel is not a termination proof"
    | "native" | "native_callable" =>
      reject p s!"<{sp}> is unsupported: source annotations cannot create a trusted native binding (#494)"
    | "no_rollback" =>
      reject p "<no_rollback> is unsupported as a source annotation in OpenVerse; transactional output/events retain their documented policy (#494, #495)"
    | "dictates" | "diverges" | "succeeds" | "fails" =>
      reject p s!"explicit <{sp}> annotations are unsupported in OpenVerse (#494); the pinned Book describes this as an implicit effect"
    | "varies" => reject p "<varies> is an obsolete effect specifier and is unsupported (#494)"
    | _ => pure ()

/-- Where a declaration's specifiers are written (`specifierPlaces`). -/
inductive Place where
  /-- the name of a constant, class, interface, struct, enum, alias or
      module, of a module or the top level -/
  | definition
  /-- a function of a module or of the top level: its name or after its parameters -/
  | function
  /-- a method of a class or an interface: its name or after its parameters -/
  | method
  /-- a field's name, in a class or an interface -/
  | field
  /-- a field's name, in a struct -/
  | structField
  /-- a field's `var`: its write access (`var<private> X<public>:int`) -/
  | var
  /-- after `class`, `interface` or `struct` -/
  | classType | interfaceType | structType
  deriving BEq, Repr

def Place.what : Place → String
  | .definition => "the name of a constant, type or module"
  | .function => "a module's function"
  | .method => "a method"
  | .field => "a field"
  | .structField => "a struct's field"
  | .var => "a field's var"
  | .classType => "a class"
  | .interfaceType => "an interface"
  | .structType => "a struct"

/-- The access specifiers (Book of Verse ch. 12; the rules are pinned in
    docs/research/access-specifiers.md). -/
def accessNames : List String := ["public", "internal", "protected", "private", "epic_internal"]

def isAccess (sp : String) : Bool := accessNames.contains sp || sp.startsWith "scoped{"

/-- A specifier's entry in `specifierPlaces`: `scoped` for `scoped{…}`. -/
def placeKey (sp : String) : String := if sp.startsWith "scoped{" then "scoped" else sp


/-- The specifiers that say what a declaration is, each with the places it
    may be written; anywhere else it is refused (`checkPlace`), as the Book of
    Verse's tests do (`Tests/Attributes/`, `Castable.versetest`; ch. 10: only
    a class may be `<abstract>`, ch. 17: `<persistable>` classes and structs).
    What each requires of what it is on is checked where that is known:
    `<final>` a member's body or value (`checkField`, `checkPlaces`), and
    of a field that nothing below overrides it nor a construction sets it
    (`classFields`, `elabConstructionValue`: the field keeps its specifiers,
    `SField.specs`); `<abstract>` and `<concrete>` not

    together (`checkPlaces`);
    `<concrete>` a default for every field (a struct's in `checkPlaces`, a
    class's with its inherited fields, `classFields`); `<castable>` and
    `<final_super_base>` of the classes below (`classHierarchy`); a
    `<persistable>` struct's fields persist (`typeEnvironment`). Enums take
    `<open>`, `<closed>` and `<persistable>` (the parser's check), and
    effects are `checkSpecs`'. An access specifier (Book of Verse ch. 12)
    goes on a definition of a module or of a class: `<protected>` and
    `<private>` only on a class's or an interface's members (and
    `<protected>` on a class's constructor, `class<protected>`), and a
    struct's field is `<public>`; at most one in a place, and none on an
    override, which has the access of what it overrides (`checkAccess`). -/
def specifierPlaces : List (String × List Place) :=
  [("abstract", [.classType]),
   ("concrete", [.classType, .structType]),
   ("final", [.classType, .method, .field, .structField]),
   ("final_super", [.classType]),
   ("final_super_base", [.classType, .interfaceType]),
   ("castable", [.classType, .interfaceType]),
   ("unique", [.classType, .interfaceType]),
   ("persistable", [.classType, .structType]),
   -- (a class whose objects key module-scoped `var weak_map`s, and one whose
   -- entries persist: `player`, `session`, Book of Verse ch. 3)
   ("persistent", [.classType]),
   ("module_scoped_var_weak_map_key", [.classType]),
   ("override", [.method, .field, .structField]),
   ("public", [.definition, .function, .method, .field, .structField, .var, .classType, .interfaceType, .structType]),
   ("internal", [.definition, .function, .method, .field, .var, .classType, .interfaceType, .structType]),
   ("epic_internal", [.definition, .function, .method, .field, .var, .classType, .interfaceType, .structType]),
   ("scoped", [.definition, .function, .method, .field, .var, .classType, .interfaceType, .structType]),
   ("protected", [.method, .field, .var, .classType]),
   ("private", [.method, .field, .var])]

/-- Why an access specifier is not allowed at `place` (Book of Verse ch. 12
    and its tests: 3594). -/
def accessPlaceWhy : Place → String
  | .definition | .function =>
    "a module's definition is <public>, <internal>, <scoped{…}> or <epic_internal>; <protected> and <private> are for a class's or an interface's members (Book of Verse ch. 11, 12)"
  | .structField => "a struct's fields are public (Book of Verse ch. 9: \"All struct fields are public\")"
  | .classType => "a class's constructor is <public>, <internal>, <protected> or <epic_internal> (Book of Verse tests, Classes/AccessSpecifiers)"
  | .interfaceType | .structType =>
    "its constructor is <public>, <internal> or <epic_internal> (Book of Verse tests, ArchetypeAccessSpecifiers)"
  | _ => ""

/-- Each specifier of `specifierPlaces` in `specs`, written at `place`, is
    one of its places; and at most one access specifier is written there
    (Book of Verse tests, Classes/AccessSpecifiers: 3543, 3642). -/
def checkPlace (p : Pos) (place : Place) (specs : List String) : Except String Unit := do
  for sp in specs do
    if let some places := specifierPlaces.lookup (placeKey sp) then
      if !places.contains place then
        if isAccess sp then reject p s!"<{sp}> is not allowed on {place.what}: {accessPlaceWhy place}"
        reject p s!"<{sp}> is not allowed on {place.what}: it is for {" or ".intercalate (places.map (·.what))}"
  match specs.filter isAccess with
  | a :: b :: _ =>
    if a == b then reject p s!"<{a}> is written twice on {place.what}"
    reject p s!"{place.what} has two access specifiers, <{a}> and <{b}>: a definition has one access level (Book of Verse ch. 12)"
  | _ => pure ()

/-- An override has the access of what it overrides, for reading and for
    writing, and writes none (Book of Verse tests, AccessLevelInheritance:
    3650, whether wider, narrower or the same). -/
def checkOverrideAccess (p : Pos) (what : String) (specs varSpecs : List String) : Except String Unit := do
  if specs.contains "override" then
    if let some sp := (specs ++ varSpecs).find? isAccess then
      reject p s!"<{sp}> on {what}<override>: an override has the access of the member it overrides and writes none (Book of Verse tests, AccessLevelInheritance)"

/-- Whether openverse knows `sp` on a definition's name or a field: a
    specifier of `specifierPlaces`, an effect (refused where none goes), or
    one `checkUnsupported` or `checkSpecs` refuses with its reason. -/
def known (sp : String) : Bool :=
  (specifierPlaces.lookup (placeKey sp)).isSome || effectNames.contains sp ||
    ["predicts", "native", "native_callable", "no_rollback", "constructor"].contains sp ||
    -- (a field's accessors, `checkField`)
    sp.startsWith "getter(" || sp.startsWith "setter("

/-- Used by the parser at sites where attributes are otherwise discarded: a
    field's name (`kind` "field", at `place`) or a definition's. -/
def checkNonFunction (p : Pos) (kind : String) (specs : List String)
    (place : Place := if kind == "field" then .field else .definition) : Except String Unit := do
  checkUnsupported p specs
  if let some sp := specs.find? effectNames.contains then
    reject p s!"<{sp}> on a {kind} is unsupported: effect specifiers are not supported at this declaration position (#494)"
  checkPlace p place specs

/-- The specifiers of a definition's name: a constant's, class's,
    interface's, struct's, enum's or alias's. -/
def checkName (p : Pos) (specs : List String) : Except String Unit := do
  checkUnsupported p specs
  checkPlace p .definition specs

/-- A field's specifiers, on its name and its `var`, at `place` (a class's or
    an interface's field, or a struct's): `var` takes an access specifier,
    an override none, and a `<final>` field cannot be given another value,
    so it needs one (`hasValue`). -/
def checkField (p : Pos) (place : Place) (name : String) (specs varSpecs : List String) (hasValue : Bool)
    (isVar : Bool := true) : Except String Unit := do
  -- (a field with accessors, `var X<getter(GetX)><setter(SetX)>:t =
  -- external{}`, Book of Verse ch. 10, "Fields with Accessors": one getter
  -- and one setter, on a `var` of a class or an interface, ch. 12; the rest
  -- `Accessors.desugar` checks)
  let accessors := specs.filter fun sp => sp.startsWith "getter(" || sp.startsWith "setter("
  if let some sp := accessors.head? then
    if let .structField := place then
      reject p s!"<{sp}>: a struct's field cannot have accessors, only a class's or an interface's (Book of Verse ch. 12)"
    if (accessors.filter (·.startsWith "getter(")).length != 1 || (accessors.filter (·.startsWith "setter(")).length != 1 then
      reject p s!"{name} is a field with accessors: it has one <getter(…)> and one <setter(…)> (Book of Verse ch. 12: \"Must include both\")"
    if !isVar then
      reject p s!"{name} is a field with accessors, so it is a var: write var {name}<getter(…)><setter(…)>:t (Book of Verse ch. 12)"
  checkNonFunction p "field" specs place
  if let some sp := varSpecs.find? (fun sp => !isAccess sp && known sp) then

    reject p s!"<{sp}> is not allowed on var: var takes the field's write access, an access specifier (Book of Verse ch. 12)"
  checkPlace p .var varSpecs
  checkOverrideAccess p name specs varSpecs
  if specs.contains "final" && !hasValue then
    reject p "a <final> field needs a value: it cannot be given one elsewhere"


/-- Declaration metadata is separate from effects; its existing access and
    override semantics remain the elaborator's responsibility. Compiler-only
    markers cannot be written by the source lexer. -/
def checkSpecs (p : Pos) (subject : String) (specs : List String)
    (typeOnly : Bool := false) : Except String Unit := do
  -- Retain the established exclusive-effect diagnostic for declarations.
  -- (Book of Verse ch. 13, `13_effects.md:99-105`: "*exclusive*
  -- specifiers (`<converges>`, `<computes>`, `<transacts>`) and *additive*
  -- specifiers (`<suspends>`, `<decides>`, `<reads>`, `<writes>`,
  -- `<allocates>`). A function may have at most one exclusive specifier but
  -- can combine multiple additive ones": `<computes><allocates>` allows
  -- `allocates`, `heapAllowed`)
  if (["converges", "computes", "transacts"].filter specs.contains).length > 1 then
    reject p s!"{subject} has more than one of <converges>, <computes> and <transacts> (they exclude each other)"
  if specs.contains "suspends" && specs.contains "decides" then
    reject p s!"{subject} is both <suspends> and <decides>, which exclude each other"
  -- (Book of Verse ch. 13: "`<transacts>` implies `reads`, `writes` and
  -- `allocates`")
  if specs.contains "transacts" then
    if let some sp := ["reads", "writes", "allocates"].find? specs.contains then
      reject p s!"<{sp}> on {subject} is redundant: <transacts> implies it"
  let mut seen : List String := []
  for sp in specs do
    if effectNames.contains sp then
      if seen.contains sp then reject p s!"duplicate effect specifier <{sp}> on {subject}"
      seen := sp :: seen
  checkUnsupported p specs
  for sp in specs do
    if supported.contains sp then continue
    -- (a name that is no specifier openverse knows may name an access
    -- level, `S := scoped{…}`: `resolveSpecifiers` decides)
    if !typeOnly && (metadata.contains sp || sp.startsWith "$" || isAccess sp || !known sp) then continue
    reject p s!"unknown or unsupported {if typeOnly then "function-type effect" else "function specifier"} <{sp}> on {subject} (#494)"

/-- Construction has the same heap family as functions, but is immediate and
    cannot declare failure. Declaration metadata retains its separate meaning. -/
def checkData (p : Pos) (kind : String) (specs : List String) : Except String Unit := do
  checkUnsupported p specs
  checkSpecs p kind (specs.filter effectNames.contains)
  for sp in ["decides", "suspends"] do
    if specs.contains sp then reject p s!"<{sp}> is not allowed on a {kind}: construction effects are heap effects"

/-- No heap specifier means transacts, also for data types (pinned
    Tests/Effects.versetest). Metadata does not change that default.
    `<computes>` alone means none, and with additive heap specifiers
    (`<computes><allocates>`) those (Book of Verse ch. 13, "*exclusive*
    specifiers … and *additive* specifiers"; `Attributes/allocates.versetest`
    4-5: "Combines with <varies> and <computes>"). -/
def constructionFx (specs : List String) : List String :=
  let heap := ["reads", "writes", "allocates"]
  if specs.contains "transacts" then heap
  else if heap.any specs.contains then heap.filter specs.contains
  else if specs.contains "computes" then []
  else heap

partial def checkTy (p : Pos) : STy → Except String Unit
  | .name _ => pure ()
  | .arr t | .opt t => checkTy p t
  | .tup ts | .app _ ts => ts.forM (checkTy p)
  | .map k v => do checkTy p k; checkTy p v
  | .fn ps specs ret => do
    checkSpecs p "function type" specs true
    ps.forM (checkTy p)
    checkTy p ret

def checkTParams (params : List TParam) : Except String Unit := do
  for param in params do param.upperBound.forM (checkTy param.pos)
  UpperBounds.checkKinds params

partial def checkExpr (e : SExpr) (file : String := "") : Except String Unit := do
  let p := if e.pos.file.isEmpty then { e.pos with file } else e.pos
  match e with
  | .decl _ _ ty _ _ => ty.forM (checkTy p)
  | .construct _ _ args _ => args.forM (checkTy p)
  | .structDef _ params specs fields =>
    checkData p "struct" specs
    checkTParams params
    for f in fields do
      checkTy p f.ty
      f.default.forM (checkExpr · p.file)
  | .refineDef _ _ base conditions => do
    checkTy p base
    conditions.forM (checkExpr · p.file)
  | .typeAlias _ params ty => do
    checkTParams params
    checkTy p ty
  | _ => pure ()
  e.children.forM (checkExpr · p.file)

partial def checkTop (top : STop) (owner : String := "") : Except String Unit := do
  match top with
  | .fn p name params tparams specs ret body =>
    checkSpecs p (owner ++ name) specs
    checkTParams tparams
    UpperBounds.checkDetermined (owner ++ name) params tparams ret
    for param in params do
      checkTy p param.ty
      param.default.forM (checkExpr · p.file)
    checkTy p ret
    checkExpr body p.file
  | .const p _ _ ty value => do
    ty.forM (checkTy p)
    checkExpr value p.file
  | .classDef p name _ tparams specs parents _ fields methods =>
    checkData p "class/interface" specs
    checkTParams tparams
    parents.forM (checkTy p)
    for f in fields do
      checkTy p f.ty
      f.default.forM (checkExpr · p.file)
    methods.forM (checkTop · (name ++ "."))

/-- The places of the specifiers the source keeps (`checkPlace`): of its
    functions, methods, classes, interfaces and structs; and what `<final>`
    and `<concrete>` require there: a `<final>` method's body, and a default
    for each field of a `<concrete>` struct. -/
def checkPlaces (tops : List STop) : Except String Unit := do
  let method (p : Pos) (name : String) (specs : List String) : Except String Unit := do
    checkPlace p .method specs
    checkOverrideAccess p name specs []
    if specs.contains "final" && specs.contains "$abstract" then
      reject p "a <final> method needs a body: it cannot be given one elsewhere"
  for top in tops do
    match top with
    | .fn p _ _ _ specs .. => checkPlace p .function specs
    | .classDef p n _ _ specs _ isI _ methods =>
      checkPlace p (if isI then .interfaceType else .classType) specs
      -- (`C{}` constructs a `<concrete>` class, and nothing an `<abstract>` one)
      if specs.contains "abstract" && specs.contains "concrete" then
        reject p s!"{n} cannot be both <abstract> and <concrete>: a concrete class is constructed with {n}\{}, an abstract one never"
      for m in methods do
        if let .fn mp mn _ _ mspecs .. := m then method mp mn mspecs

    | .const p n _ _ (.structDef _ _ specs fields) =>
      checkPlace p .structType specs
      if specs.contains "concrete" then
        if let some f := fields.find? (·.default.isNone) then
          reject p s!"{n} is <concrete>, so its field '{f.name}' needs a default"

    | .const .. => pure ()

/-- Check every loaded definition, including unused imports, before a source
    annotation can be erased or normalized into generated helper signatures. -/
def check (tops : List STop) (entry : Option SExpr := none) : Except String Unit := do
  tops.forM (checkTop ·)
  entry.forM (checkExpr ·)

end OpenVerse.Front.EffectPolicy
