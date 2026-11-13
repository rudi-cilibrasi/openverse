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
  ["public", "internal", "private", "protected", "override", "final", "abstract", "constructor"]

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
  /-- the name of a constant, class, interface, struct, enum or module -/
  | definition
  /-- a function of a module or of the top level: its name or after its parameters -/
  | function
  /-- a method of a class or an interface: its name or after its parameters -/
  | method
  /-- a field's name, in a class, an interface or a struct -/
  | field
  /-- after `class`, `interface` or `struct` -/
  | classType | interfaceType | structType
  deriving BEq, Repr

def Place.what : Place → String
  | .definition => "the name of a constant, type or module"
  | .function => "a module's function"
  | .method => "a method"
  | .field => "a field"
  | .classType => "a class"
  | .interfaceType => "an interface"
  | .structType => "a struct"

/-- The specifiers that say what a declaration is, each with the places it
    may be written; anywhere else it is refused (`checkPlace`), as the Book of
    Verse's tests do (`Tests/Attributes/`, `Castable.versetest`; ch. 10: only
    a class may be `<abstract>`, ch. 17: `<persistable>` classes and structs).
    What each requires of what it is on is checked where that is known:
    `<final>` a member's body or value (`checkField`, `checkPlaces`);
    `<concrete>` a default for every field (a struct's in `checkPlaces`, a
    class's with its inherited fields, `classFields`); `<castable>` and
    `<final_super_base>` of the classes below (`classHierarchy`). Enums take
    `<open>`, `<closed>` and `<persistable>` (the parser's check); access
    specifiers are accepted where the parser takes them (LANGUAGE.md,
    Readings), and effects are `checkSpecs`'. -/
def specifierPlaces : List (String × List Place) :=
  [("abstract", [.classType]),
   ("concrete", [.classType, .structType]),
   ("final", [.classType, .method, .field]),
   ("final_super", [.classType]),
   ("final_super_base", [.classType, .interfaceType]),
   ("castable", [.classType, .interfaceType]),
   ("unique", [.classType, .interfaceType]),
   ("persistable", [.classType, .structType]),
   ("override", [.method, .field])]

/-- Each specifier of `specifierPlaces` in `specs`, written at `place`, is
    one of its places. -/
def checkPlace (p : Pos) (place : Place) (specs : List String) : Except String Unit := do
  for sp in specs do
    if let some places := specifierPlaces.lookup sp then
      if !places.contains place then
        reject p s!"<{sp}> is not allowed on {place.what}: it is for {" or ".intercalate (places.map (·.what))}"

/-- Used by the parser at sites where attributes are otherwise discarded: a
    field's name (`kind` "field") or a definition's. -/
def checkNonFunction (p : Pos) (kind : String) (specs : List String) : Except String Unit := do
  checkUnsupported p specs
  if let some sp := specs.find? effectNames.contains then
    reject p s!"<{sp}> on a {kind} is unsupported: effect specifiers are not supported at this declaration position (#494)"
  checkPlace p (if kind == "field" then .field else .definition) specs

/-- The specifiers of a definition's name, which the parser then discards: a
    constant's, class's, interface's, struct's or enum's. -/
def checkName (p : Pos) (specs : List String) : Except String Unit := do
  checkUnsupported p specs
  checkPlace p .definition specs

/-- A field's specifiers, the parser's to check as it discards them: a
    `<final>` field cannot be given another value, so it needs one
    (`hasValue`). -/
def checkField (p : Pos) (specs : List String) (hasValue : Bool) : Except String Unit := do
  checkNonFunction p "field" specs
  if specs.contains "final" && !hasValue then
    reject p "a <final> field needs a value: it cannot be given one elsewhere"

/-- Declaration metadata is separate from effects; its existing access and
    override semantics remain the elaborator's responsibility. Compiler-only
    markers cannot be written by the source lexer. -/
def checkSpecs (p : Pos) (subject : String) (specs : List String)
    (typeOnly : Bool := false) : Except String Unit := do
  -- Retain the established exclusive-effect diagnostic for declarations.
  if (["converges", "computes", "transacts"].filter specs.contains).length > 1 then
    reject p s!"{subject} has more than one of <converges>, <computes> and <transacts> (they exclude each other)"
  if specs.contains "computes" && ["transacts", "reads", "writes", "allocates"].any specs.contains then
    reject p s!"<computes> excludes the heap effects (<reads>, <writes>, <allocates>, <transacts>) that {subject} also has"
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
    if !typeOnly && (metadata.contains sp || sp.startsWith "$") then continue
    reject p s!"unknown or unsupported {if typeOnly then "function-type effect" else "function specifier"} <{sp}> on {subject} (#494)"

/-- Construction has the same heap family as functions, but is immediate and
    cannot declare failure. Declaration metadata retains its separate meaning. -/
def checkData (p : Pos) (kind : String) (specs : List String) : Except String Unit := do
  checkUnsupported p specs
  checkSpecs p kind (specs.filter effectNames.contains)
  for sp in ["decides", "suspends"] do
    if specs.contains sp then reject p s!"<{sp}> is not allowed on a {kind}: construction effects are heap effects"

/-- No heap specifier means transacts, also for data types (pinned
    Tests/Effects.versetest). Metadata does not change that default. -/
def constructionFx (specs : List String) : List String :=
  let heap := ["reads", "writes", "allocates"]
  if specs.contains "computes" then []
  else if specs.contains "transacts" || !(heap.any specs.contains) then heap
  else heap.filter specs.contains

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
  UpperBounds.checkParams params

partial def checkExpr (e : SExpr) (file : String := "") : Except String Unit := do
  let p := if e.pos.file.isEmpty then { e.pos with file } else e.pos
  match e with
  | .decl _ _ ty _ _ => ty.forM (checkTy p)
  | .construct _ _ args _ => args.forM (checkTy p)
  | .structDef _ params specs fields =>
    checkData p "struct" specs
    checkTParams params
    for (_, ty, value, _) in fields do
      checkTy p ty
      value.forM (checkExpr · p.file)
  | .refineDef _ _ base conditions => do
    checkTy p base
    conditions.forM (checkExpr · p.file)
  | _ => pure ()
  e.children.forM (checkExpr · p.file)

partial def checkTop (top : STop) (owner : String := "") : Except String Unit := do
  match top with
  | .fn p name params tparams specs ret body =>
    checkSpecs p (owner ++ name) specs
    checkTParams tparams
    for param in params do
      checkTy p param.ty
      param.default.forM (checkExpr · p.file)
    checkTy p ret
    checkExpr body p.file
  | .const p _ ty value => do
    ty.forM (checkTy p)
    checkExpr value p.file
  | .classDef p name tparams specs parents _ fields _ methods =>
    checkData p "class/interface" specs
    checkTParams tparams
    parents.forM (checkTy p)
    for (_, ty, value, _) in fields do
      checkTy p ty
      value.forM (checkExpr · p.file)
    methods.forM (checkTop · (name ++ "."))

/-- The places of the specifiers the source keeps (`checkPlace`): of its
    functions, methods, classes, interfaces and structs; and what `<final>`
    and `<concrete>` require there: a `<final>` method's body, and a default
    for each field of a `<concrete>` struct. -/
def checkPlaces (tops : List STop) : Except String Unit := do
  let method (p : Pos) (specs : List String) : Except String Unit := do
    checkPlace p .method specs
    if specs.contains "final" && specs.contains "$abstract" then
      reject p "a <final> method needs a body: it cannot be given one elsewhere"
  for top in tops do
    match top with
    | .fn p _ _ _ specs .. => checkPlace p .function specs
    | .classDef p _ _ specs _ isI _ _ methods =>
      checkPlace p (if isI then .interfaceType else .classType) specs
      for m in methods do
        if let .fn mp _ _ _ mspecs .. := m then method mp mspecs
    | .const p n _ (.structDef _ _ specs fields) =>
      checkPlace p .structType specs
      if specs.contains "concrete" then
        if let some (f, _) := fields.find? (·.2.2.1.isNone) then
          reject p s!"{n} is <concrete>, so its field '{f}' needs a default"
    | .const .. => pure ()

/-- Check every loaded definition, including unused imports, before a source
    annotation can be erased or normalized into generated helper signatures. -/
def check (tops : List STop) (entry : Option SExpr := none) : Except String Unit := do
  tops.forM (checkTop ·)
  entry.forM (checkExpr ·)

end OpenVerse.Front.EffectPolicy
