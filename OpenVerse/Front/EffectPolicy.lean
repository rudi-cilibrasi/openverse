/- Source effect admission before function-value and continuation lowering. -/
import OpenVerse.Front.Syntax

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

/-- Used by the parser at sites where attributes are otherwise discarded. -/
def checkNonFunction (p : Pos) (kind : String) (specs : List String) : Except String Unit := do
  checkUnsupported p specs
  if let some sp := specs.find? effectNames.contains then
    reject p s!"<{sp}> on a {kind} is unsupported: construction/field effect budgets are not enforced (#494)"

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

partial def checkTy (p : Pos) : STy → Except String Unit
  | .name _ => pure ()
  | .arr t | .opt t => checkTy p t
  | .tup ts | .app _ ts => ts.forM (checkTy p)
  | .map k v => do checkTy p k; checkTy p v
  | .fn ps specs ret => do
    checkSpecs p "function type" specs true
    ps.forM (checkTy p)
    checkTy p ret

partial def checkExpr (e : SExpr) (file : String := "") : Except String Unit := do
  let p := if e.pos.file.isEmpty then { e.pos with file } else e.pos
  match e with
  | .decl _ _ ty _ _ => ty.forM (checkTy p)
  | .construct _ _ args _ => args.forM (checkTy p)
  | .structDef _ _ fields =>
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
  | .fn p name params _ specs ret body =>
    checkSpecs p (owner ++ name) specs
    for param in params do
      checkTy p param.ty
      param.default.forM (checkExpr · p.file)
    checkTy p ret
    checkExpr body p.file
  | .const p _ ty value => do
    ty.forM (checkTy p)
    checkExpr value p.file
  | .classDef p name _ specs parents _ fields _ methods =>
    checkNonFunction p "class/interface" specs
    parents.forM (checkTy p)
    for (_, ty, value, _) in fields do
      checkTy p ty
      value.forM (checkExpr · p.file)
    methods.forM (checkTop · (name ++ "."))

/-- Check every loaded definition, including unused imports, before a source
    annotation can be erased or normalized into generated helper signatures. -/
def check (tops : List STop) (entry : Option SExpr := none) : Except String Unit := do
  tops.forM (checkTop ·)
  entry.forM (checkExpr ·)

end OpenVerse.Front.EffectPolicy
