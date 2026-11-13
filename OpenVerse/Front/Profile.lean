/- Source-language profiles, checked before compiler-generated lowering. -/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front

/-- Both profiles use the same deterministic execution semantics. -/
inductive SourceProfile where
  | full
  | choiceFree
  deriving BEq, Repr, Inhabited

namespace SourceProfile

def reject (p : Pos) (construct : String) : Except String Unit :=
  .error s!"{p.show}: --no-choice excludes {construct} from the choice-free source profile"

/-- Check source expressions, including definition bodies that `children`
    intentionally treats as leaves. Compiler-generated loops and first-success
    markers are introduced after this check and retain their usual meaning. -/
partial def checkExpr (e : SExpr) (file : String := "") : Except String Unit := do
  -- Loaded .value expressions inherit their file from the enclosing constant.
  let pos := if e.pos.file.isEmpty then { e.pos with file } else e.pos
  match e with
  | .app _ (.ident _ "$choice") _ false => reject pos "choice (|)"
  | .app _ (.ident _ "$first") _ false => reject pos "first-success consumers (first)"
  | .forE .. => reject pos "for consumers (including collection iteration)"
  | .gen .. => reject pos "generator clauses"
  | .range .. => reject pos "ranges"
  | .structDef _ _ _ fields =>
    for f in fields do
      if let some value := f.default then checkExpr value file
  | .refineDef _ _ _ conditions => conditions.forM (checkExpr · file)
  | _ => e.children.forM (checkExpr · file)

partial def checkTop : STop → Except String Unit
  | .fn p _ params _ _ _ body => do
    for param in params do
      if let some value := param.default then checkExpr value p.file
    checkExpr body p.file
  | .const p _ _ _ value => checkExpr value p.file
  | .classDef p _ _ _ _ _ _ fields methods => do
    for f in fields do
      if let some value := f.default then checkExpr value p.file

    methods.forM checkTop

/-- All loaded definitions are admitted, including unused imports. A source
    choice cannot hide behind a call, method, default, or function value. -/
def check (profile : SourceProfile) (tops : List STop) (entry : Option SExpr := none) :
    Except String Unit := do
  if profile == .full then return
  tops.forM checkTop
  if let some entry := entry then checkExpr entry

end SourceProfile
end OpenVerse.Front
