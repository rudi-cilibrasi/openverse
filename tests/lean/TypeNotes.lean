import OpenVerse.Front.Elab.Statement

open OpenVerse OpenVerse.Front

private def p : Pos := { line := 17, col := 4 }

private def context (selected : Ty) : Ctx := {
  sigs := [], sigProg := { fns := [], main := 0 }
  types := { tvars := [("a", selected), ("b", selected)] }
  locals := [
    { name := "Capture", slot := 3, ty := .arr selected, mutable := true, typeValue := true },
    { name := "Return", slot := 4, ty := .string, mutable := false }] }

private def annotation (name : String) (ty : STy) : SExpr :=
  -- The right-hand side is deliberately invalid: this is a type note,
  -- not a declaration to evaluate or a new binding in the source scope.
  .decl p name (some ty) true (.ident p "ThisMustNeverBeElaborated")

private def note (entries : List SExpr) : SExpr :=
  .app p (.ident p "$noteTypes") (.str p [.text "loop/"] :: entries) false

private def noExpression : Ctx → SExpr → Option Ty → EM R :=
  fun _ _ _ => throw "a type note tried to elaborate a value"

private def need (label : String) (value : Bool) : IO Unit :=
  unless value do throw (IO.userError label)

def main : IO Unit := do
  for selected in [Ty.int, Ty.string, Ty.param "shared" false] do
    let ctx := context selected
    let entries := [SExpr.ident p "Capture", annotation "Return" (.name "b"),
      annotation "Packet" (.tup [.opt (.name "a"), .arr (.name "b")]),
      .ident p "MissingLocal", .decl p "Unannotated" none false (.int p 0)]
    let initial : ESt := { needs := { nested := [("earlier", .name "logic")] } }
    let .ok ((result, after), state) := (elabStmtWith noExpression ctx (note entries) none).run initial
      | throw (IO.userError "type-note elaboration failed")
    need "capture keeps its actual local type"
      (state.needs.nested.lookup "loop/Capture" == some (STy.arr selected.toSTy))
    need "annotation uses the selected type rather than the same-named local"
      (state.needs.nested.lookup "loop/Return" == some selected.toSTy)
    need "compound annotation resolves in the current world"
      (state.needs.nested.lookup "loop/Packet" ==
        some (.tup [.opt selected.toSTy, .arr selected.toSTy]))
    need "earlier requests remain intact" (state.needs.nested.lookup "earlier" == some (.name "logic"))
    need "missing and unannotated entries do not invent types"
      ((state.needs.nested.lookup "loop/MissingLocal").isNone &&
       (state.needs.nested.lookup "loop/Unannotated").isNone)
    let noCode := match result.e with | .lit .void => true | _ => false
    need "notes emit no executable expression" (noCode && result.ty == .void)
    need "notes do not bind locals or alter metadata roles"
      (after.locals.map (fun l => (l.name, l.slot, l.ty, l.mutable, l.typeValue)) ==
       ctx.locals.map (fun l => (l.name, l.slot, l.ty, l.mutable, l.typeValue)))
  match (elabStmtWith noExpression (context .int)
      (note [annotation "Bad" (.name "UnknownType")]) none).run {} with
  | .ok _ => throw (IO.userError "unknown annotation type was admitted")
  | .error message =>
    need "unknown annotation retains its diagnostic" (decide ((message.splitOn "UnknownType").length > 1))
  IO.println "helper type notes passed (selected worlds, annotations, captures, scope and no value evaluation)"
