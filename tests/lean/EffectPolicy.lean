import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private def expectError (label needle : String) (result : Except String α) : IO Unit :=
  match result with
  | .error message =>
    unless (message.splitOn needle).length > 1 do
      throw (IO.userError s!"{label}: wrong diagnostic: {message}")
  | .ok _ => throw (IO.userError s!"{label}: unsupported effect was accepted")

private def requireOK (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok result => pure result
  | .error message => throw (IO.userError s!"{label}: {message}")

def main : IO Unit := do
  let source := "Bad()<predicts>:int=1\nMain():void={}"
  expectError "compile" "<predicts>" (compile source)
  expectError "checked" "<predicts>" (compileChecked source)
  expectError "compileWith" "<predicts>" (compileWith source [] none)
  let tops ← requireOK "parse" (parseProgram source)
  expectError "compileTops" "<predicts>" (compileTops tops [] false none)
  expectError "elabProgram" "<predicts>" (elabProgram tops)
  expectError "elabProgramCore" "<predicts>" (elabProgramCore tops)
  expectError "choice-free mode" "<predicts>" (compile source { profile := .choiceFree })

  let p : Pos := { line := 12, col := 7, file := "api.verse" }
  let main := STop.fn p "Main" [] [] [] (.name "void") (.tuple p [])
  let bad := STy.fn [] ["converges"] (.name "int")
  let defaultParam : SParam := {
    name := "X", ty := .name "int",
    default := some (.decl p "F" (some bad) false (.ident p "Never")) }
  -- This bypasses parsing, and exercises types/defaults which generic child
  -- visitors treat as leaves. Refusals must occur before unrelated typing.
  let places : List STop := [
    .const p "Unused" [] (some (.arr bad)) (.arrayLit p []),
    .const p "Packet" [] none (.structDef p [] [] [{ name := "F", ty := bad }]),
    .const p "Refined" [] none (.refineDef p "X" (.name "int")
      [.decl p "F" (some bad) false (.ident p "Never")]),
    .fn p "Unused" [defaultParam] [] [] (.name "int") (.int p 1),
    .classDef p "Unused" [] [] [] [] false [{ name := "F", ty := bad }] [],
    .classDef p "Unused" [] [] [] [] true []
      [.fn p "Get" [] [] ["$abstract"] bad (.tuple p [])]]
  for (top, i) in places.zipIdx do
    expectError s!"AST place {i}" "api.verse:12:7" (elabProgramCore [top, main])
    expectError s!"AST effect {i}" "<converges>" (elabProgramCore [top, main])
  let entry := SExpr.decl p "F" (some bad) false (.ident p "Never")
  expectError "AST entry" "<converges>" (elabProgramCore [main] { entry := some entry })

  -- Generated requests are checked before FnValues.desugar can normalize
  -- away unrepresented effects, even if a caller constructed Options directly.
  expectError "function request" "<predicts>" (elabProgramCore [main]
    { requests := { fns := [("Missing", .struct "$fn0:predicts" [.int])] } })
  let request : FnValues.MethodRequest := {
    key := "api-method", pos := p, owner := "Unused", method := "Get", tparams := [],
    receiver := .name "Unused", params := [], effs := ["predicts"], ret := .name "int",
    args := [], decides := false }
  expectError "method request" "<predicts>" (elabProgramCore [main] { requests := { methods := [request] } })

  -- Diagnostics, rather than a fake proof or a normalization, cover every
  -- unsupported family. Supported combinations still compile normally.
  for spec in ["converges", "predicts", "native", "native_callable", "no_rollback",
      "dictates", "diverges", "succeeds", "fails", "varies", "fictional_effect"] do
    expectError s!"specifier {spec}" s!"<{spec}>"
      (elabProgramCore [.fn p "Main" [] [] [spec] (.name "void") (.tuple p [])])
  for specs in [["reads", "reads"], ["computes", "computes"], ["decides", "decides"],
      ["suspends", "suspends"]] do
    expectError "duplicate" "duplicate effect specifier"
      (elabProgramCore [.fn p "Main" [] [] specs (.name "void") (.tuple p [])])
  let _ ← requireOK "supported" (compile
    "F(X:int)<computes>:int=X+1\nMain():void=Print(\"{F(3)}\")")
  let construction := "cell:=class<computes>{var N:int=0}\nMain():void={}"
  expectError "construction compile" "construction of cell" (compile construction)
  expectError "construction checked" "construction of cell" (compileChecked construction)
  expectError "construction with" "construction of cell" (compileWith construction [] none)
  let constructionTops ← requireOK "construction parse" (parseProgram construction)
  expectError "construction tops" "construction of cell" (compileTops constructionTops [] false none)
  expectError "construction program" "construction of cell" (elabProgram constructionTops)
  expectError "construction core" "construction of cell" (elabProgramCore constructionTops)
  for effect in ["decides", "suspends"] do
    expectError "AST data effect" s!"<{effect}> is not allowed"
      (elabProgramCore [.const p "Packet" [] none (.structDef p [] [effect] []), main])
  let packet := STop.const p "Packet" [] none (.structDef p [] ["computes"] [])
  let usePacket := STop.fn p "Use" [] [] ["computes"] (.name "Packet")
    (.construct p "Packet" [] [])
  let _ ← requireOK "AST pure struct" (elabProgramCore [packet, usePacket, main])
  expectError "AST default construction budget" "declared construction budget"
    (elabProgramCore [STop.const p "Packet" [] none (.structDef p [] [] []), usePacket, main])
  let materializedCell (specs : List String) := STop.classDef p "Cell" [] [] specs [] false
    [{ name := "N", ty := .name "int", default := some (.int p 0), isVar := true }] []

  let stage (specs : List String) : Choice.FirstLift :=
    { (default : Choice.FirstLift) with
        stageOnly := true, key := "api-stage", name := "$stage", pos := p,
        extraFns := [materializedCell specs] }
  expectError "materialized data budget" "construction of Cell"
    (elabProgramCore [main] { requests := { loops := [stage ["computes"]] } })
  let _ ← requireOK "materialized allocating budget"
    (elabProgramCore [main] { requests := { loops := [stage ["allocates"]] } })
  IO.println "effect admission compiler API contracts passed"
