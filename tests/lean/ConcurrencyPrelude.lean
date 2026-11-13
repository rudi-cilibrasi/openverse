import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private def need (label : String) (x : Except String α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{label}: {e}")

private def report (label : String) (x : Except String α) : IO Unit := do
  discard <| need label x

private def refusal (label needle : String) (x : Except String α) : IO Unit :=
  match x with
  | .error e => unless (e.splitOn needle).length > 1 do
      throw (IO.userError s!"{label}: wrong diagnostic: {e}")
  | .ok _ => throw (IO.userError s!"{label}: unsupported source was accepted")

def main : IO Unit := do
  let src := "Main():void={}"
  let tops ← need "parse" (parseProgram src)
  let p : Pos := { line := 11, col := 3, file := "api-availability.verse" }
  let et := STy.app "event" [.name "int"]
  let ec := SExpr.construct p "event" [.name "int"] []
  let opts : Options := { entry := some ec }
  report "compile entry" (compile src opts)
  report "compileChecked entry" (compileChecked src opts)
  report "elabProgram entry" (elabProgram tops opts)
  report "elabProgramCore entry" (elabProgramCore tops opts)
  report "compileWith entry" (compileWith src [] (some "event(int){}"))
  report "compileTops entry" (compileTops tops [] false (some "event(int){}"))
  let letBody := SExpr.decl p "E" (some et) false ec
  let extra := STop.fn p "$apiExtra" [] [] [] et ec
  let stage : Choice.FirstLift := {
    stageOnly := true, key := "api-stage", pos := p, name := "$apiStage", params := [], specs := [],
    ret := .name "void", body := .tuple p [], binds := [], sets := [], args := [], extraFns := [extra] }
  report "materialized loop extra function" (elabProgramCore tops { requests := { loops := [stage] } })
  let request : Choice.FirstLift := { stage with stageOnly := false, name := "$apiFirst", ret := et, body := ec, extraFns := [] }
  report "materialized loop function" (elabProgramCore tops { requests := { loops := [request] } })
  let framed := STop.const p "$apiPacket" [] none (.structDef p [] [] [{ name := "E", ty := .opt et, default := some (.ident p "false") }])
  report "materialized loop data field" (elabProgramCore tops { requests := { loops := [{stage with extraFns := [framed]}] } })
  let lift : Refine.Lift := {
    pos := p, bound := "D", target := "holder", name := "$apiCast", params := [], tparams := [],
    specs := [], ret := et, subst := [], body := some ec }
  let cls ← need "holder parse" (parseProgram "holder:=class{}\nMain():void={}")
  report "materialized refining function" (elabProgramCore cls { requests := { casts := [lift] } })
  let generic ← need "Id parse" (parseProgram "Id(X:t where t:type):t=X\nMain():void={}")
  report "fnRequests nested event" (elabProgramCore generic { requests := {
    fns := [("Id", .struct "$fn1" [.struct "event" [.int], .struct "event" [.int]])] } })
  let genericHolder ← need "generic holder parse" (parseProgram "holder(t:type):=class{V:t;Get():t=V}\nMain():void={}")
  let mr : FnValues.MethodRequest := {
    key := "api-method", pos := p, owner := "holder", method := "Get", tparams := [],
    receiver := .app "holder" [et], params := [], effs := [], ret := et, args := [], decides := false }
  report "methodRequests receiver/result event" (elabProgramCore genericHolder { requests := { methods := [mr] } })
  let defaultParam : SParam := {
    name := "X", ty := .name "int", named := true,
    default := some (.block p [letBody, .int p 7]) }
  let defaultFn := STop.fn p "Unused" [defaultParam] [] [] (.name "int") (.int p 1)
  report "AST parameter default event" (elabProgramCore (defaultFn :: tops))
  refusal "API user choice profile" "--no-choice excludes" (compileWith src [] (some "1|2") .choiceFree)
  refusal "API unsupported effects before availability" "<predicts>" (elabProgramCore tops { requests := {
    loops := [{request with specs := ["predicts"]}] } })
  let badEntry := SExpr.decl p "F" (some (.fn [] ["predicts"] et)) false (.ident p "Missing")
  refusal "API entry unsupported effects" "<predicts>" (elabProgramCore tops { entry := some badEntry })
  -- A materialized internal task dependency must retain its builtin
  -- identity even when source owns the public task name.
  let ownTask ← need "own task" (parseProgram "task(t:type):=class{Own:int=8}\nMain():void={}")
  let internalTask : Choice.FirstLift := { stage with
    stageOnly := false, name := "$privateTask", ret := .app "$task" [.name "int"],
    body := .construct p "$task" [.name "int"] [], extraFns := [] }
  report "selected builtin identity in request" (elabProgramCore ownTask { requests := { loops := [internalTask] } })
  IO.println "concurrency-prelude compiler API contracts passed (17 checks)"
