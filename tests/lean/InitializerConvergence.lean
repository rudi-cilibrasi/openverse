import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private def refused (label needle : String) (result : Except String α) : IO Unit := do
  match result with
  | .error e => unless (e.splitOn needle).length > 1 do
      throw (IO.userError s!"{label}: wrong refusal: {e}")
  | .ok _ => throw (IO.userError s!"{label}: convergence boundary was bypassed")

private def checked (label : String) (result : Except String Compiled) : IO Unit := do
  match result with
  | .error e => throw (IO.userError s!"{label}: {e}")
  | .ok c =>
    unless c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
      throw (IO.userError s!"{label}: unchecked Core")

def main : IO Unit := do
  let source := "Helper()<computes>:int=42\nc:=class<computes>{N:int=Helper()}\nMain():void={}"
  let tops ← match parseProgram source with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  refused "compile" "requires convergence" (compile source)
  refused "checked" "requires convergence" (compileChecked source)
  refused "with" "requires convergence" (compileWith source [] none)
  refused "tops" "requires convergence" (compileTops tops [] false none)
  refused "program" "requires convergence" (elabProgram tops)
  refused "core" "requires convergence" (elabProgramCore tops)
  refused "choice-free" "requires convergence" (compile source { profile := .choiceFree })
  checked "explicit extension" (compileChecked source { extendedDefaults := true })
  checked "explicit extension core" (elabProgramCore tops { extendedDefaults := true })
  let indirect := "Helper()<computes>:int=42\nF:type{_()<computes>:int}=Helper\nc:=class<computes>{N:int=F()}\nMain():void={}"
  let indirectTops ← match parseProgram indirect with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  refused "indirect checked" "requires convergence" (compileChecked indirect)
  refused "indirect with" "requires convergence" (compileWith indirect [] none)
  refused "indirect tops" "requires convergence" (compileTops indirectTops [] false none)
  -- The low-level discovery API may return a request instead of a program;
  -- it must not return a completed program with an unchecked indirect call.
  match elabProgramCore indirectTops with
  | .error e => unless (e.splitOn "requires convergence").length > 1 do
      throw (IO.userError s!"indirect core: {e}")
  | .ok c => unless !c.fnNeeds.isEmpty || !c.methodNeeds.isEmpty || !c.loopNeeds.isEmpty do
      throw (IO.userError "indirect core: completed without convergence admission")

  let p : Pos := { line := 8, col := 3, file := "initializer-api.verse" }
  let helper := STop.fn p "Helper" [] [] ["computes"] (.name "int") (.int p 42)
  let main := STop.fn p "Main" [] [] [] (.name "void") (.tuple p [])
  let packet (target : String) := STop.const p "Packet" none
    (.structDef p [] [] [("N", .name "int", some (.app p (.ident p target) [] false), false)])
  refused "raw AST" "initializer-api.verse:8:3" (elabProgramCore [helper, packet "Helper", main])
  let request (extra : List STop) : Choice.FirstLift :=
    { (default : Choice.FirstLift) with
        stageOnly := true, key := "initializer-api", name := "$stage", pos := p, extraFns := extra }
  refused "request field" "requires convergence"
    (elabProgramCore [helper, main] { loopRequests := [request [packet "Helper"]] })
  let forwarding := STop.fn p "$forward" [] [] ["computes"] (.name "int")
    (.app p (.ident p "Helper") [] false)
  refused "request forwarding" "requires convergence"
    (elabProgramCore [helper, packet "$forward", main] { loopRequests := [request [forwarding]] })
  let cyclic := STop.fn p "$cycle" [] [] ["computes"] (.name "int")
    (.app p (.ident p "$cycle") [] false)
  refused "request recursion" "recursive helper"
    (elabProgramCore [packet "$cycle", main] { loopRequests := [request [cyclic]] })
  let fakeBlock := STop.fn p "fake.$block" [] [] ["computes"] (.name "int") (.int p 42)
  refused "ordinary block spelling" "ordinary function"
    (elabProgramCore [fakeBlock, packet "fake.$block", main])
  for extended in [false, true] do
    refused "heap remains checked" "construction of cell"
      (compile "cell:=class<computes>{var N:int=0}\nMain():void={}"
        { extendedDefaults := extended })
    refused "explicit converges stays unsupported" "<converges>"
      (compile "F()<converges>:int=42\nMain():void={}"
        { extendedDefaults := extended })
  IO.println "initializer convergence compiler API contracts passed"
