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
  -- (#724) a data member's definition calls no function of the program's:
  -- refused as the default is elaborated (Epic's 3582), before #511's check
  let divergent := "calls Helper, which might not complete"
  refused "compile" divergent (compile source)
  refused "checked" divergent (compileChecked source)
  refused "with" divergent (compileWith source [] none)
  refused "tops" divergent (compileTops tops [] false none)
  refused "program" divergent (elabProgram tops)
  refused "core" divergent (elabProgramCore tops)
  refused "choice-free" divergent (compile source { profile := .choiceFree })
  checked "explicit extension" (compileChecked source { extendedDefaults := true })
  checked "explicit extension core" (elabProgramCore tops { extendedDefaults := true })
  let indirect := "Helper()<computes>:int=42\nF:type{_()<computes>:int}=Helper\nc:=class<computes>{N:int=F()}\nMain():void={}"
  let indirectTops ← match parseProgram indirect with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  let valueCall := "which might not complete"
  refused "indirect checked" valueCall (compileChecked indirect)
  refused "indirect with" valueCall (compileWith indirect [] none)
  refused "indirect tops" valueCall (compileTops indirectTops [] false none)
  -- The low-level discovery API may return a request instead of a program;
  -- it must not return a completed program with an unchecked indirect call.
  match elabProgramCore indirectTops with
  | .error e => unless (e.splitOn valueCall).length > 1 do
      throw (IO.userError s!"indirect core: {e}")
  | .ok c => unless !c.needs.fns.isEmpty || !c.needs.methods.isEmpty || !c.needs.loops.isEmpty do
      throw (IO.userError "indirect core: completed without convergence admission")

  let p : Pos := { line := 8, col := 3, file := "initializer-api.verse" }
  let helper := STop.fn p "Helper" [] [] ["computes"] (.name "int") (.int p 42)
  let main := STop.fn p "Main" [] [] [] (.name "void") (.tuple p [])
  let packet (target : String) := STop.const p "Packet" [] none
    (.structDef p [] [] [{ name := "N", ty := .name "int", default := some (.app p (.ident p target) [] false) }])
  refused "raw AST" "initializer-api.verse:8:3" (elabProgramCore [helper, packet "Helper", main])
  let request (extra : List STop) : Choice.FirstLift :=
    { (default : Choice.FirstLift) with
        stageOnly := true, key := "initializer-api", name := "$stage", pos := p, extraFns := extra }
  refused "request field" divergent
    (elabProgramCore [helper, main] { requests := { loops := [request [packet "Helper"]] } })
  let forwarding := STop.fn p "$forward" [] [] ["computes"] (.name "int")
    (.app p (.ident p "Helper") [] false)
  refused "request forwarding" "requires convergence"
    (elabProgramCore [helper, packet "$forward", main] { requests := { loops := [request [forwarding]] } })
  let cyclic := STop.fn p "$cycle" [] [] ["computes"] (.name "int")
    (.app p (.ident p "$cycle") [] false)
  refused "request recursion" "recursive helper"
    (elabProgramCore [packet "$cycle", main] { requests := { loops := [request [cyclic]] } })
  let fakeBlock := STop.fn p "fake.$block" [] [] ["computes"] (.name "int") (.int p 42)
  refused "ordinary block spelling" "of Packet calls fake"
    (elabProgramCore [fakeBlock, packet "fake.$block", main])
  for extended in [false, true] do
    refused "heap remains checked" "construction of cell"
      (compile "cell:=class<computes>{var N:int=0}\nMain():void={}"
        { extendedDefaults := extended })
    refused "explicit converges stays unsupported" "<converges>"
      (compile "F()<converges>:int=42\nMain():void={}"
        { extendedDefaults := extended })
  IO.println "initializer convergence compiler API contracts passed"
