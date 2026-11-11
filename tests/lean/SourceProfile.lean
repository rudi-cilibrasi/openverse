import OpenVerse.Front.Elab
import OpenVerse.Core.Encode

open OpenVerse.Front

def expectProfileError (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .error message => do
    if (message.splitOn "--no-choice excludes").length ≤ 1 then
      throw (IO.userError s!"{label}: unexpected diagnostic: {message}")
  | .ok _ => throw (IO.userError s!"{label}: excluded source was accepted")

def requireOK (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{label}: {message}")

def main : IO Unit := do
  let source := "Pick():int=1|2\nMain():void=if(X:=Pick())then Print(\"{X}\")"
  let _ ← requireOK "default profile" (compile source)
  expectProfileError "compile" (compile source { profile := .choiceFree })
  expectProfileError "compileChecked" (compileChecked source { profile := .choiceFree })
  expectProfileError "compileWith" (compileWith source [] none .choiceFree)
  let tops ← requireOK "parse source" (parseProgram source)
  expectProfileError "compileTops" (compileTops tops [] false none false .choiceFree)
  expectProfileError "elabProgram" (elabProgram tops { profile := .choiceFree })
  let plain := "Main():void=Print(\"ok\")"
  let plainTops ← requireOK "parse plain source" (parseProgram plain)
  let entry ← requireOK "parse entry" (parseExprText "first{1}")
  expectProfileError "explicit entry" (compileChecked plain { profile := .choiceFree, entry := some entry })
  expectProfileError "compileWith entry" (compileWith plain [] (some "1|2") .choiceFree)
  expectProfileError "compileTops entry" (compileTops plainTops [] false (some "1..2") false .choiceFree)
  -- Type-definition children need admission too, before type-specific lowering.
  expectProfileError "refinement conditions" (compile
    "small:=type{_X:int where _X<(1|2)}\nMain():void=Print(\"ok\")"
    { profile := .choiceFree })
  let full ← requireOK "plain normal" (compile plain)
  let strict ← requireOK "plain choice-free" (compile plain { profile := .choiceFree })
  if full.encode != strict.encode then throw (IO.userError "profile changed admitted bytecode")
  IO.println "source-profile compiler API contracts passed"
