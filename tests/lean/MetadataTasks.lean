import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private def functionTy := "type{_()<computes>:int}"
private def header (ret : String := "int") : String :=
  s!"Caller(F:{functionTy},Dummy:{functionTy})<suspends>:{ret}=\n"
private def keep := "Keep(V:v where v:type)<suspends>:v=block{Sleep(0.1);V}\n"

private def refusals : List (String × String) := [
  ("awaited generic result", keep ++ header ++
    "    T:=spawn{Keep(Dummy)}\n    Saved:=T.Await()\n    Saved()"),
  ("result forwarded through helpers", keep ++
    "Forward(V:v where v:type)<computes>:v=V\n" ++ header ++
    "    T:=spawn{Keep(Forward(Dummy))}\n    Saved:=Forward(T.Await())\n    Saved()"),
  ("aggregate result", "Keep(V:v where v:type)<suspends>:[]v=block{Sleep(0.1);array{V}}\n" ++ header ++
    "    T:=spawn{Keep(Dummy)}\n    Saved:=T.Await()\n    if(Fn:=Saved[0])then Fn() else 0"),
  ("immediate task result", "Keep(V:v where v:type)<suspends>:v=V\n" ++ header ++
    "    T:=spawn{Keep(Dummy)}\n    T.Await()()"),
  -- A task's Result is an ordinary mutable field even without an await.
  ("discarded task still stores its result", keep ++ header "void" ++
    "    spawn{Keep(Dummy)}\n    Sleep(0.2)"),
  ("task factory forwards metadata argument", keep ++
    "Start(V:v where v:type):task(v)=spawn{Keep(V)}\n" ++ header ++
    "    T:=Start(Dummy)\n    T.Await()()"),
  ("spawned generic method result", "worker:=class<computes>:\n    Keep(V:v where v:type)<suspends>:v=block{Sleep(0.1);V}\n" ++ header ++
    "    W:=worker{}\n    T:=spawn{W.Keep(Dummy)}\n    T.Await()()"),
  ("nonreturning task does not hide its caller", "Forever()<suspends>:void=loop{Sleep(0.1)}\n" ++ header ++
    "    spawn{Forever()}\n    Dummy()"),
  ("nonreturning branch does not hide its owner's return", "Finish()<suspends>:void=\n    branch:\n        loop{Sleep(0.1)}\n" ++ header ++
    "    spawn{Finish()}\n    Dummy()"),
  ("nonreturning branch does not hide its owner's wait", "Finish()<suspends>:void=\n    branch:\n        loop{Sleep(0.1)}\n    Sleep(0.2)\n" ++ header ++
    "    spawn{Finish()}\n    Dummy()"),
  ("nonreturning branch does not hide its owner's waiting loop", "Finish()<suspends>:void=\n    branch:\n        loop{Sleep(0.1)}\n    loop{Sleep(0.2)}\n" ++ header ++
    "    spawn{Finish()}\n    Dummy()"),
  ("nonreturning branch helper does not hide its owner", "Forever()<suspends>:void=loop{Sleep(0.1)}\nFinish()<suspends>:void=branch{Forever()}\n" ++ header ++
    "    spawn{Finish()}\n    Dummy()"),
  ("return after nonreturning branch retains metadata result", "Finish(V:v where v:type)<suspends>:v=\n    branch:\n        loop{Sleep(0.1)}\n    V\n" ++ header ++
    "    T:=spawn{Finish(Dummy)}\n    T.Await()()"),
  ("sync with a waiting arm lets its caller continue", "NoWait()<suspends>:void={}\nForever()<suspends>:void=\n    loop:\n        sync:\n            Sleep(0.1)\n            NoWait()\n" ++ header ++
    "    spawn{Forever()}\n    Dummy()")]

private def controls : List (String × String) := [
  ("metadata argument with real result", "Ignore(V:v,R:v where v:type)<suspends>:v=block{Sleep(0.1);R}\n" ++ header ++
    "    T:=spawn{Ignore(Dummy,F)}\n    T.Await()()"),
  ("metadata argument discarded", "Ignore(V:v where v:type)<suspends>:int=block{Sleep(0.1);7}\n" ++ header ++
    "    T:=spawn{Ignore(Dummy)}\n    T.Await()"),
  ("opaque metadata forwarding inside task", "Forward(V:v where v:type)<computes>:v=V\nIgnore(V:v,R:v where v:type)<suspends>:v=block{Saved:=Forward(V);Sleep(0.1);R}\n" ++ header ++
    "    T:=spawn{Ignore(Dummy,F)}\n    T.Await()()"),
  ("nonreturning task with real continuation", "Forever()<suspends>:void=loop{Sleep(0.1)}\n" ++ header ++
    "    spawn{Forever()}\n    F()"),
  ("nonwaiting task cannot reach its caller", "NoWait()<suspends>:void={}\nForever()<suspends>:void=loop{NoWait()}\n" ++ header ++
    "    spawn{Forever()}\n    Dummy()"),
  ("zero sleep cannot reach a nonreturning task's caller", "Forever()<suspends>:void=loop{Sleep(0.0)}\n" ++ header ++
    "    spawn{Forever()}\n    Dummy()"),
  ("negative sleep cannot reach a nonreturning task's caller", "Forever()<suspends>:void=loop{Sleep(-0.1)}\n" ++ header ++
    "    spawn{Forever()}\n    Dummy()"),
  ("error before wait cannot reach its caller", "Never()<suspends>:void=block{Err();Sleep(0.1)}\n" ++ header ++
    "    spawn{Never()}\n    Dummy()"),
  ("nested spawn does not yield its owner", "Pause()<suspends>:void=Sleep(0.1)\nNoWait()<suspends>:void={}\nForever()<suspends>:void=\n    spawn{Pause()}\n    loop{NoWait()}\n" ++ header ++
    "    spawn{Forever()}\n    Dummy()"),
  ("branch does not yield its owner", "NoWait()<suspends>:void={}\nForever()<suspends>:void=\n    branch{Sleep(0.1)}\n    loop{NoWait()}\n" ++ header ++
    "    spawn{Forever()}\n    Dummy()"),
  ("branch that neither returns nor yields holds its owner", "NoWait()<suspends>:void={}\nForever()<suspends>:void=\n    branch:\n        loop{NoWait()}\n" ++ header ++
    "    spawn{Forever()}\n    Dummy()"),
  ("nonreturning branch does not yield its nonwaiting owner", "NoWait()<suspends>:void={}\nForever()<suspends>:void=\n    branch:\n        loop{Sleep(0.1)}\n    loop{NoWait()}\n" ++ header ++
    "    spawn{Forever()}\n    Dummy()"),
  ("return real result after nonreturning branch", "Finish(V:v,R:v where v:type)<suspends>:v=\n    branch:\n        loop{Sleep(0.1)}\n    R\n" ++ header ++
    "    T:=spawn{Finish(Dummy,F)}\n    T.Await()()"),
  ("immediate race winner cannot yield its owner", "NoWait()<suspends>:void={}\nForever()<suspends>:void=\n    loop:\n        race:\n            Sleep(0.1)\n            NoWait()\n" ++ header ++
    "    spawn{Forever()}\n    Dummy()"),
  ("unreachable metadata argument", keep ++ header ++
    "    T:=spawn{Keep(if(false?)then Dummy else F)}\n    T.Await()()"),
  ("spawn arguments overwrite before caller continuation", "Ignore(V:v where v:type)<suspends>:void=block{Sleep(0.1);()}\n" ++ header ++
    s!"    var Stored:{functionTy}=Dummy\n    spawn\{Ignore(block\{set Stored=F;Dummy})}\n    Stored()")]

private def compileCase (source : String) (dummy : Bool) : Except String Compiled := do
  let implementations :=
    s!"One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:{functionTy}=if(C?)then One else Two\n"
  let tops ← parseProgram (implementations ++ source ++ "\nMain():void={}")
  let tops := tops.map fun
    | .fn p name ps tps specs ret body => .fn p name (ps.map fun param =>
        { param with typeValue := dummy && name == "Caller" && param.name == "Dummy" }) tps specs ret body
    | top => top
  elabProgram tops

def main : IO Unit := do
  let mut failures := 0
  for (label, source) in refusals ++ controls do
    for dummy in [false, true] do
      let shouldReject := dummy && refusals.any (·.1 == label)
      match compileCase source dummy with
      | .ok c =>
        if shouldReject || !(c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys) then
          IO.println s!"FAIL {label}, dummy={dummy}: admitted={shouldReject}, Core checks"
          failures := failures + 1
      | .error message =>
        if !shouldReject || (message.splitOn "dummy type value cannot").length ≤ 1 then
          IO.println s!"FAIL {label}, dummy={dummy}: {message}"
          failures := failures + 1
  if failures > 0 then throw (IO.userError s!"{failures} metadata task contracts failed")
  IO.println s!"metadata task contracts passed ({refusals.length} real/dummy refusals, {controls.length} forwarding pairs)"
