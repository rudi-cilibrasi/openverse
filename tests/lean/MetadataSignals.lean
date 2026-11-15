import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private def functionTy := "type{_()<computes>:int}"
private def header : String :=
  s!"Caller(E:event(int),F:{functionTy},Dummy:{functionTy})<suspends>:int=\n"
private def setup (awaitExpr : String := "E.Await()") : String :=
  s!"    var Stored:{functionTy}=Dummy\n    branch:\n        {awaitExpr}\n        set Stored=Dummy\n    set Stored=F\n"

private def refusals : List (String × String) := [
  ("Signal resumes a pending metadata writer", header ++ setup ++
    "    E.Signal(0)\n    Stored()"),
  ("Signal through an immutable event alias", header ++ setup ++
    "    Alias:=E\n    Alias.Signal(0)\n    Stored()"),
  ("Signal through a generic event alias helper",
    "Identity(X:t where t:type):t=X\n" ++ header ++ setup ++
    "    Identity(E).Signal(0)\n    Stored()"),
  ("Signal in a nonwaiting helper",
    "Send(E:event(int)):void=E.Signal(0)\n" ++ header ++ setup ++
    "    Send(E)\n    Stored()"),
  ("Await in a helper retains its event",
    "Wait(E:event(int))<suspends>:void=\n    E.Await()\n" ++ header ++ setup "Wait(E)" ++
    "    E.Signal(0)\n    Stored()"),
  ("Signal in a successful condition", header ++ setup ++
    "    if(E.Signal(0);true?){}\n    Stored()"),
  ("Rollback restores a waiting callback", header ++ setup ++
    "    if(E.Signal(0);false?){}\n    E.Signal(0)\n    Stored()"),
  ("Signal in cancellation cleanup", header ++ setup ++
    "    V:=race:\n        block:\n            defer:\n                E.Signal(0)\n            loop{Sleep(1.0)}\n        block:\n            Sleep(0.1)\n            0\n    Stored()"),
  ("Owner return cleanup signals a living branch", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        E.Await()\n        Value:=Stored()\n    branch:\n        defer:\n            E.Signal(0)\n        loop\{Sleep(1.0)}\n    0"),
  ("Distinct event parameters may alias",
    (header.replace "Caller(" "Caller(Other:event(int),") ++ setup ++
    "    Other.Signal(0)\n    Stored()")]

private def controls : List (String × String) := [
  ("Signal cannot wake a timer", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        Sleep(0.1)\n        set Stored=Dummy\n    set Stored=F\n    E.Signal(0)\n    Stored()"),
  ("A fresh unrelated event cannot wake this branch", header ++ setup ++
    "    Other:=event(int){}\n    Other.Signal(0)\n    Stored()"),
  ("Fresh events remain distinct through aliases", header ++
    "    Other:=event(int){}\n    Alias:=Other\n" ++ setup ++
    "    Alias.Signal(0)\n    Stored()"),
  ("A failed condition rolls back callback writes", header ++ setup ++
    "    if(E.Signal(0);false?){}\n    Stored()"),
  ("Signal cannot skip a helper's initial timer",
    "Wait(E:event(int))<suspends>:void=\n    Sleep(0.1)\n    E.Await()\n" ++ header ++ setup "Wait(E)" ++
    "    E.Signal(0)\n    Stored()"),
  ("Completed callbacks cannot run again", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        E.Await()\n        set Stored=Dummy\n    E.Signal(0)\n    set Stored=F\n    E.Signal(0)\n    Stored()"),
  ("Canceled listeners cannot be woken by later cleanup", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        defer:\n            E.Signal(0)\n        loop\{Sleep(1.0)}\n    branch:\n        E.Await()\n        Value:=Stored()\n    0"),
  ("Awaiter registration order makes the later read real", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        E.Await()\n        set Stored=F\n    branch:\n        E.Await()\n        Value:=Stored()\n    E.Signal(0)\n    0")]

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
  if failures > 0 then throw (IO.userError s!"{failures} metadata Signal contracts failed")
  IO.println s!"metadata Signal contracts passed ({refusals.length} real/dummy refusals, {controls.length} forwarding/overwrite pairs)"
