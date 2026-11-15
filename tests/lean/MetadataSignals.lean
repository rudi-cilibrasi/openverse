import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private def functionTy := "type{_()<computes>:int}"
private def header : String :=
  s!"Caller(E:event(int),F:{functionTy},Dummy:{functionTy})<suspends>:int=\n"
private def setup (awaitExpr : String := "E.Await()") : String :=
  s!"    var Stored:{functionTy}=Dummy\n    branch:\n        {awaitExpr}\n        set Stored=Dummy\n    set Stored=F\n"

private def returningHelper (value : String) : String :=
  s!"Later(V:v,R:v where v:type)<suspends>:v=\n    Value:=race:\n        block:\n            Sleep(0.1)\n            return {value}\n        block:\n            Sleep(0.2)\n            {value}\n    R\n"

private def scheduledCaller (body : String) : String := header ++
  s!"    var Shadow:{functionTy}=Dummy\n    branch:\n        Sleep(1.0)\n        set Shadow=Dummy\n" ++ body

private def loopTasks (signal : String) : String :=
  "Work(E:event(int))<suspends>:int=E.Await()\n" ++ header ++
  s!"    A:=event(int)\{}\n    B:=event(int)\{}\n    Other:=event(int)\{}\n    var Selected:event(int)=A\n    Tasks:=for(N:=0..1):\n        T:=spawn\{Work(Selected)}\n        set Selected=B\n        T\n    var Stored:{functionTy}=Dummy\n    if(T:=Tasks[0]):\n        branch:\n            T.Await()\n            set Stored=Dummy\n        set Stored=F\n        {signal}.Signal(0)\n        Stored()\n    else:\n        0"

private def refusals : List (String × String) := [
  ("Writable recursive helpers can change a stored event alias",
    "holder:=class{var E:event(int)}\nChange(H:holder,E:event(int),N:int)<transacts>:int=if(N>0)then Change(H,E,N-1)else block{set H.E=E;0}\n" ++
    header ++ setup ++
    "    Other:=event(int){}\n    Alias:=holder{E:=Other}\n    N:=Change(Alias,E,1)\n    Alias.E.Signal(N)\n    Stored()"),
  ("Readonly recursive returns can still alias the waiting event",
    "holder:=class{E:event(int)}\nSelect(A:event(int),B:event(int),N:int)<computes>:event(int)=if(N>0)then Select(B,A,N-1)else A\n" ++
    header ++ setup ++
    "    Other:=event(int){}\n    Alias:=holder{E:=Select(Other,E,1)}\n    Alias.E.Signal(0)\n    Stored()"),
  ("An inlined helper arm can return metadata to its caller",
    returningHelper "V" ++ scheduledCaller "    Saved:=Later(Shadow,F)\n    Saved()"),
  ("Returns from every helper arm keep the caller reachable",
    "Later(V:v,R:v where v:type)<suspends>:v=\n    race:\n        block:\n            Sleep(0.1)\n            return R\n        block:\n            Sleep(0.2)\n            return R\n    R\n" ++
    scheduledCaller "    Saved:=Later(Shadow,F)\n    Dummy()"),
  ("A user's Signal method follows its event field",
    "signaler:=class{E:event(int);Signal():void=E.Signal(0)}\n" ++ header ++ setup ++
    "    S:=signaler{E:=E}\n    S.Signal()\n    Stored()"),
  ("An older worker can complete after another start at its spawn site", loopTasks "A"),
  ("Recursive signals retain argument permutations",
    "Send(E:event(int),Other:event(int),N:int):void=\n    if(N>0)then Send(Other,E,N-1)else E.Signal(0)\n" ++
    header ++ setup ++ "    Other:=event(int){}\n    Send(Other,E,1)\n    Stored()"),
  ("Task completion resumes its listener inside Signal",
    "Work(E:sticky_event(task(int)))<suspends>:int=\n    Me:=E.Await()\n    7\n" ++ header ++
    s!"    Handshake:=sticky_event(task(int))\{}\n    T:=spawn\{Work(Handshake)}\n    var Stored:{functionTy}=Dummy\n    branch:\n        T.Await()\n        set Stored=Dummy\n    set Stored=F\n    Handshake.Signal(T)\n    Stored()"),
  ("Failed Signal still cannot reintroduce metadata into a data cell", header ++ setup ++
    "    if(E.Signal(0);false?){}\n    Stored()"),
  ("Signal resumes a pending metadata writer", header ++ setup ++
    "    E.Signal(0)\n    Stored()"),
  ("Signal through an immutable event alias", header ++ setup ++
    "    Alias:=E\n    Alias.Signal(0)\n    Stored()"),
  ("Signal through an event stored in an object field",
    "holder:=class{E:event(int)}\n" ++ header ++ setup ++
    "    Alias:=holder{E:=E}\n    Alias.E.Signal(0)\n    Stored()"),
  ("Signal through an event stored in an array", header ++ setup ++
    "    Aliases:=array{E}\n    if(Alias:=Aliases[0])then Alias.Signal(0)\n    Stored()"),
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
  ("Readonly recursive helpers preserve unrelated stored events",
    "holder:=class{E:event(int)}\nCount(N:int)<computes>:int=if(N>0)then Count(N-1)else 0\n" ++
    header ++ setup ++
    "    Other:=event(int){}\n    Alias:=holder{E:=Other}\n    N:=Count(1)\n    Alias.E.Signal(N)\n    Stored()"),
  ("A nested arm return stops at an already completed rush",
    "Later(V:v,R:v where v:type)<suspends>:v=\n    Release:=event(int){}\n    Never:=event(int){}\n    Value:=rush:\n        block:\n            Inner:=race:\n                block:\n                    Release.Await()\n                    return V\n                block:\n                    Never.Await()\n                    R\n            R\n        block:\n            Sleep(0.0)\n            R\n    Release.Signal(0)\n    R\n" ++
    scheduledCaller "    Saved:=Later(Shadow,F)\n    Saved()"),
  ("A helper's late rush return only stops its background arm",
    "Later(V:v,R:v where v:type)<suspends>:v=\n    Release:=event(int){}\n    Value:=rush:\n        block:\n            Release.Await()\n            return V\n        block:\n            Sleep(0.0)\n            R\n    Release.Signal(0)\n    R\n" ++
    scheduledCaller "    Saved:=Later(Shadow,F)\n    Saved()"),
  ("A source late rush return only stops its background arm",
    (header.replace "<suspends>:int=" s!"<suspends>:{functionTy}=") ++
    "    Value:=rush:\n        block:\n            E.Await()\n            return Dummy\n        block:\n            Sleep(0.0)\n            F\n    E.Signal(0)\n    F\n" ++
    s!"Use(E:event(int),F:{functionTy},D:{functionTy})<suspends>:int=\n    Saved:=Caller(E,F,D)\n    Saved()"),
  ("An inlined helper arm can return real data to its caller",
    returningHelper "R" ++ scheduledCaller "    Saved:=Later(Shadow,F)\n    Saved()"),
  ("A user's Signal method preserves a fresh unrelated event",
    "signaler:=class{E:event(int);Signal():void=E.Signal(0)}\n" ++ header ++ setup ++
    "    Other:=event(int){}\n    S:=signaler{E:=Other}\n    S.Signal()\n    Stored()"),
  ("Repeated workers remain waiting on an unrelated Signal", loopTasks "Other"),
  ("An unrelated Signal cannot finish a waiting worker",
    "Work(E:event(int))<suspends>:int=E.Await()\n" ++ header ++
    s!"    T:=spawn\{Work(E)}\n    var Stored:{functionTy}=Dummy\n    branch:\n        T.Await()\n        set Stored=Dummy\n    set Stored=F\n    Other:=event(int)\{}\n    Other.Signal(0)\n    Stored()"),
  ("Signal cannot complete a worker's timer",
    "Work()<suspends>:int=block{Sleep(0.1);7}\n" ++ header ++
    s!"    T:=spawn\{Work()}\n    var Stored:{functionTy}=Dummy\n    branch:\n        T.Await()\n        set Stored=Dummy\n    set Stored=F\n    E.Signal(0)\n    Stored()"),
  ("Cancellation does not signal a task's successful completion",
    "Work(E:event(int))<suspends>:int=E.Await()\n" ++ header ++
    s!"    T:=spawn\{Work(E)}\n    var Stored:{functionTy}=Dummy\n    branch:\n        T.Await()\n        set Stored=Dummy\n    set Stored=F\n    T.Cancel()\n    E.Signal(0)\n    Stored()"),
  ("Await of a completed task can return without another wait",
    "Work()<suspends>:int=7\n" ++ header ++
    s!"    T:=spawn\{Work()}\n    var Stored:{functionTy}=Dummy\n    branch:\n        T.Await()\n        set Stored=F\n    Stored()"),
  ("Failed Signal restores an opaque cell's metadata mode",
    (header.replace "<suspends>:int=" s!"<suspends>:{functionTy}=") ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        E.Await()\n        set Stored=F\n    if(E.Signal(0);false?)\{}\n    set Stored=Dummy\n    Stored"),
  ("Failed Signal restores its listener before the next Signal", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        E.Await()\n        set Stored=F\n    if(E.Signal(0);false?)\{}\n    E.Signal(0)\n    Stored()"),
  ("Signal cannot wake a timer", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        Sleep(0.1)\n        set Stored=Dummy\n    set Stored=F\n    E.Signal(0)\n    Stored()"),
  ("A fresh unrelated event cannot wake this branch", header ++ setup ++
    "    Other:=event(int){}\n    Other.Signal(0)\n    Stored()"),
  ("Fresh events remain distinct through aliases", header ++
    "    Other:=event(int){}\n    Alias:=Other\n" ++ setup ++
    "    Alias.Signal(0)\n    Stored()"),
  ("A fresh unrelated event stays distinct through an object field",
    "holder:=class{E:event(int)}\n" ++ header ++ setup ++
    "    Other:=event(int){}\n    Alias:=holder{E:=Other}\n    Alias.E.Signal(0)\n    Stored()"),
  ("A fresh unrelated event stays distinct through an array", header ++ setup ++
    "    Other:=event(int){}\n    Aliases:=array{Other}\n    if(Alias:=Aliases[0])then Alias.Signal(0)\n    Stored()"),
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
