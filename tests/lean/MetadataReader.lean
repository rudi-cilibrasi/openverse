import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private def cases : List (String × String × Bool) := [
  ("recursive producer real overwrite", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\nDigit(N:int)<computes>:int=if(N>0)then (Digit(N-1)|N)else 0\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    branch:\n        Values:=for(A:=(Digit(1)|Digit(1)),B:=(Digit(1)|Digit(1))):\n            E.Await()\n            Stored()\n    set Stored=F\n    E.Signal(0)\n    0\nMain():void={}\n", true),
  ("unoverwritten-metadata", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\nDigit(N:int)<computes>:int=if(N>0)then (Digit(N-1)|N)else 0\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    branch:\n        Values:=for(A:=(Digit(1)|Digit(1)),B:=(Digit(1)|Digit(1))):\n            E.Await()\n            Stored()\n    E.Signal(0)\n    0\nMain():void={}\n", false),
  ("immutable-snapshot-metadata", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\nDigit(N:int)<computes>:int=if(N>0)then (Digit(N-1)|N)else 0\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    Saved:=Stored\n    branch:\n        Values:=for(A:=(Digit(1)|Digit(1)),B:=(Digit(1)|Digit(1))):\n            E.Await()\n            Saved()\n    set Stored=F\n    E.Signal(0)\n    0\nMain():void={}\n", false),
  ("signal-return-positive", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\nWorker(E:event(int))<suspends>:int=E.Await()\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    P:=event(int){}\n    Q:=event(int){}\n    var Alias:event(int)=Q\n    branch:\n        P.Await()\n        set Stored=Dummy\n    E.Signal(0)\n    Q.Signal(0)\n    Stored()\nMain():void={}\n", true),
  ("signal-return-negative", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\nWorker(E:event(int))<suspends>:int=E.Await()\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    P:=event(int){}\n    Q:=event(int){}\n    var Alias:event(int)=Q\n    branch:\n        P.Await()\n        set Stored=Dummy\n    E.Signal(0)\n    P.Signal(0)\n    Stored()\nMain():void={}\n", false),
  ("rollback-query-positive", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\nWorker(E:event(int))<suspends>:int=E.Await()\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    P:=event(int){}\n    Q:=event(int){}\n    var Alias:event(int)=Q\n    branch:\n        P.Await()\n        set Stored=Dummy\n    if(set Alias=P,false?):\n        0\n    Alias.Signal(0)\n    Stored()\nMain():void={}\n", true),
  ("rollback-query-negative", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\nWorker(E:event(int))<suspends>:int=E.Await()\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    P:=event(int){}\n    Q:=event(int){}\n    var Alias:event(int)=Q\n    branch:\n        P.Await()\n        set Stored=Dummy\n    if(set Alias=P,true?):\n        0\n    Alias.Signal(0)\n    Stored()\nMain():void={}\n", false),
  ("spawn-continuation-positive", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\nWorker(E:event(int))<suspends>:int=E.Await()\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    P:=event(int){}\n    Q:=event(int){}\n    var Alias:event(int)=Q\n    branch:\n        P.Await()\n        set Stored=Dummy\n    Task:=spawn{Worker(E)}\n    Q.Signal(0)\n    Stored()\nMain():void={}\n", true),
  ("spawn-continuation-negative", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\nWorker(E:event(int))<suspends>:int=E.Await()\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    P:=event(int){}\n    Q:=event(int){}\n    var Alias:event(int)=Q\n    branch:\n        P.Await()\n        set Stored=Dummy\n    Task:=spawn{Worker(E)}\n    P.Signal(0)\n    Stored()\nMain():void={}\n", false)]

private def compile (source : String) (dummy : Bool) : Except String Compiled := do
  let tops ← parseProgram source
  let tops := tops.map fun
    | .fn p name ps tps specs ret body => .fn p name (ps.map fun param =>
      { param with typeValue := dummy && name == "Caller" && param.name == "Dummy" }) tps specs ret body
    | top => top
  elabProgram tops

def main (args : List String) : IO Unit := do
  if args == ["--count"] then
    IO.println cases.length
    return
  let selected ← match args with
    | [] => pure cases
    | [index] =>
      match index.toNat? >>= fun i => cases[i]? with
      | some spec => pure [spec]
      | none => throw <| IO.userError "invalid metadata reader case"
    | _ => throw <| IO.userError "expected one metadata reader case index"
  for (name, source, metadataAccepted) in selected do
    for dummy in [false,true] do
      let expected := !dummy || metadataAccepted
      match compile source dummy with
      | .ok c =>
        unless expected do throw <| IO.userError s!"{name}: metadata unexpectedly admitted"
        unless c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
          throw <| IO.userError s!"{name}: invalid Core"
      | .error message =>
        if expected || (message.splitOn "dummy type value cannot").length ≤ 1 then
          throw <| IO.userError s!"{name}: unexpected refusal: {message}"
  IO.println s!"metadata reader contracts passed ({selected.length} real/metadata pairs)"
