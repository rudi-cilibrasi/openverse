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

private def flattenedSignal (arrayExpr : String) (prelude : String := "") : String :=
  prelude ++ header ++ setup ++
  "    Other:=event(int){}\n    Flat:[]event(int)=" ++ arrayExpr ++
  "\n    if(Alias:=Flat[0])then Alias.Signal(0)\n    Stored()"

private def flattenedTask (signal : String) : String :=
  "Work(E:event(int))<suspends>:int=E.Await()\n" ++ header ++
  "    Other:=event(int){}\n    T:=spawn{Work(E)}\n    Tasks:=Concatenate(array{array{T}})\n" ++
  s!"    var Stored:{functionTy}=Dummy\n    if(Alias:=Tasks[0]):\n        branch:\n            Alias.Await()\n            set Stored=Dummy\n        set Stored=F\n        {signal}.Signal(0)\n        Stored()\n    else:\n        0"

private def comparisonWrite (binding : String) (action : String := "set Alias.E=E")
    (helpers : String := "") : String :=
  "holder:=class<unique>{var E:event(int)}\n" ++ helpers ++ header ++ setup ++
  "    Other:=event(int){}\n    H:=holder{E:=Other}\n    K:=holder{E:=E}\n    if(" ++
  binding ++ ")then " ++ action ++ "\n    H.E.Signal(0)\n    Stored()"

private def comparedSignal (op : String) (swap : Bool) : String :=
  ("holder:=class<unique>{E:event(int)}\nSend(A:holder,B:holder,N:int):void=\n    if(N>0)then Send(" ++
    (if swap then "B,A" else "A,B") ++ ",N-1)else:\n        if(Alias:=A" ++ op ++
    (if op == "=" then "A" else "B") ++ ")then Alias.E.Signal(0)\n") ++
  header ++ setup ++ "    Other:=event(int){}\n    H:=holder{E:=Other}\n    K:=holder{E:=E}\n    Send(H,K,1)\n    Stored()"

private def returnedField (helpers : String)
    (action : String := "N:=Change(H,E,true)") (receiver : String := "H") : String :=
  "holder:=class{var E:event(int)}\n" ++ helpers ++ header ++ setup ++
  "    Other:=event(int){}\n    H:=holder{E:=Other}\n    " ++ action ++
  "\n    " ++ receiver ++ ".E.Signal(0)\n    Stored()"

private def earlyChange : String :=
  "Change(H:holder,E:event(int),C:logic)<transacts>:int=\n    if(C?):\n        set H.E=E\n        return 0\n    0\n"

private def moduleField (action : String) : String :=
  "holder:=class{var E:event(int)}\nsession_key:=class<unique><module_scoped_var_weak_map_key>{}\n" ++
  "var Holders:weak_map(session_key,holder)=map{}\n" ++
  "Cache:=module:\n    var NestedHolders<public>:weak_map(session_key,holder)=map{}\n" ++
  "Put(Key:session_key,H:holder)<transacts><decides>:void=set Holders[Key]=H\n" ++
  "Get(Key:session_key)<transacts><decides>:holder=Holders[Key]\n" ++
  "Change(Key:session_key,E:event(int))<transacts><decides>:void=\n    Alias:=Get[Key]\n    set Alias.E=E\n" ++
  (header.replace "Caller(" "Caller(Key:session_key,") ++ setup ++
  "    Other:=event(int){}\n    H:=holder{E:=Other}\n" ++ action ++
  "\n    H.E.Signal(0)\n    Stored()"

private def refusals : List (String × String) := [
  -- (#724) A branch outlives the function that started it, until its task
  -- ends: this listener is no longer canceled when Caller returns, so a
  -- later Signal of E, by Caller's caller, wakes it to execute the dummy (it
  -- was a control).
  ("Listeners outlive their function and can be woken later", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        defer:\n            E.Signal(0)\n        loop\{Sleep(1.0)}\n    branch:\n        E.Await()\n        Value:=Stored()\n    0"),
  ("A module weak map retains a field-write receiver", moduleField
    "    if(set Holders[Key]=H,Alias:=Holders[Key]):\n        set Alias.E=E"),
  ("A helper returns the receiver stored in a module weak map", moduleField
    "    if(Put[Key,H],Alias:=Get[Key]):\n        set Alias.E=E"),
  ("A helper mutates the receiver stored in a module weak map", moduleField
    "    if(Put[Key,H],Change[Key,E]){}"),
  ("A saved module weak-map alias retains its receiver", moduleField
    "    if(set Holders[Key]=H,Alias:=Holders[Key]):\n        Saved:=Alias\n        set Saved.E=E"),
  ("A nested module weak map retains its field-write receiver", moduleField
    "    if(set Cache.NestedHolders[Key]=H,Alias:=Cache.NestedHolders[Key]):\n        set Alias.E=E"),
  ("A committed module alias write follows a rolled-back write", moduleField
    "    if(set Holders[Key]=H,Alias:=Holders[Key]):\n        if(set Alias.E=Other;false?){}\n        set Alias.E=E"),
  ("An early helper return preserves its heap write", returnedField earlyChange),
  ("A return from a loop preserves its heap write", returnedField
    "Change(H:holder,E:event(int),C:logic)<transacts>:int=\n    loop:\n        if(C?):\n            set H.E=E\n            return 0\n        else:\n            break\n    0\n"),
  ("A return from a for preserves its heap write", returnedField
    "Change(H:holder,E:event(int),C:logic)<transacts>:int=\n    for(I:=0..0):\n        set H.E=E\n        return 0\n    0\n"),
  ("A returned receiver retains writes made before returning", returnedField
    "Change(H:holder,E:event(int),C:logic)<transacts>:holder=\n    if(C?):\n        set H.E=E\n        return H\n    H\n"
    (receiver := "N")),
  ("An outer helper preserves an inner return's heap write", returnedField
    (earlyChange.replace "Change(" "Inner(" ++
      "Change(H:holder,E:event(int),C:logic)<transacts>:int=Inner(H,E,C)\n")),
  ("Returning branches join both heap states", returnedField
    "Change(H:holder,E:event(int),C:logic)<transacts>:int=\n    if(C?):\n        set H.E=E\n        return 0\n    else:\n        return 0\n"),
  ("A condition's heap write survives a successful early return", returnedField
    "Change(H:holder,E:event(int),C:logic)<transacts>:int=\n    if(set H.E=E;C?):\n        return 0\n    0\n"),
  ("Field writes through an equality result retain their receiver",
    comparisonWrite "Alias:=H=H"),
  ("Field writes through an inequality result retain their receiver",
    comparisonWrite "Alias:=H<>K"),
  ("Equality returns the array containing the field-write receiver",
    comparisonWrite "Aliases:=array{H}=array{H},Alias:=Aliases[0]"),
  ("Equality returns the tuple containing the field-write receiver",
    comparisonWrite "Pair:=(H,0)=(H,0),Alias:=Pair(0)"),
  ("A generic equality helper preserves the field-write receiver",
    comparisonWrite "Alias:=Same[H]" (helpers :=
      "Same(X:t where t:subtype(comparable))<transacts><decides>:t=X=X\n")),
  ("Recursive equality signals retain argument permutations", comparedSignal "=" true),
  ("Recursive inequality signals retain argument permutations", comparedSignal "<>" true),
  ("Signal follows a flattened event array",
    flattenedSignal "Concatenate(array{array{E}})"),
  ("Signal follows two flattened event layers",
    flattenedSignal "Concatenate(Concatenate(array{array{array{E}}}))"),
  ("Signal follows a generic flattening helper",
    flattenedSignal "FlatEvents(array{array{E}})"
      "FlatEvents(X:[][]t where t:type):[]t=Concatenate(X)\n"),
  ("Event await follows a flattened event array", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        Flat:=Concatenate(array\{array\{E}})\n        if(Alias:=Flat[0]):\n            Alias.Await()\n            set Stored=Dummy\n    set Stored=F\n    E.Signal(0)\n    Stored()"),
  ("Task await follows a flattened task array", flattenedTask "E"),
  ("Ordinary concatenation retains event elements",
    flattenedSignal "Concatenate(array{E},array{Other})"),
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
  ("A module weak-map alias can write an unrelated event", moduleField
    "    if(set Holders[Key]=H,Alias:=Holders[Key]):\n        set Alias.E=Other"),
  ("Rollback restores a module weak-map alias write", moduleField
    "    if(set Holders[Key]=H;Alias:=Holders[Key];set Alias.E=E;false?){}"),
  ("A helper can update an unrelated event through a module weak map", moduleField
    "    if(Put[Key,H],Change[Key,Other]){}"),
  ("A nested module weak-map alias can write an unrelated event", moduleField
    "    if(set Cache.NestedHolders[Key]=H,Alias:=Cache.NestedHolders[Key]):\n        set Alias.E=Other"),
  ("An early return can write an unrelated event", returnedField earlyChange
    "N:=Change(H,Other,true)"),
  ("Rollback restores a returning helper's heap write", returnedField earlyChange
    "if(N:=Change(H,E,true);false?){}"),
  ("Objects allocated on returning paths retain their fields", returnedField
    "Make(C:logic)<transacts>:holder=\n    if(C?):\n        return holder{E:=event(int){}}\n    holder{E:=event(int){}}\n"
    "N:=Make(true)" "N"),
  ("An equality result preserves an unrelated event field",
    comparisonWrite "Alias:=H=H" "Alias.E.Signal(0)"),
  ("An inequality returns only its left receiver",
    comparisonWrite "Alias:=H<>K" "set Alias.E=Other"),
  ("A comparison result mutates only its own fresh object",
    comparisonWrite "Alias:=K=K"),
  ("Rollback restores a field written through a comparison result",
    comparisonWrite "Alias:=H=H;set Alias.E=E;false?" "{}"),
  ("Flattening preserves a fresh unrelated event",
    flattenedSignal "Concatenate(array{array{Other}})"),
  ("Two flattened layers preserve a fresh unrelated event",
    flattenedSignal "Concatenate(Concatenate(array{array{array{Other}}}))"),
  ("A generic flattening helper preserves an unrelated event",
    flattenedSignal "FlatEvents(array{array{Other}})"
      "FlatEvents(X:[][]t where t:type):[]t=Concatenate(X)\n"),
  ("An unrelated Signal cannot finish a flattened task", flattenedTask "Other"),
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
  -- (#515: the cases signal in <transacts> functions and conditions, which
  -- the default admission refuses; these contracts are about metadata
  -- flow, so they compile in the legacy transactional mode, as before)
  elabProgram tops { signalNoRollback := false }

def main : IO Unit := do
  -- Inspect the dependencies on a typed program independently of the
  -- scheduler's conservative writable-recursion heap summary.
  for op in ["=", "<>"] do
    for swap in [false, true] do
      let .ok c := compileCase (comparedSignal op swap) false
        | throw (IO.userError "comparison dependency control failed to compile")
      unless c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
        throw (IO.userError "comparison dependency control failed Core checks")
      let fns := c.prog.fns.toArray
      let some index := fns.findIdx? (·.name == "Send")
        | throw (IO.userError "comparison dependency control lost Send")
      let expected := if swap then [0, 1] else [0]
      unless (MetadataReferences.signalArguments fns)[index]! == expected do
        throw (IO.userError s!"comparison {op}, swap={swap}: wrong Signal dependencies")
  for update in [false, true] do
    let source := if update then
      "Send(Es:[]event(int),I:int,Replacement:event(int),N:int)<transacts>:void=\n    if(N>0):\n        Send(Es,I,Replacement,N-1)\n    else:\n        var Updated:[]event(int)=Es\n        if(set Updated[I]=Replacement,E:=Updated[0])then E.Signal(0)\n"
      else
      "Send(Es:[]event(int),I:int,N:int)<transacts>:void=\n    if(N>0):\n        Send(Es,I,N-1)\n    else:\n        if(E:=Es[I])then E.Signal(0)\n"
    let .ok c := compileCase source false
      | throw (IO.userError "indexed dependency control failed to compile")
    unless c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
      throw (IO.userError "indexed dependency control failed Core checks")
    let fns := c.prog.fns.toArray
    let some index := fns.findIdx? (·.name == "Send")
      | throw (IO.userError "indexed dependency control lost Send")
    let expected := if update then [0, 2] else [0]
    unless (MetadataReferences.signalArguments fns)[index]! == expected do
      throw (IO.userError s!"update={update}: wrong indexed Signal dependencies")
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
