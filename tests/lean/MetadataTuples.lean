import OpenVerse.Front.Elab
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode
open OpenVerse OpenVerse.Front

private def fnTy := "type{_()<computes>:int}"
private def sourcePrefix := "One()<computes>:int=1\nTwo()<computes>:int=2\nPair(A:t,B:u where t:type,u:type)<computes>:tuple(t,u)=(A,B)\nId(X:t where t:type)<computes>:t=X\nRec(N:int,A:t,B:u where t:type,u:type)<computes>:tuple(t,u)=if(N>0)then Rec(N-1,A,B)else(A,B)\n"
private def cases : List (String × String × Bool) := [
  ("option-real-column", "    O:=option{(Dummy,F)}\n    if(T:=O?) then T(1)() else 0\n",true),
  ("option-metadata-column", "    O:=option{(Dummy,F)}\n    if(T:=O?) then T(0)() else 0\n",false),
  ("nested-real-column", "    T:=Id(((Dummy,F),F))\n    T(0)(1)()\n",true),
  ("nested-metadata-column", "    T:=Id(((Dummy,F),F))\n    T(0)(0)()\n",false),
  ("nested-option-real-column", "    O:=option{((Dummy,F),F)}\n    if(T:=O?) then T(0)(1)() else 0\n",true),
  ("nested-option-metadata-column", "    O:=option{((Dummy,F),F)}\n    if(T:=O?) then T(0)(0)() else 0\n",false),
  ("literal-real-column", "    T:=(Dummy,F)\n    T(1)()\n",true),
  ("literal-metadata-column", "    T:=(Dummy,F)\n    T(0)()\n",false),
  ("forwarded-real-column", "    T:=Id(Pair(Dummy,F))\n    T(1)()\n",true),
  ("forwarded-metadata-column", "    T:=Id(Pair(Dummy,F))\n    T(0)()\n",false),
  ("recursive-real-column", "    T:=Rec(2,Dummy,F)\n    T(1)()\n",true),
  ("recursive-metadata-column", "    T:=Rec(2,Dummy,F)\n    T(0)()\n",false),
  ("real-overwrite", "    var T:tuple("++fnTy++","++fnTy++")=(Dummy,F)\n    set T=(F,F)\n    T(0)()\n",true),
  ("rollback-metadata-overwrite", "    var T:tuple("++fnTy++","++fnTy++")=(F,F)\n    if(set T=(Dummy,F);false?){}\n    T(0)()\n",true),
  ("saved-metadata-alias", "    var T:tuple("++fnTy++","++fnTy++")=(Dummy,F)\n    Saved:=T\n    set T=(F,F)\n    Saved(0)()\n",false),
  ("branch-join-metadata", "    T:=if(C?)then (Dummy,F)else(F,Dummy)\n    T(1)()\n",false),
  ("unreachable-metadata", "    T:=if(false?)then (Dummy,F)else(F,F)\n    T(0)()\n",true),
  ("same-whole-role-distinct-columns", "    Left:=Id((Dummy,F))\n    Right:=Id((F,Dummy))\n    Left(1)()+Right(0)()\n",true),
  ("same-whole-role-unsafe-column", "    Left:=Id((Dummy,F))\n    Right:=Id((F,Dummy))\n    Left(1)()+Right(1)()\n",false),
  ("unknown-shape-does-not-reuse-known-summary", "    Known:=Id((Dummy,F))\n    Items:=array{(F,Dummy)}\n    if(T:=Items[0]):\n        Unknown:=Id(T)\n        return Unknown(1)()\n    0\n",false)]

private def checkTupleColumns : IO Unit := do
  for (name,body,accepted) in cases do
    let source := sourcePrefix ++ "Caller(F:"++fnTy++",Dummy:"++fnTy++",C:logic)<transacts>:int=\n" ++ body ++ "Main():void=Print(\"{Caller(One,Two,true)}\")\n"
    for dummy in [false,true] do
      let result := do
        let tops ← parseProgram source
        elabProgram (tops.map fun (top : STop) => match top with
          | .fn p n ps ts fx ret body => .fn p n (ps.map fun (parameter : SParam) =>
            { parameter with typeValue := dummy && n == "Caller" && parameter.name == "Dummy" }) ts fx ret body
          | top => top)
      match result with
      | .ok compiled =>
        unless !dummy || accepted do throw <| IO.userError s!"{name}: unsafe metadata admitted"
        unless compiled.prog.check && compiled.prog.checkControl && compiled.prog.checkTypes compiled.sigs compiled.slotTys do
          throw <| IO.userError s!"{name}: invalid Core"
        IO.println s!"PASS {name} dummy={dummy} ADMITTED Core=true"
      | .error error =>
        if !dummy || accepted || (error.splitOn "dummy type value cannot").length ≤ 1 then
          throw <| IO.userError s!"{name} dummy={dummy}: unexpected refusal {error}"
        IO.println s!"PASS {name} dummy={dummy} REFUSED"
  IO.println s!"PASS all {cases.length * 2} tuple-column controls"

/-- The independent oracle is the union of the two source branch masks,
    rather than the compiler's tuple representation or cache entries. -/
private def checkTupleJoins : IO Unit := do
  let tuple (bits : Nat) := "(" ++ String.intercalate "," ((List.range 3).map fun i =>
    if bits.testBit i then "Dummy" else "F") ++ ")"
  let mut checked := 0
  for left in [:8] do
    for right in [:8] do
      for column in [:3] do
        let body := s!"    T0:=if(C?)then {tuple left}else{tuple right}\n    T1:=if(C?)then {tuple right}else{tuple left}\n    L:=Id(T0)\n    R:=Id(T1)\n    L({column})()+R({column})()\n"
        let source := sourcePrefix ++ "Caller(F:"++fnTy++",Dummy:"++fnTy++",C:logic)<transacts>:int=\n" ++ body ++ "Main():void=Print(\"{Caller(One,Two,true)}\")\n"
        for dummy in [false,true] do
          let expected := !dummy || !((left ||| right).testBit column)
          let result := do
            let tops ← parseProgram source
            elabProgram (tops.map fun (top : STop) => match top with
              | .fn p n ps ts fx ret body => .fn p n (ps.map fun (parameter : SParam) =>
                { parameter with typeValue := dummy && n == "Caller" && parameter.name == "Dummy" }) ts fx ret body
              | top => top)
          match result with
          | .ok compiled =>
            unless expected && compiled.prog.check && compiled.prog.checkControl &&
                compiled.prog.checkTypes compiled.sigs compiled.slotTys do
              throw <| IO.userError s!"tuple branch model {left}/{right}/{column}/{dummy}: unexpected admission or invalid Core"
          | .error error =>
            if expected || (error.splitOn "dummy type value cannot").length ≤ 1 then
              throw <| IO.userError s!"tuple branch model {left}/{right}/{column}/{dummy}: {error}"
          checked := checked + 1
  IO.println s!"tuple column branch models passed ({checked} independently classified programs)"

private def checkWaitingTransport (args : List String) : IO Unit := do
  let programs := [
    ("before-wait", "        set Stored=F\n        Sleep(0.001)\n        Stored()\n", true, 1),
    ("after-wait", "        Sleep(0.001)\n        set Stored=F\n        Stored()\n", true, 1),
    ("unoverwritten", "        Sleep(0.001)\n        Stored()\n", false, 2),
    ("independent", "        Sleep(0.001)\n        F()\n", true, 1)]
  for (name, body, metadataAccepted, value) in programs do
    let waitingSource := "One()<computes>:int=1\nTwo()<computes>:int=2\na:=class<computes>{M()<computes>:int=1|2}\nb:=class<computes>{M()<computes>:int=3|4}\nDup(V:t where t:type)<computes>:t=V|V\n" ++
      "Caller(F:"++fnTy++",Dummy:"++fnTy++")<suspends>:[]int=\n    var Stored:"++fnTy++"=Dummy\n    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M()):\n" ++ body ++
      "    Rows\nMain()<suspends>:void=\n    Values:=Caller(One,Two)\n    for(Value:Values):Print(\"{Value}\")\n"
    for dummy in [false,true] do
      let expected := !dummy || metadataAccepted
      let result := do
        let tops ← parseProgram waitingSource
        elabProgram (tops.map fun (top : STop) => match top with
          | .fn p n ps ts fx ret body => .fn p n (ps.map fun (parameter : SParam) =>
            { parameter with typeValue := dummy && n == "Caller" && parameter.name == "Dummy" }) ts fx ret body
          | top => top)
      match result with
      | .ok compiled =>
        unless expected && compiled.prog.check && compiled.prog.checkControl &&
            compiled.prog.checkTypes compiled.sigs compiled.slotTys do
          throw <| IO.userError s!"waiting {name}/{dummy}: unexpected admission or invalid Core"
        let trace := String.join (List.replicate 8 s!"{value}\n")
        match compiled.prog.runB 10000000 10000 with
        | .res (.ok _, output) =>
          unless String.ofList (output.map Char.ofNat) == trace do
            throw <| IO.userError s!"waiting {name}/{dummy}: wrong complete trace"
        | _ => throw <| IO.userError s!"waiting {name}/{dummy}: VM failure"
        if let [out] := args then
          let artifact := s!"{out}/waiting-tuple-{name}-{dummy}"
          IO.FS.writeBinFile (artifact ++ ".vbc") compiled.prog.encode
          IO.FS.writeFile (artifact ++ ".expected") trace
      | .error error =>
        if expected || (error.splitOn "dummy type value cannot").length ≤ 1 then
          throw <| IO.userError s!"waiting {name}/{dummy}: {error}"
  IO.println "waiting tuple transport passed (8 classifications, 7 complete eight-value VM oracles)"

private def source : String :=
  "One()<computes>:int=1\nTwo()<computes>:int=2\n" ++
  "a:=class<computes>{M()<computes>:int=1|2}\nb:=class<computes>{M()<computes>:int=3|4}\nDup(V:t where t:type)<computes>:t=V|V\n" ++
  "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:tuple([]int,int)=\n" ++
  "    var Counter:int=0\n    var Runtime:type{_()<computes>:int}=F\n    var Stored:type{_()<computes>:int}=Dummy\n" ++
  "    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M()):\n" ++
  "        set Counter+=1\n        set Runtime=F\n        set Stored=F\n        Stored()+Runtime()+Counter\n    (Rows,Counter)\n" ++
  "Main():void=\n    Result:=Caller(One,Two)\n    for(Value:Result(0)):Print(\"{Value}\")\n    Print(\"{Result(1)}\")\n"

private def checkMixedOverwrite (args : List String) : IO Unit := do
  let expected := String.join ((List.range 64).map fun i => s!"{i+3}\n") ++ "64\n"
  for dummy in [false,true] do
    let result := do
      let tops ← parseProgram source
      elabProgram (tops.map fun (top : STop) => match top with
        | .fn p n ps ts fx ret body => .fn p n (ps.map fun (parameter : SParam) =>
          { parameter with typeValue := dummy && n == "Caller" && parameter.name == "Dummy" }) ts fx ret body
        | top => top)
    let compiled ← match result with
      | .ok compiled => pure compiled
      | .error error => throw <| IO.userError s!"dummy={dummy}: {error}"
    unless compiled.prog.check && compiled.prog.checkControl && compiled.prog.checkTypes compiled.sigs compiled.slotTys do
      throw <| IO.userError s!"dummy={dummy}: invalid Core"
    match compiled.prog.runB 10000000 10000 with
    | .res (.ok _, output) =>
      unless String.ofList (output.map Char.ofNat) == expected do
        throw <| IO.userError s!"dummy={dummy}: incorrect complete trace"
    | _ => throw <| IO.userError s!"dummy={dummy}: VM failure"
    if let [out] := args then
      IO.FS.writeFile s!"{out}/mixed-overwrite.verse" source
      IO.FS.writeFile s!"{out}/mixed-overwrite.expected" expected
      IO.FS.writeBinFile s!"{out}/mixed-overwrite-{dummy}.vbc" compiled.prog.encode
    IO.println s!"PASS mixed overwrite dummy={dummy}: all Core checks; all 64 rows and final Counter exact"

def main (args : List String) : IO Unit := do
  checkTupleColumns
  checkTupleJoins
  checkWaitingTransport args
  checkMixedOverwrite args
