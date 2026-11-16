import OpenVerse.Front.Elab
open OpenVerse OpenVerse.Front

private def base : String :=
  "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\n" ++
  "a:=class<computes>{M()<computes>:int=1|2}\n" ++
  "b:=class<computes>{M()<computes>:int=3|4}\n" ++
  "Dup(V:t where t:type)<computes>:t=V|V\n"
private def head : String :=
  "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n"
private def clauses : String :=
  "A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M()"
private def cases : List (String × Bool × String) := [
  ("for metadata capture", true,
    head ++ "    var Stored:type{_()<computes>:int}=Dummy\n    Rows:=for(" ++ clauses ++ "):Stored()\n    Rows.Length"),
  ("for real overwrite", false,
    head ++ "    var Stored:type{_()<computes>:int}=Dummy\n    Rows:=for(" ++ clauses ++ "):\n        set Stored=F\n        Stored()\n    Rows.Length"),
  ("for possibly-empty metadata copy-out (baseline refusal)", true,
    head ++ "    var Stored:type{_()<computes>:int}=Dummy\n    Rows:=for(" ++ clauses ++ "):\n        set Stored=F\n        X+Y\n    Stored()"),
  ("for dummy overwrite", true,
    head ++ "    var Stored:type{_()<computes>:int}=F\n    Rows:=for(" ++ clauses ++ "):\n        set Stored=Dummy\n        Stored()\n    Rows.Length"),
  ("for rejected dummy overwrite", false,
    head ++ "    var Stored:type{_()<computes>:int}=F\n    Rows:=for(" ++ clauses ++ "):\n        if(set Stored=Dummy;false?){}\n        Stored()\n    Rows.Length"),
  ("first metadata capture", true,
    head ++ "    var Stored:type{_()<computes>:int}=Dummy\n    if(" ++ clauses ++ ",Value:=Stored())then Value else 0"),
  ("first real overwrite", false,
    head ++ "    var Stored:type{_()<computes>:int}=Dummy\n    if(" ++ clauses ++ ",block{set Stored=F;X+Y>0},Value:=Stored())then Value else 0"),
  ("first possibly-empty metadata copy-out (baseline refusal)", true,
    head ++ "    var Stored:type{_()<computes>:int}=Dummy\n    if(" ++ clauses ++ ",block{set Stored=F;X+Y>0}){}\n    Stored()"),
  ("option metadata capture", true,
    head ++ "    var Stored:type{_()<computes>:int}=Dummy\n    O:=option{" ++ clauses ++ ";Stored()}\n    O? or 0"),
  ("option real overwrite", false,
    head ++ "    var Stored:type{_()<computes>:int}=Dummy\n    O:=option{" ++ clauses ++ ";block{set Stored=F;X+Y>0};Stored()}\n    O? or 0")]

private def mark (dummy : Bool) : STop → STop
  | .fn p name params tparams specs ret body =>
    .fn p name (params.map fun parameter =>
      { parameter with typeValue := dummy && name == "Caller" && parameter.name == "Dummy" })
      tparams specs ret body
  | top => top

private def checkMetadata : IO Unit := do
  let mut failures := 0
  let mixed := cases.filterMap fun (name, refusal, source) =>
    if name.endsWith "real overwrite" then
      -- Tuple columns retain the independent real runtime captures even when
      -- the separate metadata capture began opaque and is overwritten.
      some (name ++ " mixed runtime state", refusal,
        (source.replace "var Stored:" "var Counter:int=0\n    var Runtime:type{_()<computes>:int}=F\n    var Stored:").replace "set Stored=F" "set Counter+=1;set Runtime=F;set Stored=F" |>.replace "Stored()" "Stored()+Runtime()+Counter")
    else none
  for (name, refusal, source) in cases ++ mixed do
    for dummy in [false,true] do
      let result := do
        let tops ← parseProgram (base ++ source ++ "\nMain():void={}\n")
        elabProgram (tops.map (mark dummy))
      let reject := dummy && refusal
      match result with
      | .ok compiled =>
        if reject || !(compiled.prog.check && compiled.prog.checkControl &&
            compiled.prog.checkTypes compiled.sigs compiled.slotTys) then
          IO.println s!"FAIL {name} dummy={dummy}: admitted={reject}, Core checks"
          failures := failures + 1
      | .error error =>
        if !reject || (error.splitOn "dummy type value cannot").length ≤ 1 then
          IO.println s!"FAIL {name} dummy={dummy}: {error}"
          failures := failures + 1
  if failures > 0 then throw (IO.userError s!"{failures} producer metadata failures")
  IO.println s!"producer metadata contracts passed ({cases.length + mixed.length} paired source controls)"

private def checkForwarding : IO Unit := do
  let mut failures := 0
  for executes in [false, true] do
    let source := "One()<computes>:int=1\n" ++
      "Forward(P:type{_()<computes>:int})<computes>:int=" ++
      (if executes then "P()" else "1") ++ "\n" ++
      "Caller(Dummy:type{_()<computes>:int})<computes>:int=Forward(Dummy)\nMain():void={}\n"
    let result := do
      let tops ← parseProgram source
      elabProgram (tops.map fun (top : STop) => match top with
        | .fn p n ps ts fx ret body => .fn p n (ps.map fun (param : SParam) =>
          { param with metadataForward := n == "Forward", typeValue := n == "Caller" }) ts fx ret body
        | top => top)
    match result with
    | .ok compiled =>
      if executes || !(compiled.prog.check && compiled.prog.checkControl &&
          compiled.prog.checkTypes compiled.sigs compiled.slotTys) then
        IO.println s!"FAIL forwarding executes={executes}: accepted or invalid Core"
        failures := failures + 1
    | .error error =>
      if !executes || (error.splitOn "dummy type value cannot").length ≤ 1 then
        IO.println s!"FAIL forwarding executes={executes}: {error}"
        failures := failures + 1
  if failures > 0 then throw (IO.userError s!"{failures} forwarding contract failures")
  IO.println "metadata transport preserves actual provenance and executable-use refusals"

private def checkGenericYield : IO Unit := do
  for argument in ["F", "Dummy"] do
    for dummy in [false, true] do
      let source := "a:=class<computes>{M(V:t where t:type)<computes>:t=V|V}\nb:=class<computes>{M(V:t where t:type)<computes>:t=V|V}\nDup(V:t where t:type)<computes>:t=V|V\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(" ++ argument ++ "),B:=Dup(a{})|Dup(b{}),Y:=B.M(" ++ argument ++ ")):X()+Y()\n    Rows.Length\nMain():void={}\n"
      let result := do
        let tops ← parseProgram source
        elabProgram (tops.map fun (top : STop) => match top with
          | .fn p n ps ts fx ret body => .fn p n (ps.map fun (parameter : SParam) =>
            { parameter with typeValue := dummy && n == "Caller" && parameter.name == "Dummy" }) ts fx ret body
          | top => top)
      match result with
      | .ok compiled =>
        if (dummy && argument == "Dummy") || !(compiled.prog.check && compiled.prog.checkControl &&
            compiled.prog.checkTypes compiled.sigs compiled.slotTys) then
          throw (IO.userError s!"generic producer yielded invalid executable evidence: {argument} dummy={dummy}")
      | .error error =>
        if !dummy || argument != "Dummy" || (error.splitOn "dummy type value cannot").length ≤ 1 then
          throw (IO.userError s!"generic producer evidence: {argument} dummy={dummy}: {error}")
  IO.println "generic producer yields preserve executable evidence and dummy refusals"

private def checkGenericCrossGenerator : IO Unit := do
  for argument in ["F", "Dummy"] do
    for dummy in [false, true] do
      let source := "a:=class<computes>{M(V:t where t:type)<computes>:t=V|V}\nb:=class<computes>{M(V:t where t:type)<computes>:t=V|V}\nleft:=class<computes>{Data:type{_()<computes>:int}}\nright:=class<computes>{Data:type{_()<computes>:int}}\nDup(V:t where t:type)<computes>:t=V|V\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n    Rows:=for(A:=Dup(a{})|Dup(b{}),B:=Dup(left{Data:=" ++ argument ++ "})|Dup(right{Data:=" ++ argument ++ "}),X:=A.M(B.Data)):X()\n    Rows.Length\nMain():void={}\n"
      let result := do
        let tops ← parseProgram source
        elabProgram (tops.map fun (top : STop) => match top with
          | .fn p n ps ts fx ret body => .fn p n (ps.map fun (parameter : SParam) =>
            { parameter with typeValue := dummy && n == "Caller" && parameter.name == "Dummy" }) ts fx ret body
          | top => top)
      match result with
      | .ok compiled =>
        if (dummy && argument == "Dummy") || !(compiled.prog.check && compiled.prog.checkControl &&
            compiled.prog.checkTypes compiled.sigs compiled.slotTys) then
          throw (IO.userError s!"generic producer yielded invalid executable evidence: {argument} dummy={dummy}")
      | .error error =>
        if !dummy || argument != "Dummy" || (error.splitOn "dummy type value cannot").length ≤ 1 then
          throw (IO.userError s!"generic producer evidence: {argument} dummy={dummy}: {error}")
  IO.println "cross-generator producer yields preserve executable evidence and dummy refusals"

def main : IO Unit := do
  checkMetadata
  checkForwarding
  checkGenericYield
  checkGenericCrossGenerator
