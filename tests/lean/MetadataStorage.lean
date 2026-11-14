import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private def evidenceType (ty : STy) : STy :=
  match ty.mapNamesM (fun name => pure (if name == "evidence" then SubtypeEvidence.family else name)) with
  | .ok renamed => renamed
  | .error _ => ty

private partial def evidenceBody (body : SExpr) : SExpr :=
  Choice.mapE (fun
    | .decl p name ty mutable value =>
      some (.decl p name (ty.map evidenceType) mutable (evidenceBody value))
    | .construct p name args fields =>
      some (.construct p name (args.map evidenceType) (fields.map evidenceBody))
    | _ => none) body

private partial def roles (dummy : Bool) : STop → Except String STop
  | .fn p name ps tps specs ret body => do
    let rename (n : String) : Except String String :=
      pure (if n == "evidence" then SubtypeEvidence.family else n)
    let ps ← ps.mapM fun param => do
      return { param with
        ty := ← param.ty.mapNamesM rename
        typeValue := (dummy && ((name == "Caller" && param.name == "Dummy") ||
          (name == "ForwardMeta" && param.name == "M"))) ||
          (name == "IgnoreMeta" && param.name == "M") }
    return .fn p name ps tps specs (← ret.mapNamesM rename) (evidenceBody body)
  | .classDef p name nsp tps specs parents iface fields methods => do
    let rename (n : String) : Except String String :=
      pure (if n == "evidence" then SubtypeEvidence.family else n)
    let fields ← fields.mapM fun f => do return { f with ty := ← f.ty.mapNamesM rename }
    return .classDef p name nsp tps specs parents iface fields (← methods.mapM (roles dummy))
  | top => pure top

private def caller (body : String) : String :=
  "Caller(X:t,D:u,Dummy:u,P:evidence(evidence(vehicle,t),u) where t:type,u:type)<transacts>:int=\n" ++ body

private def cases : List (String × String) := [
  ("saved bound receiver across wait", "reader:=class<computes>{Read()<suspends>:int=7}\nCaller(Dummy:reader)<suspends>:int=\n    Saved:=Dummy.Read\n    Sleep(0.01)\n    Saved()"),
  ("ignored method receiver", "reader:=class<computes>{Read()<computes>:int=7}\nCaller(Dummy:reader)<computes>:int=Dummy.Read()"),
  ("constructed metadata receiver", "reader:=class<computes>{Value:int;Read()<computes>:int=7}\nCaller(Dummy:int)<computes>:int=reader{Value:=Dummy}.Read()"),
  ("task cancel receiver", "Caller(Dummy:task(int))<suspends>:void=Dummy.Cancel()"),
  ("task await receiver", "Caller(Dummy:task(int))<suspends>:int=Dummy.Await()"),
  ("event await receiver", "Caller(Dummy:event(int))<suspends>:int=Dummy.Await()"),
  ("event signal receiver", "Caller(Dummy:event(int)):void=Dummy.Signal(1)"),
  ("unit event signal receiver", "Caller(Dummy:event()):void=Dummy.Signal()"),
  ("mutable local", caller "    var Stored:u=D\n    set Stored=Dummy\n    P.Up(Stored).Up(X).N"),
  ("helper return", "Keep(V:v where v:type)<computes>:v=V\n" ++
    caller "    var Stored:u=D\n    set Stored=Keep(Dummy)\n    P.Up(Stored).Up(X).N"),
  ("helper local", "Keep(V:v where v:type)<transacts>:v=\n    var Stored:v=V\n    set Stored=V\n    Stored\n" ++
    caller "    var Stored:u=D\n    set Stored=Keep(Dummy)\n    P.Up(Stored).Up(X).N"),
  ("returned metadata formal", "ForwardMeta(M:v where v:type)<computes>:v=M\n" ++
    caller "    var Stored:u=D\n    set Stored=ForwardMeta(Dummy)\n    P.Up(Stored).Up(X).N"),
  ("recursive helper", "Keep(V:v,N:int where v:type)<computes>:v=if(N>0)then Keep(V,N-1)else V\n" ++
    caller "    var Stored:u=D\n    set Stored=Keep(Dummy,2)\n    P.Up(Stored).Up(X).N"),
  ("branch join", caller "    var Stored:u=D\n    if(true?)then set Stored=Dummy\n    P.Up(Stored).Up(X).N"),
  ("loop back edge", caller "    var Stored:u=D\n    loop:\n        set Stored=Dummy\n        break\n    P.Up(Stored).Up(X).N"),
  ("array update", caller "    var Stored:[]u=array{D}\n    if(set Stored[0]=Dummy){}\n    if(V:=Stored[0])then P.Up(V).Up(X).N else 0"),
  ("map update", caller "    var Stored:[int]u=map{0=>D}\n    if(set Stored[0]=Dummy){}\n    if(V:=Stored[0])then P.Up(V).Up(X).N else 0"),
  ("object alias", "cell(v:type):=class:\n    var Value:v\n" ++
    caller "    C:=cell(u){Value:=D}\n    Alias:=C\n    set Alias.Value=Dummy\n    P.Up(C.Value).Up(X).N"),
  ("indexed object alias", "cell(v:type):=class:\n    var Value:v\n" ++
    caller "    C:=cell(u){Value:=D}\n    Refs:=array{C}\n    if(Alias:=Refs[0])then set Alias.Value=Dummy\n    P.Up(C.Value).Up(X).N"),
  ("helper object write", "cell(v:type):=class:\n    var Value:v\nStore(C:cell(v),V:v where v:type)<transacts>:void=set C.Value=V\n" ++
    caller "    C:=cell(u){Value:=D}\n    Store(C,Dummy)\n    P.Up(C.Value).Up(X).N"),
  ("shared frame local", "Caller(X:t,D:u,Dummy:u,P:evidence(evidence(vehicle,t),u),E:event(int) where t:type,u:type)<suspends>:int=\n    var Stored:u=D\n    E.Await()\n    set Stored=Dummy\n    P.Up(Stored).Up(X).N"),
  ("later GADT refinement", "pair(a:type,b:type):=class{A:a;B:b}\nsame(v:type):=class(pair(v,v)){}\nCaller(X:t,D:u,Dummy:u,Pair:pair(u,evidence(vehicle,t)) where t:type,u:type)<transacts>:int=\n    var Stored:u=D\n    set Stored=Dummy\n    if(S:=same[Pair])then Stored.Up(X).N else 0"),
  ("function stored in local", "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Dummy\n    Stored()"),
  ("metadata function without overwrite", "Caller(Dummy:type{_()<computes>:int})<transacts>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    Stored()"),
  ("metadata copy survives real overwrite", "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    Saved:=Stored\n    set Stored=F\n    Saved()"),
  ("mutable implicit evidence without overwrite", "Caller(X:t,Dummy:evidence(vehicle,t) where t:type)<transacts>:int=\n    var Stored:evidence(vehicle,t)=Dummy\n    X.N")]

private def forwards : List (String × String) := [
  ("independent bound receiver across wait", "reader:=class<computes>{Read()<suspends>:int=7}\nFresh(V:u where u:type)<computes>:reader=reader{}\nCaller(Dummy:u where u:type)<suspends>:int=\n    Saved:=Fresh(Dummy).Read\n    Sleep(0.01)\n    Saved()"),
  ("void to real array carrier", "carrier:=class<computes>{Values:[]int;Count()<computes>:int=Values.Length}\nCaller(Dummy:void)<computes>:int=\n    Items:[]int=Dummy\n    Box:=carrier{Values:=Items}\n    Box.Count()"),
  ("true to real array carrier", "carrier:=class<computes>{Values:[]int;Count()<computes>:int=Values.Length}\nCaller(Dummy:true)<computes>:int=carrier{Values:=Dummy}.Count()"),
  ("independent method receiver", "reader:=class<computes>{Read()<computes>:int=7}\nFresh(V:u where u:type)<computes>:reader=reader{}\nCaller(Dummy:u where u:type)<computes>:int=Fresh(Dummy).Read()"),
  ("independent virtual receiver", "reader:=interface<computes>{Read()<computes>:int}\nleft:=class<computes>(reader){Read<override>()<computes>:int=7}\nright:=class<computes>(reader){Read<override>()<computes>:int=8}\nFresh(V:u,C:logic where u:type)<computes>:reader=if(C?)then left{}else right{}\nCaller(Dummy:u,C:logic where u:type)<computes>:int=Fresh(Dummy,C).Read()"),
  ("independent function receiver", "One()<computes>:int=7\nFresh(V:u where u:type)<computes>:type{_()<computes>:int}=One\nCaller(Dummy:u where u:type)<computes>:int=Fresh(Dummy)()"),
  ("independent spawned receiver", "Work()<suspends>:int=7\nFresh(V:u where u:type)<computes>:type{_()<suspends>:int}=Work\nCaller(Dummy:u where u:type)<suspends>:int=\n    T:=spawn{Fresh(Dummy)()}\n    T.Await()"),
  ("metadata argument with real return", "IgnoreMeta(M:u,Real:evidence(vehicle,t) where u:type,t:type)<computes>:evidence(vehicle,t)=Real\nCaller(X:t,D:evidence(vehicle,t),Dummy:u where t:type,u:type)<computes>:int=IgnoreMeta(Dummy,D).Up(X).N"),
  ("metadata argument with real failable return", "IgnoreMeta(M:u,Real:evidence(vehicle,t) where u:type,t:type)<decides><computes>:evidence(vehicle,t)=block{true?;Real}\nCaller(X:t,D:evidence(vehicle,t),Dummy:u where t:type,u:type)<computes>:int=if(Proof:=IgnoreMeta[Dummy,D])then Proof.Up(X).N else 0"),
  ("opaque mutable local", "Caller(Dummy:u where u:type)<transacts>:u=\n    var Stored:u=Dummy\n    set Stored=Dummy\n    Stored"),
  ("opaque overwritten local", "Caller(D:u,Dummy:u where u:type)<transacts>:u=\n    var Stored:u=D\n    set Stored=Dummy\n    Stored"),
  ("opaque updated array", "Caller(D:u,Dummy:u where u:type)<transacts>:[]u=\n    var Stored:[]u=array{D}\n    if(set Stored[0]=Dummy){}\n    Stored"),
  ("opaque helper", "Keep(V:u where u:type)<transacts>:u=\n    var Stored:u=V\n    set Stored=V\n    Stored\nCaller(Dummy:u where u:type)<transacts>:u=Keep(Dummy)"),
  ("real overwrite", caller "    var Stored:u=D\n    set Stored=Dummy\n    set Stored=D\n    P.Up(Stored).Up(X).N"),
  ("rolled back unit query", caller "    var Stored:u=D\n    if(set Stored=Dummy;()?){}\n    P.Up(Stored).Up(X).N"),
  ("rolled back negation query", "No(V:u where u:type)<decides><computes>:void=false?\n" ++
    caller "    var Stored:u=D\n    if(set Stored=Dummy;(not No[Dummy])?){}\n    P.Up(Stored).Up(X).N"),
  ("rolled back overwrite", caller "    var Stored:u=D\n    if(set Stored=Dummy;false?){}\n    P.Up(Stored).Up(X).N")]
  ++ [("failed helper branch", "No(V:u where u:type)<decides><transacts>:void=false?\n" ++
    caller "    var Stored:u=D\n    if(No[Dummy])then set Stored=Dummy\n    P.Up(Stored).Up(X).N"),
  ("opaque shared local", "Caller(Dummy:u,E:event(int) where u:type)<suspends>:u=\n    var Stored:u=Dummy\n    E.Await()\n    set Stored=Dummy\n    Stored"),
  ("metadata function overwritten with data", "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    Stored()"),
  ("nested overwrite returns data", "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n    Saved:=block{var Stored:type{_()<computes>:int}=Dummy;set Stored=F;Stored}\n    Saved()"),
  ("overwrite in condition clauses", "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n    if(var Stored:type{_()<computes>:int}=Dummy,set Stored=F,Value:=Stored(),Value>=0)then Value else 0"),
  ("opaque metadata alias in suspended stage", "Dup(N:int)<computes>:int=N|N\nCaller(Dummy:u where u:type)<suspends>:[]u=\n    var Stored:u=Dummy\n    Saved:=Stored\n    for(A:=(Dup(1)|Dup(2)),B:=(Dup(1)|Dup(2))):block{Sleep(0.01);Saved}"),
  ("real overwrite alias in suspended stage", "Dup(N:int)<computes>:int=N|N\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:[]int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    Saved:=Stored\n    for(A:=(Dup(1)|Dup(2)),B:=(Dup(1)|Dup(2))):block{Sleep(0.01);Saved()}"),
  ("mutable implicit evidence after real overwrite", "Caller(X:t,Dummy:evidence(vehicle,t),Real:type{_()<computes>:evidence(vehicle,t)} where t:type)<transacts>:int=\n    var Stored:evidence(vehicle,t)=Dummy\n    set Stored=Real()\n    X.N")]

private def compileCase (source : String) (dummy : Bool) : Except String Compiled := do
  let tops ← parseProgram ("vehicle:=class<computes>{N:int=7}\n" ++ source ++ "\nMain():void={}")
  elabProgram (← tops.mapM (roles dummy))

def main : IO Unit := do
  let mut failures := 0
  for (label, source) in cases ++ forwards do
    for dummy in [false, true] do
      let shouldReject := dummy && cases.any (·.1 == label)
      match compileCase source dummy with
      | .ok c =>
        if shouldReject || !(c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys) then
          IO.println s!"FAIL {label}, dummy={dummy}: admitted={shouldReject}, Core checks"
          failures := failures + 1
      | .error message =>
        -- An opaque proof is also excluded from implicit member lookup.
        let missingProof := label == "mutable implicit evidence without overwrite" &&
          (message.splitOn "t has no member 'N'").length > 1
        if !shouldReject || (!missingProof && (message.splitOn "dummy type value cannot").length ≤ 1) then
          IO.println s!"FAIL {label}, dummy={dummy}: {message}"
          failures := failures + 1
  if failures > 0 then throw (IO.userError s!"{failures} metadata storage contracts failed")
  IO.println s!"metadata storage contracts passed ({cases.length} real/dummy refusals, {forwards.length} forwarding/overwrite pairs)"
