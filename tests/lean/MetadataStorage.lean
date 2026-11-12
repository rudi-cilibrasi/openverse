import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private partial def roles (dummy : Bool) : STop → Except String STop
  | .fn p name ps tps specs ret body => do
    let rename (n : String) : Except String String :=
      pure (if n == "evidence" then SubtypeEvidence.family else n)
    let ps ← ps.mapM fun param => do
      return { param with
        ty := ← param.ty.mapNamesM rename
        typeValue := dummy && name == "Caller" && param.name == "Dummy" }
    return .fn p name ps tps specs (← ret.mapNamesM rename) body
  | .classDef p name tps specs parents iface fields overrides methods => do
    let rename (n : String) : Except String String :=
      pure (if n == "evidence" then SubtypeEvidence.family else n)
    let fields ← fields.mapM fun (field, ty, value, mutable) =>
      return (field, ← ty.mapNamesM rename, value, mutable)
    return .classDef p name tps specs parents iface fields overrides (← methods.mapM (roles dummy))
  | top => pure top

private def caller (body : String) : String :=
  "Caller(X:t,D:u,Dummy:u,P:evidence(evidence(vehicle,t),u) where t:type,u:type)<transacts>:int=\n" ++ body

private def cases : List (String × String) := [
  ("mutable local", caller "    var Stored:u=D\n    set Stored=Dummy\n    P.Up(Stored).Up(X).N"),
  ("helper return", "Keep(V:v where v:type)<computes>:v=V\n" ++
    caller "    var Stored:u=D\n    set Stored=Keep(Dummy)\n    P.Up(Stored).Up(X).N"),
  ("helper local", "Keep(V:v where v:type)<transacts>:v=\n    var Stored:v=V\n    set Stored=V\n    Stored\n" ++
    caller "    var Stored:u=D\n    set Stored=Keep(Dummy)\n    P.Up(Stored).Up(X).N"),
  ("recursive helper", "Keep(V:v,N:int where v:type)<computes>:v=if(N>0)then Keep(V,N-1)else V\n" ++
    caller "    var Stored:u=D\n    set Stored=Keep(Dummy,2)\n    P.Up(Stored).Up(X).N"),
  ("branch join", caller "    var Stored:u=D\n    if(true?)then set Stored=Dummy\n    P.Up(Stored).Up(X).N"),
  ("loop back edge", caller "    var Stored:u=D\n    loop:\n        set Stored=Dummy\n        break\n    P.Up(Stored).Up(X).N"),
  ("array update", caller "    var Stored:[]u=array{D}\n    if(set Stored[0]=Dummy){}\n    if(V:=Stored[0])then P.Up(V).Up(X).N else 0"),
  ("map update", caller "    var Stored:[int]u=map{0=>D}\n    set Stored[0]=Dummy\n    if(V:=Stored[0])then P.Up(V).Up(X).N else 0"),
  ("object alias", "cell(v:type):=class:\n    var Value:v\n" ++
    caller "    C:=cell(u){Value:=D}\n    Alias:=C\n    set Alias.Value=Dummy\n    P.Up(C.Value).Up(X).N"),
  ("indexed object alias", "cell(v:type):=class:\n    var Value:v\n" ++
    caller "    C:=cell(u){Value:=D}\n    Refs:=array{C}\n    if(Alias:=Refs[0])then set Alias.Value=Dummy\n    P.Up(C.Value).Up(X).N"),
  ("helper object write", "cell(v:type):=class:\n    var Value:v\nStore(C:cell(v),V:v where v:type)<transacts>:void=set C.Value=V\n" ++
    caller "    C:=cell(u){Value:=D}\n    Store(C,Dummy)\n    P.Up(C.Value).Up(X).N"),
  ("shared frame local", "Caller(X:t,D:u,Dummy:u,P:evidence(evidence(vehicle,t),u),E:event(int) where t:type,u:type)<suspends>:int=\n    var Stored:u=D\n    E.Await()\n    set Stored=Dummy\n    P.Up(Stored).Up(X).N"),
  ("later GADT refinement", "pair(a:type,b:type):=class{A:a;B:b}\nsame(v:type):=class(pair(v,v)){}\nCaller(X:t,D:u,Dummy:u,Pair:pair(u,evidence(vehicle,t)) where t:type,u:type)<transacts>:int=\n    var Stored:u=D\n    set Stored=Dummy\n    if(S:=same[Pair])then Stored.Up(X).N else 0"),
  ("function stored in local", "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Dummy\n    Stored()")]

private def forwards : List (String × String) := [
  ("opaque mutable local", "Caller(Dummy:u where u:type)<transacts>:u=\n    var Stored:u=Dummy\n    set Stored=Dummy\n    Stored"),
  ("opaque overwritten local", "Caller(D:u,Dummy:u where u:type)<transacts>:u=\n    var Stored:u=D\n    set Stored=Dummy\n    Stored"),
  ("opaque updated array", "Caller(D:u,Dummy:u where u:type)<transacts>:[]u=\n    var Stored:[]u=array{D}\n    if(set Stored[0]=Dummy){}\n    Stored"),
  ("opaque helper", "Keep(V:u where u:type)<transacts>:u=\n    var Stored:u=V\n    set Stored=V\n    Stored\nCaller(Dummy:u where u:type)<transacts>:u=Keep(Dummy)"),
  ("real overwrite", caller "    var Stored:u=D\n    set Stored=Dummy\n    set Stored=D\n    P.Up(Stored).Up(X).N"),
  ("rolled back overwrite", caller "    var Stored:u=D\n    if(set Stored=Dummy;false?){}\n    P.Up(Stored).Up(X).N")]
  ++ [("failed helper branch", "No(V:u where u:type)<decides><transacts>:void=false?\n" ++
    caller "    var Stored:u=D\n    if(No[Dummy])then set Stored=Dummy\n    P.Up(Stored).Up(X).N"),
  ("opaque shared local", "Caller(Dummy:u,E:event(int) where u:type)<suspends>:u=\n    var Stored:u=Dummy\n    E.Await()\n    set Stored=Dummy\n    Stored")]

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
        if !shouldReject || (message.splitOn "dummy type value cannot").length ≤ 1 then
          IO.println s!"FAIL {label}, dummy={dummy}: {message}"
          failures := failures + 1
  if failures > 0 then throw (IO.userError s!"{failures} metadata storage contracts failed")
  IO.println s!"metadata storage contracts passed ({cases.length} real/dummy refusals, {forwards.length} forwarding/overwrite pairs)"
