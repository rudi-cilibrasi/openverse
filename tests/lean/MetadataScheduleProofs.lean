import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private def callable := "type{_()<computes>:int}"
private def sourcePrefix := "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(V:" ++ callable ++ ")<computes>:int=V()\nId(V:t where t:type)<computes>:t=V\n"
private def recursivePrefix :=
  "Keep(V:t,N:int where t:type)<computes>:t=if(N>0)then Keep(V,N-1)else V\n"



/-- These controls distinguish a checked replay from a cached return role:
    called bodies, shared-write diagnostics, tuple-column contexts and borrowed
    captures must still be checked even when the caller returns ordinary data. -/
private def cases : List (String × String × Bool) := [
  ("recursive callee summary must invalidate provisional replay", "    Rows:=for(A:=1|2):\n        Sleep(0.001)\n        Use(Keep(Dummy,2))\n    Rows.Length\n", false),
  ("recursive real return remains valid", "    Rows:=for(A:=1|2):\n        Sleep(0.001)\n        Use(Keep(F,2))\n    Rows.Length\n", true),
  ("called receiver remains executable", "    Rows:=for(A:=1|2):\n        Sleep(0.001)\n        Use(Dummy)\n    Rows.Length\n", false),
  ("real called receiver remains valid", "    Rows:=for(A:=1|2):\n        Sleep(0.001)\n        Use(F)\n    Rows.Length\n", true),
  ("suppressed shared write must force validation", "    var Stored:" ++ callable ++ "=F\n    Rows:=for(A:=1|2):\n        set Stored=Dummy\n        Sleep(0.001)\n        0\n    Rows.Length\n", false),
  ("real shared write remains valid", "    var Stored:" ++ callable ++ "=Dummy\n    Rows:=for(A:=1|2):\n        set Stored=F\n        Sleep(0.001)\n        0\n    Rows.Length\n", true),
  ("opaque tuple column cannot reuse real context", "    Real:=Id((Dummy,F))\n    Other:=Id((F,Dummy))\n    Rows:=for(A:=1|2):\n        Sleep(0.001)\n        Real(1)()+Other(1)()\n    Rows.Length\n", false),
  ("distinct real tuple columns remain valid", "    Real:=Id((Dummy,F))\n    Other:=Id((F,Dummy))\n    Rows:=for(A:=1|2):\n        Sleep(0.001)\n        Real(1)()+Other(0)()\n    Rows.Length\n", true),
  ("live forwarded tuple survives rollback and wait", "    Rows:=for(A:=1|2):\n        var T:tuple(" ++ callable ++ "," ++ callable ++ ")=(Dummy,F)\n        Saved:=Id(T)\n        if(set T=(F,Dummy);false?){}\n        Sleep(0.001)\n        Saved(1)()+T(1)()\n    Rows.Length\n", true),
  ("live forwarded tuple retains opaque column", "    Rows:=for(A:=1|2):\n        var T:tuple(" ++ callable ++ "," ++ callable ++ ")=(Dummy,F)\n        Saved:=Id(T)\n        if(set T=(F,Dummy);false?){}\n        Sleep(0.001)\n        Saved(0)()\n    Rows.Length\n", false),
  ("overwritten tuple retains its new real column", "    Rows:=for(A:=1|2):\n        var T:tuple(" ++ callable ++ "," ++ callable ++ ")=(Dummy,F)\n        set T=(F,Dummy)\n        Sleep(0.001)\n        Id(T)(0)()\n    Rows.Length\n", true),
  ("borrowed real overwrite remains valid", "    var Stored:" ++ callable ++ "=Dummy\n    branch:\n        Sleep(0.001)\n        Value:=Stored()\n    set Stored=F\n    Sleep(0.002)\n    0\n", true),
  ("saved borrowed metadata remains unsafe", "    var Stored:" ++ callable ++ "=Dummy\n    Saved:=Stored\n    branch:\n        Sleep(0.001)\n        Value:=Saved()\n    set Stored=F\n    Sleep(0.002)\n    0\n", false)]

private def checkForwardedCalls : IO Unit := do
  let reader : VTy := .ref [0] []
  let origin : FrameRefs.Origin := { frame := "Owner", name := "Value", args := [] }
  for called in [false,true] do
    for dummy in [false,true] do
      let make (name : String) (arity : Nat) (body : Expr) : Fn :=
        { name, arity, nslots := arity, decides := false, writes := false, body }
      let fns := #[
        make "Owner" 1 (if called then .call 1 [.local 0] else .lit (.int 7)),
        make "Bridge" 1 (.call 2 [.local 0]),
        make "Leaf" 1 (.call 3 [.local 0]),
        make "Run" 1 (.lit (.int 7)),
        make "Main" 0 (.lit .void)]
      let prog : Prog := { fns := fns.toList, main := 4 }
      let sigs : Sigs := {
        fns := List.replicate 4 ([reader], .int) ++ [([], .void)]
        classes := [[]], pins := [[]] }
      let slots := List.replicate 4 [reader] ++ [[]]
      unless prog.check && prog.checkControl && prog.checkTypes sigs slots do
        throw <| IO.userError "forwarded call control has invalid Core"
      let infos : Array MetadataFlow.Info := #[
        { inputs := if dummy then [0] else [], source := { slots := [(0, origin)] } },
        { source := { forwarded := [origin] } },
        { source := { slots := [(0, origin)] } },
        { required := [0] }, {}]
      match MetadataFlow.check fns infos #[] with
      | .ok _ =>
        if called && dummy then throw <| IO.userError "forwarded owner hid an actually called unsafe callee"
      | .error error =>
        unless called && dummy && (error.splitOn "dummy type value cannot").length > 1 do
          throw <| IO.userError s!"forwarded call/{called}/{dummy}: {error}"

def main : IO Unit := do
  for (name, body, accepted) in cases do
    let source := sourcePrefix ++ recursivePrefix ++ "Caller(F:" ++ callable ++ ",Dummy:" ++ callable ++ ")<suspends>:int=\n" ++ body ++ "Main()<suspends>:void=Print(\"{Caller(One,Two)}\")\n"
    for dummy in [false,true] do
      let result := do
        let tops ← parseProgram source
        elabProgram (tops.map fun (top : STop) => match top with
          | .fn p n ps ts fx ret body => .fn p n (ps.map fun (parameter : SParam) =>
            { parameter with typeValue := dummy && n == "Caller" && parameter.name == "Dummy" }) ts fx ret body
          | top => top)
      match result with
      | .ok compiled =>
        unless (!dummy || accepted) && compiled.prog.check && compiled.prog.checkControl &&
            compiled.prog.checkTypes compiled.sigs compiled.slotTys do
          throw <| IO.userError s!"{name}/{dummy}: unsafe admission or invalid Core"
      | .error error =>
        if dummy && name == "suppressed shared write must force validation" &&
            (error.splitOn "enter a shared local containing executable data").length ≤ 1 then
          throw <| IO.userError s!"{name}: wrong boundary {error}"
        if !dummy || accepted || (error.splitOn "dummy type value cannot").length ≤ 1 then
          throw <| IO.userError s!"{name}/{dummy}: unexpected refusal {error}"
  checkForwardedCalls
  IO.println "metadata scheduled replay contracts passed (13 real/dummy pairs, 4 forwarded-owner controls)"
