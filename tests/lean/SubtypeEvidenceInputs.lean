import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def getOK (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{label}: {message}")

/-- Mark only Caller's input. The callee must keep its ordinary real proof
    formal, as in the review reproduction; marking both hides the defect. -/
private partial def roles (dummy : Bool) : STop → Except String STop
  | .fn p name ps tps specs ret body => do
    let rename (name : String) : Except String String := pure (if name == "evidence" then family else name)
    let ps ← ps.mapM fun param => do
      let ty ← param.ty.mapNamesM rename
      return { param with
        ty, typeValue := dummy && name == "Caller" && param.name == "D" }
    return .fn p name ps tps specs (← ret.mapNamesM rename) body
  | .classDef p name nsp tps specs parents iface fields methods => do
    let rename (name : String) : Except String String := pure (if name == "evidence" then family else name)
    let fields ← fields.mapM fun f => do return { f with ty := ← f.ty.mapNamesM rename }
    return .classDef p name nsp tps specs parents iface fields (← methods.mapM (roles dummy))
  | top => pure top

private def cases : List (String × String) := [
  ("ordinary generic body", "
Use(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=X.N
Caller(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=Use(X,D)"),
  ("written named proof", "
Use(X:t,?D:evidence(vehicle,t) where t:type)<computes>:int=X.N
Caller(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=Use(X,?D:=D)"),
  ("nongeneric body", "
Use(D:evidence(vehicle,vehicle))<computes>:int=D.Up(vehicle{}).N
Caller(D:evidence(vehicle,vehicle))<computes>:int=Use(D)"),
  ("nongeneric packed tuple", "
Use(X:vehicle,D:evidence(vehicle,vehicle))<computes>:int=D.Up(X).N
Caller(D:evidence(vehicle,vehicle))<computes>:int=Use((vehicle{},D))"),
  ("nongeneric array packing", "
Use(Ds:[]evidence(vehicle,vehicle))<computes>:int=if(D:=Ds[0])then D.Up(vehicle{}).N else 0
Caller(D:evidence(vehicle,vehicle))<computes>:int=Use(D,D)"),
  ("array proof carrier", "
Use(X:t,Ds:[]evidence(vehicle,t) where t:type)<computes>:int=if(D:=Ds[0])then D.Up(X).N else 0
Caller(X:t,D:[]evidence(vehicle,t) where t:type)<computes>:int=Use(X,D)"),
  ("object proof carrier", "
holder(t:type):=class<computes>{Proof:evidence(vehicle,t)}
Use(X:t,H:holder(t) where t:type)<computes>:int=H.Proof.Up(X).N
Caller(X:t,D:holder(t) where t:type)<computes>:int=Use(X,D)"),
  ("constructed proof carrier", "
holder(t:type):=class<computes>{Proof:evidence(vehicle,t)}
Use(X:t,H:holder(t) where t:type)<computes>:int=H.Proof.Up(X).N
Caller(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=Use(X,holder(t){Proof:=D})"),
  ("direct method proof input", "
reader:=class<computes>:
    Use(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=X.N
Caller(H:reader,X:t,D:evidence(vehicle,t) where t:type)<computes>:int=H.Use(X,D)"),
  ("virtual method proof input", "
reader:=interface<computes>:
    Use(X:t,D:evidence(vehicle,t) where t:type)<computes>:int
left:=class<computes>(reader):
    Use<override>(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=X.N
right:=class<computes>(reader):
    Use<override>(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=X.N+1
Caller(H:reader,X:t,D:evidence(vehicle,t) where t:type)<computes>:int=H.Use(X,D)"),
  ("dummy method receiver", "
Caller(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=D.Up(X).N"),
  ("dummy function receiver", "
Caller(X:t,D:type{_(:t)<computes>:vehicle} where t:type)<computes>:int=D(X).N"),
  ("returned dummy function receiver", "
Keep(X:u where u:type)<computes>:u=X
Caller(X:t,D:type{_(:t)<computes>:vehicle} where t:type)<computes>:int=Keep(D)(X).N"),
  ("ordinary callback input", "
Use(X:t,F:type{_(:t)<computes>:vehicle} where t:type)<computes>:int=F(X).N
Caller(X:t,D:type{_(:t)<computes>:vehicle} where t:type)<computes>:int=Use(X,D)"),
  ("spawned function receiver", "
Caller(D:type{_()<suspends>:int})<suspends>:void=spawn{D()}"),
  ("returned spawned function receiver", "
Keep(X:u where u:type)<computes>:u=X
Caller(D:type{_()<suspends>:int})<suspends>:void=spawn{Keep(D)()}"),
  ("spawned method receiver", "
worker:=class<computes>:
    Work()<suspends>:int=1
Caller(D:worker)<suspends>:void=spawn{D.Work()}"),
  ("opaque callable receiver", "
Caller(D:t,E:evidence(type{_(:int)<computes>:int},t) where t:type)<computes>:int=D(7)"),
  ("spawned opaque callable receiver", "
Caller(D:t,E:evidence(type{_(:int)<suspends>:int},t) where t:type)<suspends>:void=spawn{D(7)}")]

private def indexedInputContracts : IO Unit := do
  for position in [:4] do
    let inputs := ["K", "O", "L", "R"]
    let proof := "evidence(vehicle,vehicle)"
    let types := inputs.zipIdx |>.map fun (_, i) => if i == position then proof else "int"
    let operation := "operation(" ++ String.intercalate "," (types ++ ["int"]) ++ ")"
    let parameters := String.intercalate "," ((inputs.zip types).map fun (name, ty) => name ++ ":" ++ ty)
    let values := inputs.zipIdx |>.map fun (_, i) => if i == position then "D" else "0"
    let source := "vehicle:=class<computes>{N:int=7}\n" ++
      "operation(k:type,o:type,l:type,r:type,z:type):=class<computes>{}\n" ++
      s!"Apply(Op:{operation},{parameters})<computes>:int={inputs[position]!}" ++ ".Up(vehicle{}).N\n" ++
      s!"Caller(D:{proof},Op:{operation})<computes>:int=Indexed(Op,{values[0]!},{values[1]!},(),{values[2]!},{values[3]!})\n" ++
      "Main():void={}"
    let parsed ← getOK "indexed operation input: parse" (parseProgram source)
    let rewrite : STop → STop := fun
      | .fn p name ps tps specs ret body =>
        let body := Choice.mapE (fun
          | .app p (.ident _ "Indexed") args false => some (.app p (.ident p "$choiceIndexedOperation")
              (.str p [.text (FnValues.shapeOf 4 ["computes"]).name] :: args) false)
          | _ => none) body
        .fn p (if name == "Apply" then "operation$apply" else name) ps tps specs ret body
      | top => top
    let actual ← getOK "indexed operation: real roles" (parsed.mapM (roles false))
    let compiled ← getOK "indexed operation: real control" (elabProgram (actual.map rewrite))
    need "indexed operation: real input passes all Core checks"
      (compiled.prog.check && compiled.prog.checkControl && compiled.prog.checkTypes compiled.sigs compiled.slotTys)
    let dummy ← getOK "indexed operation: dummy roles" (parsed.mapM (roles true))
    match elabProgram (dummy.map rewrite) with
    | .ok _ => throw (IO.userError s!"indexed operation: dummy input {inputs[position]!} became executable evidence")
    | .error message =>
      need s!"indexed operation: wrong refusal: {message}"
        ((message.splitOn "dummy type value cannot").length > 1)

def main : IO Unit := do
  indexedInputContracts
  for (label, source) in cases do
    let parsed ← getOK s!"{label}: parse" (parseProgram
      ("vehicle:=class<computes>{N:int=7}\n" ++ source ++ "\nMain():void={}"))
    let actual ← getOK s!"{label}: actual roles" (parsed.mapM (roles false))
    let compiled ← getOK s!"{label}: actual proof control" (elabProgram actual)
    need s!"{label}: real proof passes all Core admission checks"
      (compiled.prog.check && compiled.prog.checkControl && compiled.prog.checkTypes compiled.sigs compiled.slotTys)
    let dummy ← getOK s!"{label}: dummy roles" (parsed.mapM (roles true))
    match elabProgram dummy with
    | .ok _ => throw (IO.userError s!"{label}: a dummy input became executable evidence")
    | .error message =>
      need s!"{label}: wrong refusal: {message}"
        ((message.splitOn "dummy type value cannot").length > 1)
  let builtins := [
    ("whole-array flatten", "Caller(A:t,D:evidence([][]int,t) where t:type)<computes>:[]int=Concatenate(A)",
      "Concatenate takes arrays, or an array of arrays"),
    ("component-array flatten", "Caller(A:[]t,D:evidence([]int,t) where t:type)<computes>:[]int=Concatenate(A)",
      "Concatenate takes arrays, or an array of arrays"),
    ("composed-array flatten", "Caller(A:t,D:evidence([]a,t),E:evidence([]int,a) where t:type,a:type)<computes>:[]int=Concatenate(A)",
      "Concatenate takes arrays, or an array of arrays"),
    ("variadic concatenate", "Caller(A:t,B:[]int,D:evidence([]int,t) where t:type)<computes>:[]int=Concatenate(A,B)",
      "Concatenate takes arrays, found t"),
    ("whole-map concatenate", "Caller(A:t,D:evidence([int]int,t) where t:type)<computes>:[int]int=ConcatenateMaps(A)",
      "ConcatenateMaps takes maps, not t"),
    ("map-value concatenate", "Caller(A:[int]t,B:[int]int,D:evidence(int,t) where t:type)<computes>:[int]int=ConcatenateMaps(A,B)",
      "ConcatenateMaps takes maps of one type"),
    ("map-key concatenate", "Caller(A:[t]int,B:[rational]int,D:evidence(rational,t) where t:subtype(comparable))<computes>:[rational]int=ConcatenateMaps(A,B)",
      "ConcatenateMaps takes maps of one type"),
    ("bounded event await", "Caller(X:t,D:evidence(event(int),t) where t:type)<suspends>:int=X.Await()",
      "t has no method 'Await'"),
    ("bounded task cancel", "Caller(X:t,D:evidence(task(int),t) where t:type)<suspends>:void=X.Cancel()",
      "t has no method 'Cancel'"),
    ("bounded unit signal", "Caller(X:t,D:evidence(event(void),t) where t:type)<transacts>:void=X.Signal()",
      "t has no method 'Signal'"),
    ("ordinary Await before redundant intrinsic", "worker:=class(event(int)):\n    Await()<computes>:int=7\nCaller(X:t,D:evidence(worker,t),E:evidence(event(int),t) where t:type)<computes>:int=X.Await()",
      "Await suspends"),
    ("ordinary Await before reversed redundant intrinsic", "worker:=class(event(int)):\n    Await()<computes>:int=7\nCaller(X:t,E:evidence(event(int),t),D:evidence(worker,t) where t:type)<computes>:int=X.Await()",
      "Await suspends")]
  for (label, source, refusal) in builtins do
    let parsed ← getOK s!"{label}: parse" (parseProgram (source ++ "\nMain():void={}"))
    let compiled ← getOK s!"{label}: actual proof control" (elabProgram (← getOK label (parsed.mapM (roles false))))
    need s!"{label}: real proof passes all Core admission checks"
      (compiled.prog.check && compiled.prog.checkControl && compiled.prog.checkTypes compiled.sigs compiled.slotTys)
    let dummy ← getOK s!"{label}: dummy roles" (parsed.mapM (roles true))
    match elabProgram dummy with
    | .ok _ => throw (IO.userError s!"{label}: a dummy input supplied a builtin view")
    | .error message => need s!"{label}: wrong refusal: {message}" ((message.splitOn refusal).length > 1)
  let t := Ty.param "t" false
  let proof := (Bound.mk (.struct "vehicle" []) t).ty
  let env : TyEnv := {
    structs := [("node", [("Next", .struct "node" [.arr t], none)]),
      ("metadata", [("$w.proof", proof, none)]), ("box", [("Value", t, none)])]
    sparams := [("node", [("t", false)]), ("box", [("t", false)])] }
  need "a polymorphically recursive declaration terminates"
    (!exposesEvidence env (.struct "node" [.int]))
  need "recursive arguments still expose actual dictionaries"
    (exposesEvidence env (.struct "node" [proof]))
  need "hidden witness fields do not expose actual evidence"
    (!exposesEvidence env (.struct "metadata" []))
  need "unconstrained generic forwarding stays opaque" (!exposesEvidence env t)
  need "declared peer domains expose evidence"
    (exposesEvidence { env with boundFacts := [(proof, .param "u" false), (.param "u" false, t)] } t)
  IO.println s!"subtype evidence input contracts passed ({cases.length} real/dummy call controls, {builtins.length} builtin controls, 4 indexed input controls)"
