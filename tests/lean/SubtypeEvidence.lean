import OpenVerse.Front.Elab
import OpenVerse.Front.SubtypeEvidence
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode

open OpenVerse OpenVerse.Front
open OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def getOK (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{label}: {message}")

private def getSome (label : String) (result : Option α) : IO α :=
  match result with
  | some value => pure value
  | none => throw (IO.userError label)

private def env : TyEnv := {
  classes := ["vehicle", "car", "truck", "node", "left", "right", "both"]
  cinfo := [("vehicle", {}), ("car", { parent := some "vehicle" }),
    ("truck", { parent := some "vehicle" }), ("node", { parent := some "vehicle" }), ("left", { isIface := true }),
    ("right", { isIface := true }), ("both", { ifaces := ["left", "right"] })]
  sparams := [("node", [("t", false)])] }

private def pos : Pos := { line := 1, col := 1, file := "subtype-evidence.verse" }

private def expectError (label needle : String) (result : Except String α) : IO Unit :=
  match result with
  | .error message => need label ((message.splitOn needle).length > 1)
  | .ok _ => throw (IO.userError s!"{label}: expected refusal")

private def resolutionContracts : IO Unit := do
  let classes := env.classes ++ ["garage", "root", "leaf", "identity_base", "identity_child"]
  let declarations := { env with
    classes
    structs := classes.map fun name => (name, [])
    cinfo := env.cinfo ++ [("garage", {}), ("root", {}), ("leaf", { parent := some "root" }),
      ("identity_base", {}), ("identity_child", { parent := some "identity_base" })]
    uniques := ["identity_base"]
    sparams := env.sparams ++ [("garage", [("g", false)]), ("root", [("r", false)]), ("leaf", [("l", false)])]
    pargs := [("leaf", [.arr (.param "l" false)])]
    sbounds := [("garage", [(.struct "vehicle" [], .param "g" false)])] }
  let params (source : String) : IO (List TParam) := do
    let tops ← getOK "parse formal bounds" (parseProgram (source ++ "\nMain():void={}"))
    getSome "missing formal parameters" (tops.findSome? fun | .fn _ "F" _ tps .. => some tps | _ => none)
  let tps ← params "F(X:v where u:subtype(garage(t)),t:subtype(vehicle),v:subtype(u)):v=X"
  let resolved ← getOK "resolve forward/generic bounds" (resolveTParams declarations tps)
  let scope := resolved.env declarations
  need "bound parameters remain opaque" ((scope.tvars.lookup "v") == some (.param "v" false))
  need "all peer relations remain available" (scope.boundSubtype (.param "v" false) (.struct "garage" [.param "t" false]))
  let _ ← getOK "formal applications use declared facts"
    ((resolveTy scope pos (.app "garage" [.name "t"])).run' { env := scope })
  let bad ← params "F(X:u where t:type,u:subtype(garage(t))):u=X"
  expectError "unproved nested generic bound" "does not satisfy subtype(vehicle)" (resolveTParams declarations bad)
  let ambient := { declarations with boundFacts := [(.struct "vehicle" [], .param "t" false)] }
  expectError "caller facts do not leak into a declaration" "does not satisfy subtype(vehicle)" (resolveTParams ambient bad)
  let tps ← params "F(X:t where t:subtype(u),u:subtype(identity_child)):t=X"
  let unique ← getOK "resolve implied comparability" (resolveTParams declarations tps)
  need "unique implication follows ancestors and peer bounds" (unique.params == [("t", true), ("u", true)])
  let tps ← params "F(X:t where t:subtype(vehicle)):t=X"
  let ordinary ← getOK "ordinary class bound" (resolveTParams declarations tps)
  need "ordinary class does not imply comparable" (ordinary.params == [("t", false)])
  let tps ← params "F(X:t where t:subtype(u),u:subtype(t)):t=X"
  let cycle ← getOK "resolve dependent cycle" (resolveTParams declarations tps)
  need "cycle does not invent comparability" (cycle.params == [("t", false), ("u", false)])
  let tps ← params "F(X:t where t:subtype(left)):t=X"
  let _ ← getOK "interface bound" (resolveTParams declarations tps)
  let tps ← params "F(X:t where t:subtype(missing)):t=X"
  expectError "unknown upper type" "unknown type 'missing'" (resolveTParams declarations tps)
  need "project generic ancestry without erasing arguments"
    (declarations.boundSubtype (.struct "leaf" [.int]) (.struct "root" [.arr .int]))
  need "incompatible generic arguments remain refused"
    (!declarations.boundSubtype (.struct "leaf" [.int]) (.struct "root" [Ty.string]))
  let good := Ty.arr (.struct "garage" [.struct "car" []])
  let _ ← getOK "closed constrained class application" (good.checkBounds declarations)
  expectError "nested bad class argument" "does not satisfy subtype(vehicle)"
    ((Ty.arr (.struct "garage" [.int])).checkBounds declarations)
  let relation : Bound := ⟨.struct "root" [.param "a" false], .param "u" false⟩
  let actual := Ty.struct "leaf" [.int]
  let inferred ← getSome "infer argument occurring only in a bound"
    (SubtypeEvidence.infer declarations [relation] [("u", actual)] true)
  need "bound projection retains precise input and solves the hidden argument"
    (inferred.lookup "u" == some actual && inferred.lookup "a" == some (.arr .int))
  let callerType := Ty.param "caller" false
  let facts := { declarations with boundFacts := [(.struct "root" [.arr .int], callerType)] }
  let inferred ← getSome "infer through an opaque nominal bound"
    (SubtypeEvidence.infer facts [relation] [("u", callerType)] true)
  need "opaque bound projection" (inferred.lookup "a" == some (.arr .int))
  let conflict := { facts with boundFacts := facts.boundFacts ++ [(.struct "root" [Ty.string], callerType)] }
  need "incompatible projections do not depend on declaration order"
    ((SubtypeEvidence.infer conflict [relation] [("u", callerType)]).isNone &&
      (SubtypeEvidence.infer { conflict with boundFacts := conflict.boundFacts.reverse } [relation] [("u", callerType)]).isNone)
  need "static facts cannot supply an executable view" ((SubtypeEvidence.views facts [] callerType).isEmpty)
  let signature : Sig := {
    idx := 0, name := "Projected", params := [.param "u" false], ret := .param "u" false,
    decides := false, isConst := false, tparams := [("a", false), ("u", false)], fx := [], bounds := [relation] }
  let functionType := Ty.struct (FnValues.shapeOf 1 ["computes"]).name [actual, actual]
  need "function-value instance uses the same bound inference"
    (fnValueArgs declarations signature functionType == some [.arr .int, actual])
  need "function value cannot replace an incompatible fixed argument"
    ((fnValueArgs declarations signature functionType [("a", Ty.string)]).isNone)
  let peerBounds : List Bound := [⟨.param "t" false, .param "u" false⟩,
    ⟨.param "t" false, .param "v" false⟩]
  let inputs := [("u", Ty.struct "car" []), ("v", Ty.struct "truck" [])]
  for constraints in [peerBounds, peerBounds.reverse] do
    for arguments in [inputs, inputs.reverse] do
      let peers ← getSome "infer a common peer upper" (SubtypeEvidence.infer declarations constraints arguments true)
      need "common peer keeps both inputs precise" (peers.lookup "t" == some (.struct "vehicle" []) &&
        peers.lookup "u" == inputs.lookup "u" && peers.lookup "v" == inputs.lookup "v")
      need "inferred common peer satisfies every relation"
        (constraints.all fun bound => declarations.boundSubtype (bound.derived.subst peers) (bound.base.subst peers))
  let chain : List Bound := peerBounds ++ [⟨.param "v" false, .param "w" false⟩]
  let peers ← getSome "infer a peer chain" (SubtypeEvidence.infer declarations chain
    [("u", .struct "car" []), ("w", .struct "truck" [])] true)
  need "peer chain aggregates all incoming types" (peers.lookup "t" == some (.struct "vehicle" []) &&
    peers.lookup "v" == some (.struct "truck" []))
  let cycleBounds : List Bound := [⟨.param "t" false, .param "u" false⟩,
    ⟨.param "u" false, .param "t" false⟩, ⟨.param "t" false, .param "w" false⟩]
  let peers ← getSome "infer a reached peer cycle"
    (SubtypeEvidence.infer declarations cycleBounds [("w", .struct "car" [])] true)
  need "cycle receives a known lower type" (peers.lookup "t" == some (.struct "car" []) &&
    peers.lookup "u" == some (.struct "car" []))
  let deferred : List Bound := [⟨.param "t" false, .param "u" false⟩,
    ⟨.param "t" false, .struct "root" [.param "a" false]⟩,
    ⟨.param "a" false, .param "w" false⟩]
  let peers ← getSome "infer a deferred compound lower" (SubtypeEvidence.infer declarations deferred
    [("u", actual), ("w", .arr .int)] true)
  need "compound lower cannot prematurely freeze the peer upper"
    (peers.lookup "t" == some (.struct "root" [.arr .int]))
  let ambiguous := { declarations with
    classes := declarations.classes ++ ["other_both"]
    cinfo := declarations.cinfo ++ [("other_both", { ifaces := ["left", "right"] })] }
  let ambiguousInputs := [("u", Ty.struct "both" []), ("v", Ty.struct "other_both" [])]
  need "unrelated common interfaces need an explicit choice"
    ((SubtypeEvidence.infer ambiguous peerBounds ambiguousInputs true).isNone)
  let peers ← getSome "explicit interface upper resolves ambiguity"
    (SubtypeEvidence.infer ambiguous peerBounds (("t", .struct "left" []) :: ambiguousInputs) true)
  need "an explicit interface is a valid shared upper"
    (peerBounds.all fun bound => ambiguous.boundSubtype (bound.derived.subst peers) (bound.base.subst peers))
  let peerSignature : Sig := { signature with
    params := [.param "u" false, .param "v" false], ret := .void,
    tparams := [("t", false), ("u", false), ("v", false)], bounds := peerBounds }
  let peerFunctionType := Ty.struct (FnValues.shapeOf 2 ["computes"]).name
    [.struct "car" [], .struct "truck" [], .void]
  need "function-value matching aggregates peer lower types" (fnValueArgs declarations peerSignature peerFunctionType ==
    some [.struct "vehicle" [], .struct "car" [], .struct "truck" []])
  let flagInputs := [("u", Ty.arr (.param "q" true)), ("v", Ty.arr (.param "q" false))]
  for arguments in [flagInputs, flagInputs.reverse] do
    let peers ← getSome "infer a common type without inventing comparability"
      (SubtypeEvidence.infer declarations peerBounds arguments true)
    need "inferred peer intersects comparable guarantees"
      (((peers.lookup "t").getD .void).paramsC == [("q", false)])
  let weakFacts := { declarations with boundFacts :=
    [(.struct "root" [.param "q" true], callerType), (.struct "root" [.param "q" false], callerType)] }
  let inferred ← getSome "infer nominal argument with weaker guarantees"
    (SubtypeEvidence.infer weakFacts [relation] [("u", callerType)] true)
  need "nominal projections cannot select the first comparable flag"
    (((inferred.lookup "a").getD .void).paramsC == [("q", false)])
  let constrained := { declarations with sbounds :=
    [("node", [(.struct "vehicle" [], .param "t" false)])] }
  let dictionary ← getOK "retain bounds on a nominal dictionary family"
    (nominal constrained pos "node" "vehicle")
  match dictionary with
  | .classDef _ _ [parameter] .. =>
    need "a generic dictionary does not erase its nominal parameter bound"
      (reprStr parameter.upperBound == reprStr (some (STy.name "vehicle")))
  | _ => throw (IO.userError "unexpected nominal dictionary declaration")

private partial def protocolParams (body : SExpr) : List TParam :=
  let own := match body with
    | .app _ (.ident _ marker) args false =>
      if ["$tparams", "$params", "$defaults"].contains marker then
        let offset := if marker == "$tparams" then 1 else 2
        (args.drop offset).filterMap fun arg => (TParam.ofMarker arg).toOption
      else []
    | _ => []
  own ++ body.children.flatMap protocolParams

private def metadataContracts : IO Unit := do
  let source := "M:=module:\n    vehicle(t:type):=class<computes>{Value:t}\n    F(X:u where t:type,u:subtype(vehicle(t))):u=X\n    packet(t:type,u:subtype(vehicle(t))):=struct{Value:u}\n    boxed(t:type,u:subtype(vehicle(t))):=class{Value:u}\nMain():void={}"
  let parsed ← getOK "parse bound metadata" (parseProgram source)
  let resolved ← getOK "resolve bound metadata" (resolveModules parsed)
  for name in ["M::F", "M::packet", "M::boxed"] do
    let params ← getSome s!"missing bound declaration {name}" (resolved.findSome? fun
      | .fn _ n _ tps .. | .classDef _ n tps .. => if n == name then some tps else none
      | .const _ n _ (.structDef _ tps _ _) => if n == name then some tps else none
      | _ => none)
    let bound ← getSome s!"missing bound in {name}" ((params.find? (·.name == "u")).bind (·.upperBound))
    need s!"qualified parametric bound lost in {name}"
      (reprStr bound == reprStr (STy.app "M::vehicle" [.name "t"]))
  let parameter := TParam.withUpperBound pos "u" (.app "vehicle" [.name "t"])
  let renamed := parameter.rename [("u", "$result"), ("t", "$element")]
  let decoded ← getOK "bound marker round trip" (TParam.ofMarker (renamed.marker pos))
  need "bound marker retains dependent type" (decoded.name == "$result" &&
    reprStr decoded.upperBound == reprStr (some (STy.app "vehicle" [.name "$element"])))
  need "type metadata creates no lexical binding" ((Choice.localsOf (renamed.marker pos)).isEmpty)
  need "malformed bound marker refused"
    ((TParam.ofMarker (.tuple pos [.ident pos "u", .ident pos "vehicle", .int pos 7])).toOption.isNone)
  let source := "vehicle(t:type):=class<computes>{Value:t}\ncar:=class<computes>(vehicle(int)){}\nF(X:u,?Y:u=X where t:type,u:subtype(vehicle(t)))<computes>:u=X|Y\nMain():void=for(X:=F(car{})):Print(\"ok\")"
  let parsed ← getOK "parse inlined bound metadata" (parseProgram source)
  let (inlined, _) ← getOK "inline bound metadata" (Choice.inlineMulti parsed [])
  let constraints := inlined.flatMap fun
    | .fn _ _ _ _ _ _ body | .const _ _ _ body => protocolParams body
    | _ => []
  let bounded := constraints.filter (·.upperBound.isSome)
  need "inlining retains bounds" (!bounded.isEmpty)
  for bound in bounded do
    match bound.upperBound with
    | some (.app "vehicle" [.name element]) =>
      need "inlining renames peer parameter in the bound" (element.startsWith "$tp" &&
        constraints.any (fun parameter => parameter.name == element && parameter.constraint == "type"))
    | _ => throw (IO.userError s!"inlining lost the bound type: {reprStr bound}")
  for (source, needed) in [
      ("F(X:t where t:subtype(event(int))):t=X", "event"),
      ("C(t:subtype(task(int))):=class{}", "task"),
      ("S(t:subtype(sticky_event(int))):=struct{}", "sticky_event")] do
    let tops ← getOK "parse bound library dependencies" (parseProgram (source ++ "\nMain():void={}"))
    need s!"prelude sees upper-bound dependency {needed}" ((PreludeNeeds.uses tops).contains needed)
  let shadowed ← getOK "parse peer named event"
    (parseProgram "F(X:t where event:type,t:subtype(event)):t=X\nMain():void={}")
  need "a bound peer is not a nominal prelude dependency" (!(PreludeNeeds.uses shadowed).contains "event")

private def rewrite (replacements : List (String × SExpr)) (body : SExpr) : Except String SExpr := do
  let rename (name : String) := if name == "evidence" then family else name
  let r : Resolver := {
    val := fun _ name => pure (rename name), ty := fun _ name => pure (rename name),
    bind := fun _ _ => pure (), qual := fun _ _ => pure none }
  let body := Choice.mapE (fun
    | .app _ (.ident _ name) [] false => replacements.lookup name
    | _ => none) body
  body.mapNamesM r

private partial def rewriteTop (replacements : List (String × SExpr)) : STop → Except String STop
  | .fn p name ps tps specs ret body => do
    let rename (name : String) : Except String String := pure (if name == "evidence" then family else name)
    let ps ← ps.mapM fun param => do
      let ty ← param.ty.mapNamesM rename
      let value ← param.default.mapM (rewrite replacements)
      return { param with ty, default := value }
    return .fn p name ps tps specs (← ret.mapNamesM rename) (← rewrite replacements body)
  | .classDef p name tps specs parents iface fields overrides methods => do
    let rename (name : String) : Except String String := pure (if name == "evidence" then family else name)
    let fields ← fields.mapM fun (name, ty, value, mutable) => do
      return (name, ← ty.mapNamesM rename, ← value.mapM (rewrite replacements), mutable)
    return .classDef p name tps specs (← parents.mapM (·.mapNamesM rename)) iface fields overrides
      (← methods.mapM (rewriteTop replacements))
  | .const p name ty body => return .const p name ty (← rewrite replacements body)

private def source := "
vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string=\"car\"}
truck:=class<computes>(vehicle){Name:string=\"truck\"}
node(t:type):=class<computes>(vehicle){Value:t}
box(t:type):=class<computes>{Value:t}
Process(X:t,D:evidence(vehicle,t) where t:type)<computes>:t=
    Print(\"speed {X.Speed}\")
    X
UseBox(B:box(t),D:evidence(vehicle,t) where t:type)<computes>:t=Process(B.Value,D)
closure(t:type):=class<computes>:
    B:box(t)
    D:evidence(vehicle,t)
    Run()<computes>:t=UseBox(B,D)
Bind(B:box(t),D:evidence(vehicle,t) where t:type)<computes>:type{_()<computes>:t}=
    closure(t){B:=B,D:=D}.Run
Walk(X:t,D:evidence(vehicle,t),N:int where t:type)<computes>:int=
    if(N>0):
        Y:=node(t){Value:=X,Speed:=N}
        return Walk(Y,NodeEvidence(),N-1)
    D.Up(X).Speed
Widen(Base:t,Derived:u,D:evidence(t,u) where t:type,u:type)<computes>:t=Derived
ReadBound(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=X.ReadSpeed()
BindBound(X:t,D:evidence(vehicle,t) where t:type)<computes>:type{_()<computes>:int}=X.ReadSpeed
AsBase(X:t,D:evidence(vehicle,t) where t:type)<computes>:vehicle=X
Both(X:u,Y:v,DX:evidence(t,u),DY:evidence(t,v) where t:type,u:type,v:type)<computes>:t=X
Main():void=
    C:=car{Speed:=9,Name:=\"precise\"}
    R:=Process(C,CarEvidence())
    Print(\"name {R.Name}\")
    F:=Bind(box(car){Value:=C},CarEvidence())
    Print(\"escape {F().Name}\")
    Print(\"poly {Walk(C,CarEvidence(),3)}\")
    Print(\"composed {Widen(vehicle{},C,ComposedEvidence()).Speed}\")
    Print(\"identity {Widen(1,7,IntEvidence())}\")
    Print(\"method {ReadBound(C,CarEvidence())}\")
    BoundMethod:=BindBound(C,CarEvidence())
    Print(\"bound method {BoundMethod()}\")
    Print(\"widened {AsBase(C,CarEvidence()).Speed}\")
    T:=truck{Speed:=4}
    Print(\"both {Both(C,T,CarEvidence(),TruckEvidence()).Speed}\")
    Print(\"reverse both {Both(T,C,TruckEvidence(),CarEvidence()).Speed}\")
"

private def trace := "speed 9\nname precise\nspeed 9\nescape precise\npoly 1\ncomposed 9\nidentity 7\nmethod 9\nbound method 9\nwidened 9\nboth 9\nreverse both 4\n"

private def stateSource := "
vehicle:=class<allocates>:
    var N:int=0
    var Items:[]int=array{1}
    ReadN()<reads>:int=N
car:=class<allocates>(vehicle){Name:string=\"car\"}
Touch(X:t,D:evidence(vehicle,t) where t:type)<transacts>:t=
    Print(\"touch\")
    set X.N+=1
    X
BindN(X:t,D:evidence(vehicle,t) where t:type)<computes>:type{_()<reads>:int}=X.ReadN
SetPath(A:t,B:t,D:evidence(vehicle,t) where t:type)<transacts>:void=
    var X:t=A
    if(set X.Items[if(set X=B,true?)then 0 else 1]=7):Print(\"path\")
Main():void=
    A:=car{Name:=\"a\",Items:=array{1}}
    B:=car{Name:=\"b\",N:=10,Items:=array{2}}
    D:=CarEvidence()
    Returned:=Touch(A,D)
    Print(\"identity {Returned.Name} {A.N}\")
    if(Touch(A,D),false?)then Print(\"bad\")else Print(\"rolled\")
    Print(\"rollback {A.N}\")
    Live:=BindN(A,D)
    set A.N=4
    Print(\"live {Live()}\")
    SetPath(A,B,D)
    if(AV:=A.Items[0],BV:=B.Items[0]):Print(\"path values {AV} {BV}\")
"

private def stateTrace := "touch\nidentity a 1\nrolled\nrollback 1\nlive 4\npath\npath values 1 7\n"

private def witness (base derived : Ty) : SExpr :=
  .app pos (.ident pos "$subtypeWitness")
    [.construct pos family [base.toSTy, derived.toSTy] []] false

private def receiverSource := "
vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string=\"precise\"}
readable:=interface<computes>:
    Read()<computes>:int
root(a:type,b:type):=interface<computes>:
    Read()<computes>:int
carrier(s:type,t:type):=class<computes>(readable,root(t,s)):
    X:s
    Label:t
    ReceiverEvidence:evidence(vehicle,s)
    Read<override>()<computes>:int=X.Speed
    Reveal()<computes>:s=X
    Bind()<computes>:type{_()<computes>:int}=X.ReadSpeed
child(u:type):=class<computes>(carrier(u,int)){}
ReadVia(R:root(a,b) where a:type,b:type)<computes>:int=R.Read()
Main():void=
    C:=car{Speed:=9}
    H:=carrier(car,string){X:=C,Label:=\"label\",ReceiverEvidence:=CarEvidence()}
    F:=H.Bind()
    Print(\"direct {H.Read()} {H.Reveal().Name} {F()}\")
    R:readable=H
    Print(\"opened {R.Read()}\")
    Print(\"permuted {ReadVia(H)}\")
    K:=child(car){X:=car{Speed:=4},Label:=7,ReceiverEvidence:=CarEvidence()}
    I:readable=K
    Print(\"inherited {I.Read()} {K.Reveal().Name}\")
"

private def receiverTrace := "direct 9 precise 9\nopened 9\npermuted 9\ninherited 4 precise\n"

private def receiverStateSource := "
vehicle:=class<allocates>:
    var N:int=0
    ReadN()<reads>:int=N
car:=class<allocates>(vehicle){Name:string=\"a\"}
carrier(s:type,t:type):=class<computes>:
    X:s
    Label:t
    ReceiverEvidence:evidence(vehicle,s)
    Touch()<transacts>:s=
        V:=X
        Print(\"touch\")
        set V.N+=1
        X
    Bind()<computes>:type{_()<reads>:int}=X.ReadN
    Read()<reads>:int=X.N
Main():void=
    A:=car{}
    H:=carrier(car,int){X:=A,Label:=7,ReceiverEvidence:=CarEvidence()}
    R:=H.Touch()
    Print(\"identity {R.Name} {A.N}\")
    if(H.Touch(),false?)then Print(\"bad\")else Print(\"rolled\")
    Print(\"rollback {H.Read()}\")
    F:=H.Bind()
    set A.N=4
    Print(\"live {F()}\")
"

private def receiverStateControlSource := receiverStateSource
  |>.replace "V:=X" "V:=ReceiverEvidence.Up(X)"
  |>.replace "=X.ReadN" "=ReceiverEvidence.Up(X).ReadN"
  |>.replace "=X.N" "=ReceiverEvidence.Up(X).N"

private def receiverStateTrace := "touch\nidentity a 1\nrolled\nrollback 1\nlive 4\n"

private def receiverCancelSource := "
vehicle:=class<allocates>{var N:int=0}
car:=class<allocates>(vehicle){Name:string=\"a\"}
carrier(s:type,t:type):=class<computes>:
    X:s
    Label:t
    ReceiverEvidence:evidence(vehicle,s)
    Run()<suspends>:void=
        V:=X
        defer:Print(\"cleanup {V.N}\")
        set V.N=5
        Sleep(10.0)
        Print(\"bad\")
Main()<suspends>:void=
    A:=car{}
    H:=carrier(car,int){X:=A,Label:=7,ReceiverEvidence:=CarEvidence()}
    race:
        H.Run()
        block:
            Sleep(0.0)
            Print(\"winner\")
    Print(\"after {A.N} {A.Name}\")
"

private def receiverCancelControlSource := receiverCancelSource
  |>.replace "V:=X" "V:=ReceiverEvidence.Up(X)"

/-- Compiler-API fixture: explicit, checked source dictionaries become private
    receiver fields. Source upper-bound syntax is still guarded. -/
private partial def receiverFields : STop → STop
  | .classDef p owner params specs parents iface fields overrides methods =>
    .classDef p owner params specs parents iface
      (fields.map fun (name, ty, value, mutable) =>
        (if name == "ReceiverEvidence" then fieldName "carrier" "s" else name,
         ty, value.map privateFields, mutable)) overrides (methods.map receiverFields)
  | .fn p name ps params specs ret body => .fn p name ps params specs ret (privateFields body)
  | .const p name ty body => .const p name ty (privateFields body)
where
  privateFields (body : SExpr) : SExpr := Choice.mapE (fun
    | .ident p "ReceiverEvidence" => some (.ident p (fieldName "carrier" "s"))
    | .member p value "ReceiverEvidence" =>
      some (.member p (privateFields value) (fieldName "carrier" "s"))
    | .construct p name ts fields => some (.construct p name ts (fields.map fun
        | .decl p name ty mutable value => .decl p
            (if name == "ReceiverEvidence" then fieldName "carrier" "s" else name)
            ty mutable (privateFields value)
        | value => privateFields value))
    | .decl p "ReceiverEvidence" ty mutable value =>
      some (.decl p (fieldName "carrier" "s") ty mutable value)
    | _ => none) body

private def receiverContracts : IO Unit := do
  let t := Ty.param "t" false
  let u := Ty.param "u" false
  let v := Ty.param "v" false
  let vehicle := Ty.struct "vehicle" []
  let one := fieldName "holder" "one"
  let two := fieldName "holder" "two"
  let three := fieldName "holder" "three"
  let declarations := { env with
    classes := "holder" :: env.classes
    structs := [("holder", [(one, (Bound.mk vehicle t).ty, none),
      (two, (Bound.mk t u).ty, none), (three, (Bound.mk u v).ty, none),
      ("$w.proof", (Bound.mk vehicle v).ty, none), ("UserProof", (Bound.mk vehicle v).ty, none)])] }
  let locals := [("Self", Ty.struct "holder" [])]
  let plan ← getSome "receiver evidence follows every field in a single local"
    (find? declarations locals ⟨vehicle, v⟩)
  need "receiver plan uses checked fields" (plan.valid declarations locals && plan.usesLocal)
  need "receiver plan cannot survive a missing or changed receiver"
    (!plan.valid declarations [] && !plan.valid declarations [("Self", .int)])
  need "receiver evidence excludes type-value and arbitrary user fields"
    ((capabilities declarations locals).length == 3)
  need "value structs cannot supply implicit receiver evidence"
    ((capabilities { declarations with classes := env.classes } locals).isEmpty)
  let mutable := { declarations with varFields := [("holder", one)] }
  need "mutable dictionary fields cannot authorize a view"
    ((find? mutable locals ⟨vehicle, v⟩).isNone && !plan.valid mutable locals)
  need "shadowed receiver cannot expose an older lexical value"
    ((find? declarations (("Self", .int) :: locals) ⟨vehicle, v⟩).isNone)
  let receiverCtx : Ctx := {
    sigs := [], sigProg := { fns := [], main := 0 }
    types := declarations
    locals := [{ name := "Self", slot := 8, ty := .struct "holder" [], mutable := false }] }
  need "receiver facts participate in inference" (receiverCtx.evidenceEnv.boundSubtype v vehicle)
  let generic := { declarations with
    structs := [("holder", [(one, (Bound.mk vehicle t).ty, none)])]
    sparams := [("holder", [("t", false)])] }
  let captured := [("Self", Ty.struct "holder" [u])]
  let plan ← getSome "instantiate receiver proof type" (find? generic captured ⟨vehicle, u⟩)
  need "same field name with another instance is not evidence"
    (!plan.valid generic [("Self", .struct "holder" [v])])
  need "receiver constraints use the current resolved layout"
    (fieldsForBounds generic
      (.struct "holder" [u]) [⟨vehicle, u⟩, ⟨vehicle, v⟩] == [(0, 0)])
  let defaultEnv := { generic with
    structs := generic.structs ++ [("vehicle", []), (family, [])]
    sparams := generic.sparams ++ [(family, [("a", false), ("d", false)])] }
  let defaultCtx : Ctx := {
    sigs := [], sigProg := { fns := [], main := 0 }, types := defaultEnv
    locals := [{ name := "ActualProof", slot := 19, ty := (Bound.mk vehicle u).ty, mutable := false }] }
  let (actual, _) ← getOK "proof defaults use the caller's actual dictionary"
    ((elabFieldDefault defaultCtx pos "holder" [u] one (Bound.mk vehicle u).ty
      (witness vehicle t)).run { env := defaultEnv })
  need "default proof has no borrowed declaration frame slot" (reprStr actual == reprStr (Expr.local 19))
  let receiverFrame : Frame := {
    explicit := [.struct "holder" [u]], params := [("u", false)],
    bounds := [⟨vehicle, u⟩], selfBounds := [(0, 0)] }
  let (inits, _) ← getOK "initialize evidence from the current receiver"
    ((elabReceiverEvidence defaultCtx pos receiverFrame).run { env := defaultEnv })
  need "receiver initialization reads its own field"
    (reprStr inits == reprStr [Expr.heap (.get 0) [.local 0]])
  expectError "receiver initialization refuses an unrelated field type" "wrong type"
    ((elabReceiverEvidence defaultCtx pos { receiverFrame with bounds := [⟨vehicle, v⟩] }).run
      { env := defaultEnv })
  expectError "receiver initialization refuses a missing field" "field is missing"
    ((elabReceiverEvidence defaultCtx pos { receiverFrame with selfBounds := [(0, 8)] }).run
      { env := defaultEnv })
  let formal := { defaultCtx with
    types := { defaultEnv with tvars := [("t", t)], boundFacts := [(vehicle, t)] }
    locals := [], defaults := [("holder", one)], inDefaultCheck := true }
  let (checked, _) ← getOK "formal proof default is checked under the declaration's bound"
    ((elabE formal (witness vehicle t) (some (Bound.mk vehicle t).ty)).run { env := defaultEnv })
  need "formal default placeholder has the exact dictionary type" (checked.ty == (Bound.mk vehicle t).ty)
  expectError "a formal placeholder cannot become executable evidence" "does not satisfy subtype(vehicle)"
    ((elabE { formal with inDefaultCheck := false } (witness vehicle t) none).run { env := defaultEnv })
  expectError "ordinary defaults do not acquire compiler proof privileges" "does not satisfy subtype(vehicle)"
    ((elabE { formal with defaults := [("holder", "UserProof")] } (witness vehicle t) none).run
      { env := defaultEnv })
  let _ ← getOK "nested construction is checked formally before real evidence is available"
    ((elabFieldDefault { defaultCtx with
      locals := [], inDefaultCheck := true
      types := { defaultEnv with boundFacts := [(vehicle, u)] } }
      pos "holder" [u] one (Bound.mk vehicle u).ty (witness vehicle t)).run { env := defaultEnv })
  expectError "formal constraints alone cannot execute a proof default" "does not satisfy subtype(vehicle)"
    ((elabFieldDefault { defaultCtx with locals := [], types := { defaultEnv with
      boundFacts := [(vehicle, u)] } } pos "holder" [u] one (Bound.mk vehicle u).ty
      (witness vehicle t)).run { env := defaultEnv })
  let parsed ← getOK "parse bounded class fields"
    (parseProgram "holder(t:subtype(vehicle)):=class<computes>{X:t}\npacket(t:subtype(vehicle)):=struct{X:t}\nMain():void={}")
  let added := addFields parsed
  need "proof field injection is idempotent" (reprStr (addFields added) == reprStr added)
  let fields ← getSome "missing generated proof field" (added.findSome? fun
    | .classDef _ "holder" _ _ _ _ fields .. => some fields
    | _ => none)
  need "bounded class carries one readonly typed proof with a checked default"
    (fields.length == 2 && fields.any fun (name, ty, value, mutable) =>
      name == fieldName "holder" "t" && !mutable && value.isSome &&
      reprStr ty == reprStr (STy.app family [.name "vehicle", .name "t"]))
  let packet (tops : List STop) := tops.findSome? fun
    | .const _ "packet" _ body => some (reprStr body)
    | _ => none
  need "value struct representation is unchanged" (packet parsed == packet added)

private def resultInferenceContracts : IO Unit := do
  let t := Ty.param "t" false
  let vehicle := Ty.struct "vehicle" []
  let car := Ty.struct "car" []
  let types := { env with structs := env.classes.map fun name => (name, []) }
  let identity : Sig := {
    idx := 0, name := "BoundIdentity", params := [t], ret := t,
    decides := false, isConst := false, pnames := ["X"], tparams := [("t", false)],
    fx := [], bounds := [⟨vehicle, t⟩] }
  for (pattern, actual, expected) in [(t, car, Ty.any), (.arr t, .arr car, .arr .any)] do
    let signature := { identity with params := [pattern], ret := pattern }
    let ctx : Ctx := {
      sigs := [signature], sigProg := { fns := [], main := 0 }, types,
      locals := [{ name := "X", slot := 0, ty := actual, mutable := false }] }
    for resultType in [none, some expected] do
      let (result, _) ← getOK "a wider result context preserves a valid closed argument instance"
        ((elabGenericCallWith elabE ctx pos signature [.ident pos "X"] resultType).run
          { env := types, nslots := 1, slotTys := #[actual] })
      need "result inference retains the precise argument type" (result.ty == actual)
    expectError "fixed invalid instances remain refused" "does not satisfy subtype(vehicle)"
      ((elabGenericCallWith elabE ctx pos signature [.ident pos "X"] (some expected)
        (inst := [("t", .any)])).run { env := types, nslots := 1, slotTys := #[actual] })

private def defaultSource := "
vehicle:=class<computes>{Speed:int=7}
car:=class<computes>(vehicle){}
F(X:t,?D:evidence(vehicle,t)=DefaultEvidence() where t:type)<computes>:int=X.Speed
holder:=class<computes>:
    D:evidence(vehicle,car)=CarEvidence()
    Value()<computes>:int=D.Up(car{}).Speed
Main():void=
    Print(\"named {F(car{Speed:=9})}\")
    H:=holder{}
    Print(\"field {H.Value()}\")
"

private def defaultTrace := "named 9\nfield 7\n"

private def stateControlSource := stateSource
  |>.replace "    set X.N+=1" "    V:=D.Up(X)\n    set V.N+=1"
  |>.replace "=X.ReadN" "=D.Up(X).ReadN"
  |>.replace "    var X:t=A" "    var X:vehicle=D.Up(A)"
  |>.replace "if(set X=B,true?)" "if(set X=D.Up(B),true?)"

private def cancelSource := "
vehicle:=class<allocates>{var N:int=0}
car:=class<allocates>(vehicle){Name:string=\"a\"}
Worker(X:t,D:evidence(vehicle,t) where t:type)<suspends>:void=
    defer:Print(\"cleanup {X.N}\")
    set X.N=5
    Sleep(10.0)
    Print(\"bad\")
Main()<suspends>:void=
    A:=car{}
    D:=CarEvidence()
    race:
        Worker(A,D)
        block:
            Sleep(0.0)
            Print(\"winner\")
    Print(\"after {A.N} {A.Name}\")
"

private def cancelControlSource := cancelSource
  |>.replace "{X.N}" "{D.Up(X).N}"
  |>.replace "    set X.N=5" "    V:=D.Up(X)\n    set V.N=5"

private def cancelTrace := "winner\ncleanup 5\nafter 5 a\n"

private def checkTrace (label : String) (compiled : Compiled) (expected : String) : IO Unit := do
  need s!"{label}: Core admission" (compiled.prog.check && compiled.prog.checkControl &&
    compiled.prog.checkTypes compiled.sigs compiled.slotTys)
  match compiled.prog.runB 1000000 10000 with
  | .res (.ok _, output) =>
    need s!"{label}: independent output" (ByteArray.mk (output.map Nat.toUInt8).toArray == expected.toUTF8)
  | other => throw (IO.userError s!"{label}: {reprStr other}")

/-- Run implicit call binding against a real checked callee, then move both
    evidence and its type witness to different slots in a new generic frame.
    Reroute all original calls through that frame and recheck the full program. -/
private def relocate (compiled : Compiled) : IO Compiled := do
  let index ← getSome "missing Process" (compiled.prog.fns.findIdx? (·.name == "Process"))
  let caller := Ty.param "caller" false
  let required := Bound.mk (.struct "vehicle" []) caller
  let localTypes := [caller, required.ty, caller, Ty.int, required.ty, caller]
  let types := { env with tvars := [("caller", caller)] }
  let sig : Sig := {
    idx := index, name := "Process", params := [.param "t" false], ret := .param "t" false,
    decides := false, isConst := false, pnames := ["X"], tparams := [("t", false)], fx := [],
    bounds := [⟨.struct "vehicle" [], .param "t" false⟩] }
  let ctx : Ctx := {
    sigs := [sig], sigProg := compiled.prog, types, dictBase := 5, dictVars := ["caller"],
    locals := [{ name := "X", slot := 0, ty := caller, mutable := false },
      { name := "CurrentEvidence", slot := 4, ty := required.ty, mutable := false }] }
  let state : ESt := { env := types, nslots := 6, slotTys := localTypes.toArray }
  let (result, state) ← getOK "implicit evidence call"
    ((elabGenericCallWith elabE ctx pos sig [.ident pos "X"] none).run state)
  need "implicit evidence call result remains opaque" (result.ty == caller)
  need "implicit call needs no new slot" (state.nslots == 6)
  let (widened, _) ← getOK "a bounded result can widen to any after argument inference"
    ((elabGenericCallWith elabE ctx pos sig [.ident pos "X"] (some .any)).run state)
  need "result context preserves the precise bounded call and its actual witnesses"
    (widened.ty == caller && reprStr widened.e == reprStr result.e)
  let shadowed := { ctx with locals :=
    { name := "CurrentEvidence", slot := 3, ty := .int, mutable := false } :: ctx.locals ++
    [{ name := "Live", slot := 1, ty := required.ty, mutable := false }] }
  let (visible, _) ← getOK "shadowed proof search continues to another visible dictionary"
    ((elabGenericCallWith elabE shadowed pos sig [.ident pos "X"] none).run state)
  need "the shadowed proof never becomes an executable argument"
    (reprStr visible.e == reprStr (Expr.call index [.local 0, .local 1, .local 5]))
  let badCtx := { ctx with locals := ctx.locals.take 1 }
  match (elabGenericCallWith elabE badCtx pos sig [.ident pos "X"] none).run state with
  | .error message => need "missing implicit evidence refused" ((message.splitOn "does not satisfy subtype").length > 1)
  | .ok _ => throw (IO.userError "implicit call accepted a missing dictionary")
  let wrapperIndex := compiled.prog.fns.length
  let wrapper : Fn := {
    name := "$relocatedSubtypeFrame", arity := 3, nslots := 6, decides := false, writes := false,
    body := .seq (.assign 3 (.lit (.int 0)))
      (.seq (.assign 4 (.local 1)) (.seq (.assign 5 (.local 2)) result.e)) }
  let fns := compiled.prog.fns.map fun fn =>
    { fn with body := Suspend.substCall index (fun args => .call wrapperIndex args) fn.body }
  let (params, ret) := compiled.sigs.fns[index]!
  let relocated := { compiled with
    prog := { compiled.prog with fns := fns ++ [wrapper] },
    sigs := { compiled.sigs with fns := compiled.sigs.fns ++ [(params, ret)] },
    slotTys := compiled.slotTys ++ [params ++ [.int, params[1]!, params[2]!]] }
  need "relocated generic call passes Core admission"
    (relocated.prog.check && relocated.prog.checkControl &&
      relocated.prog.checkTypes relocated.sigs relocated.slotTys)
  return relocated

private def relocateCommon (compiled : Compiled) : IO Compiled := do
  let index ← getSome "missing Both" (compiled.prog.fns.findIdx? (·.name == "Both"))
  let t := Ty.param "callerT" false
  let u := Ty.param "callerU" false
  let v := Ty.param "callerV" false
  let left := (Bound.mk t u).ty
  let right := (Bound.mk t v).ty
  let locals := [u, v, left, right, t, u, v, Ty.int, Ty.int, left, right, t, u, v]
  let types := { env with tvars := [("callerT", t), ("callerU", u), ("callerV", v)] }
  let signature : Sig := {
    idx := index, name := "Both", params := [.param "u" false, .param "v" false], ret := .param "t" false,
    decides := false, isConst := false, pnames := ["X", "Y"],
    tparams := [("t", false), ("u", false), ("v", false)], fx := [],
    bounds := [⟨.param "t" false, .param "u" false⟩, ⟨.param "t" false, .param "v" false⟩] }
  let ctx : Ctx := {
    sigs := [signature], sigProg := compiled.prog, types, dictBase := 11,
    dictVars := ["callerT", "callerU", "callerV"],
    locals := [{ name := "X", slot := 0, ty := u, mutable := false },
      { name := "Y", slot := 1, ty := v, mutable := false },
      { name := "DX", slot := 9, ty := left, mutable := false },
      { name := "DY", slot := 10, ty := right, mutable := false }] }
  let state : ESt := { env := types, nslots := 14, slotTys := locals.toArray }
  let (result, state) ← getOK "implicit common-upper call"
    ((elabGenericCallWith elabE ctx pos signature [.ident pos "X", .ident pos "Y"] none).run state)
  need "common upper uses current frame witnesses" (result.ty == t && state.nslots == 14)
  let wrapperIndex := compiled.prog.fns.length
  let moves : List Expr := [.assign 7 (.lit (.int 0)), .assign 8 (.lit (.int 0)),
    .assign 9 (.local 2), .assign 10 (.local 3), .assign 11 (.local 4), .assign 12 (.local 5), .assign 13 (.local 6)]
  let wrapper : Fn := {
    name := "$relocatedCommonUpper", arity := 7, nslots := 14,
    decides := false, writes := false, body := moves.foldr Expr.seq result.e }
  let fns := compiled.prog.fns.map fun fn =>
    { fn with body := Suspend.substCall index (fun args => .call wrapperIndex args) fn.body }
  let (params, ret) := compiled.sigs.fns[index]!
  let relocated := { compiled with
    prog := { compiled.prog with fns := fns ++ [wrapper] }
    sigs := { compiled.sigs with fns := compiled.sigs.fns ++ [(params, ret)] }
    slotTys := compiled.slotTys ++ [params ++ [.int, .int, params[2]!, params[3]!, params[4]!, params[5]!, params[6]!]] }
  need "common-upper relay passes Core admission" (relocated.prog.check && relocated.prog.checkControl &&
    relocated.prog.checkTypes relocated.sigs relocated.slotTys)
  return relocated

def main (args : List String) : IO Unit := do
  resolutionContracts
  metadataContracts
  receiverContracts
  resultInferenceContracts
  let vehicle := Ty.struct "vehicle" []
  let car := Ty.struct "car" []
  let node := Ty.struct "node" [.int]
  let t := Ty.param "t" false
  let u := Ty.param "u" false
  let v := Ty.param "v" false
  let carPlan ← getSome "missing nominal upcast" (find? env [] ⟨vehicle, car⟩)
  need "nominal plan validation" (carPlan.valid env [])
  need "wrong generic projection refused" ((find? env [] ⟨.struct "node" [Ty.string], node⟩).isNone)
  need "unrelated interfaces are not evidence" ((find? env [] ⟨.struct "left" [], .struct "right" []⟩).isNone)
  need "interface overlap remains possible" ((find? env [] ⟨.struct "left" [], .struct "both" []⟩).isSome &&
    (find? env [] ⟨.struct "right" [], .struct "both" []⟩).isSome)
  let locals := [("TU", (Bound.mk t u).ty), ("UV", (Bound.mk u v).ty)]
  let dependent ← getSome "missing transitive relation" (find? env locals ⟨t, v⟩)
  need "dependent plan validation" (dependent.valid env locals && dependent.bound env == ⟨t, v⟩)
  need "missing capture refused" (!dependent.valid env locals.tail)
  need "same-name unrelated capture refused" (!dependent.valid env [("TU", .int), ("UV", (Bound.mk u v).ty)])
  need "reverse relation refused" ((find? env locals ⟨v, t⟩).isNone)
  let cycles := [("UT", (Bound.mk u t).ty), ("TU", (Bound.mk t u).ty)]
  need "cycles terminate" ((find? env cycles ⟨v, t⟩).isNone)
  let cycleExit := cycles ++ [("TV", (Bound.mk v t).ty)]
  need "cycle does not hide later path" ((find? env cycleExit ⟨v, u⟩).isSome)
  let nominalPrefix := [("TVehicle", (Bound.mk t vehicle).ty)]
  let projected ← getSome "missing nominal/dependent composition" (find? env nominalPrefix ⟨t, car⟩)
  need "nominal/dependent composition validates" (projected.valid env nominalPrefix)
  need "compound constraint survives substitution"
    ((Bound.mk vehicle t).subst [("t", .tup [.int, .logic])] == ⟨vehicle, .tup [.int, .logic]⟩)
  let frame : Frame := {
    explicit := [.int], params := [("t", false), ("u", false), ("v", false)],
    selfParams := ["u"], bounds := [⟨vehicle, t⟩, ⟨u, v⟩], selfBounds := [(1, 9)] }
  need "mixed receiver/caller frame validates" frame.valid
  need "type witnesses stay contiguous" (frame.witnessBase == 2 &&
    frame.orderedParams.map (·.1) == ["t", "v", "u"] && frame.arity == 4)
  need "caller evidence is before type witnesses" (frame.argumentTypes == [.int, (Bound.mk vehicle t).ty, t, v])
  need "receiver evidence initializes after type witnesses" (frame.evidence ==
    [(0, ⟨vehicle, t⟩, 1), (1, ⟨u, v⟩, 5)] && frame.receiverFields == [9])
  need "invalid receiver constraint index refused" (!({ frame with selfBounds := [(2, 9)] } : Frame).valid)
  let combined := Plan.compose carPlan (.identity car)
  need "one family across closed instances" ((Plan.compose
    (.nominal "node" "vehicle" [.int]) (.identity node)).nominals ==
    (Plan.nominal "node" "vehicle" [Ty.string]).nominals)
  need "ill-typed composition refused" (!(Plan.compose carPlan (.identity .int)).valid env [])
  let replacements := [
    ("CarEvidence", carPlan.value env pos),
    ("TruckEvidence", (Plan.nominal "truck" "vehicle" []).value env pos),
    ("NodeEvidence", (Plan.nominal "node" "vehicle" [t]).value env pos),
    ("ComposedEvidence", combined.value env pos),
    ("IntEvidence", (Plan.identity .int).value env pos)]
  let tops ← getOK "parse dictionary control" (parseProgram source)
  let tops ← getOK "resolve dictionary controls" (tops.mapM (rewriteTop replacements))
  let nominals ← getOK "generate canonical nominal families"
    ([ ("car", "vehicle"), ("truck", "vehicle"), ("node", "vehicle") ].mapM fun (source, target) => nominal env pos source target)
  let compiled ← getOK "checked dictionaries" (elabProgram (protocol pos ++ nominals ++ tops))
  need "Core admission" (compiled.prog.check && compiled.prog.checkControl &&
    compiled.prog.checkTypes compiled.sigs compiled.slotTys)
  match compiled.prog.runB 1000000 10000 with
  | .res (.ok _, output) =>
    need "independent dictionary trace" (ByteArray.mk (output.map Nat.toUInt8).toArray == trace.toUTF8)
  | other => throw (IO.userError s!"dictionary execution failed: {reprStr other}")
  let relocated ← relocate compiled
  let relocated ← relocateCommon relocated
  match relocated.prog.runB 1000000 10000 with
  | .res (.ok _, output) =>
    need "relocated evidence/witness trace" (ByteArray.mk (output.map Nat.toUInt8).toArray == trace.toUTF8)
  | other => throw (IO.userError s!"relocated dictionary execution failed: {reprStr other}")
  -- Even a malformed compiler-supplied plan cannot bypass ordinary Core
  -- typing. This calls the real generated Up method at incompatible types.
  let bad := (Plan.compose carPlan (.identity .int)).value env pos
  let badMain := STop.fn pos "Main" [] [] [] (.name "void") bad
  let declarations := tops.filter fun | .fn _ "Main" .. => false | _ => true
  match elabProgram (protocol pos ++ nominals ++ declarations ++ [badMain]) with
  | .error message =>
    need "wrong composition reaches a type diagnostic" ((message.splitOn "expected").length > 1)
  | .ok _ => throw (IO.userError "ill-typed dictionary composition passed the compiler")
  let stateTops ← getOK "parse mutation/order control" (parseProgram stateSource)
  let stateTops ← getOK "rewrite mutation/order control" (stateTops.mapM (rewriteTop replacements))
  let carNominal ← getOK "state nominal dictionary" (nominal env pos "car" "vehicle")
  let state ← getOK "checked mutation/order control" (elabProgram (protocol pos ++ [carNominal] ++ stateTops))
  need "state control passes Core admission" (state.prog.check && state.prog.checkControl &&
    state.prog.checkTypes state.sigs state.slotTys)
  match state.prog.runB 1000000 10000 with
  | .res (.ok _, output) =>
    need "independent identity/rollback/live/path-order trace" (ByteArray.mk (output.map Nat.toUInt8).toArray == stateTrace.toUTF8)
  | other => throw (IO.userError s!"bound state control failed: {reprStr other}")
  let badState := stateSource.replace "Touch(X:t,D:evidence(vehicle,t) where t:type)<transacts>"
    "Touch(X:t,D:evidence(vehicle,t) where t:type)<computes>"
  let badStateTops ← getOK "parse forbidden bound write" (parseProgram badState)
  let badStateTops ← getOK "rewrite forbidden bound write" (badStateTops.mapM (rewriteTop replacements))
  let refusedWrite := elabProgram (protocol pos ++ [carNominal] ++ badStateTops)
  expectError "bound write retains its source effect budget" "<computes>" refusedWrite
  expectError "bound write names the source function" "Touch" refusedWrite
  let controlTops ← getOK "parse independent state control" (parseProgram stateControlSource)
  let controlTops ← getOK "rewrite independent state control" (controlTops.mapM (rewriteTop replacements))
  let control ← getOK "compile independent state control" (elabProgram (protocol pos ++ [carNominal] ++ controlTops))
  checkTrace "explicit state control" control stateTrace
  let cancellation ← getOK "parse cancellation control" (parseProgram cancelSource)
  let cancellation ← getOK "rewrite cancellation control" (cancellation.mapM (rewriteTop replacements))
  let cancellation ← getOK "compile cancellation control" (elabProgram (protocol pos ++ [carNominal] ++ cancellation))
  checkTrace "bound cancellation" cancellation cancelTrace
  let cancelControl ← getOK "parse explicit cancellation control" (parseProgram cancelControlSource)
  let cancelControl ← getOK "rewrite explicit cancellation control" (cancelControl.mapM (rewriteTop replacements))
  let cancelControl ← getOK "compile explicit cancellation control" (elabProgram (protocol pos ++ [carNominal] ++ cancelControl))
  checkTrace "explicit cancellation control" cancelControl cancelTrace
  let automatic := [
    ("CarEvidence", witness vehicle car),
    ("TruckEvidence", witness vehicle (.struct "truck" [])),
    ("NodeEvidence", witness vehicle (.struct "node" [t])),
    ("ComposedEvidence", witness vehicle car),
    ("IntEvidence", witness .int .int),
    ("DefaultEvidence", witness vehicle t)]
  let materialize (label source : String) : IO Compiled := do
    let parsed ← getOK s!"{label}: parse" (parseProgram source)
    let rewritten ← getOK s!"{label}: rewrite" (parsed.mapM (rewriteTop automatic))
    let full ← getOK s!"{label}: compile" (elabProgram rewritten)
    let strict ← getOK s!"{label}: choice-free compile" (elabProgram rewritten { profile := .choiceFree })
    need s!"{label}: profile preserves admitted bytecode" (full.prog.encode == strict.prog.encode)
    return full
  let materialized ← materialize "automatic dictionaries" source
  checkTrace "automatic dictionaries" materialized trace
  need "materialization finishes every request" materialized.subtypeNeeds.isEmpty
  for source in ["car", "truck", "node"] do
    let name := nominalFamily source "vehicle" ++ ".Up"
    need s!"one generic dictionary family for {source}"
      ((materialized.prog.fns.filter (·.name == name)).length == 1)
  let autoState ← materialize "automatic state" stateSource
  checkTrace "automatic state" autoState stateTrace
  let autoCancel ← materialize "automatic cancellation" cancelSource
  checkTrace "automatic cancellation" autoCancel cancelTrace
  let autoDefaults ← materialize "automatic defaults" defaultSource
  checkTrace "automatic defaults" autoDefaults defaultTrace
  let receiverTops ← getOK "parse receiver dictionaries" (parseProgram receiverSource)
  let receiverTops ← getOK "rewrite receiver dictionaries" (receiverTops.mapM (rewriteTop automatic))
  let receiverTops := receiverTops.map receiverFields
  let receiver ← getOK "checked receiver dictionaries" (elabProgram receiverTops)
  checkTrace "receiver dictionaries" receiver receiverTrace
  let strictReceiver ← getOK "choice-free receiver dictionaries"
    (elabProgram receiverTops { profile := .choiceFree })
  need "receiver dictionaries preserve admitted profile bytecode"
    (receiver.prog.encode == strictReceiver.prog.encode)
  let receiverCompile (label source : String) : IO Compiled := do
    let parsed ← getOK s!"{label}: parse" (parseProgram source)
    let rewritten ← getOK s!"{label}: rewrite" (parsed.mapM (rewriteTop automatic))
    getOK s!"{label}: compile" (elabProgram (rewritten.map receiverFields))
  let receiverState ← receiverCompile "receiver state" receiverStateSource
  checkTrace "receiver state" receiverState receiverStateTrace
  let receiverStateControl ← receiverCompile "explicit receiver state" receiverStateControlSource
  checkTrace "explicit receiver state" receiverStateControl receiverStateTrace
  let receiverCancel ← receiverCompile "receiver cancellation" receiverCancelSource
  checkTrace "receiver cancellation" receiverCancel cancelTrace
  let receiverCancelControl ← receiverCompile "explicit receiver cancellation" receiverCancelControlSource
  checkTrace "explicit receiver cancellation" receiverCancelControl cancelTrace
  let entryTops ← getOK "entry-only dictionary declarations"
    (parseProgram "vehicle:=class<computes>{Speed:int=9}\ncar:=class<computes>(vehicle){}\nMain():void={}")
  let entry := SExpr.member pos
    (.app pos (.member pos (witness vehicle car) "Up") [.construct pos "car" [] []] false) "Speed"
  let autoEntry ← getOK "entry-only dictionary discovery" (elabProgram entryTops { entry := some entry })
  let strictEntry ← getOK "choice-free entry-only dictionary discovery"
    (elabProgram entryTops { entry := some entry, profile := .choiceFree })
  need "entry dictionary preserves admitted bytecode" (autoEntry.prog.encode == strictEntry.prog.encode)
  checkTrace "entry-only dictionary discovery" autoEntry "9\n"
  let badRequest := STop.classDef pos "$subtypeNominalBad" [] ["predicts"] [] false [] [] []
  let main := STop.fn pos "Main" [] [] [] (.name "void") (.tuple pos [])
  expectError "materialized dictionary effects remain checked" "<predicts>"
    (elabProgramCore [main] { subtypeRequests := [badRequest] })
  let task := STy.app "task" [.name "int"]
  let taskDictionary := STop.classDef pos "$subtypeNominalPrelude" [] ["computes"]
    [.app family [task, task]] false [] []
    [.fn pos "Up" [{ name := "X", ty := task }] [] ["override", "computes"] task (.ident pos "X")]
  let _ ← getOK "materialized subtype request loads its own library types"
    (elabProgram [main] { subtypeRequests := [taskDictionary] })
  if let [out] := args then
    IO.FS.writeBinFile (out ++ "/evidence.vbc") compiled.prog.encode
    IO.FS.writeFile (out ++ "/evidence.expected") trace
    IO.FS.writeBinFile (out ++ "/relocated.vbc") relocated.prog.encode
    IO.FS.writeFile (out ++ "/relocated.expected") trace
    IO.FS.writeBinFile (out ++ "/state.vbc") state.prog.encode
    IO.FS.writeFile (out ++ "/state.expected") stateTrace
    for (name, compiled, expected) in [("state-control", control, stateTrace),
        ("cancel", cancellation, cancelTrace), ("cancel-control", cancelControl, cancelTrace),
        ("materialized", materialized, trace), ("materialized-state", autoState, stateTrace),
        ("materialized-cancel", autoCancel, cancelTrace), ("materialized-defaults", autoDefaults, defaultTrace),
        ("materialized-entry", autoEntry, "9\n"), ("receiver", receiver, receiverTrace),
        ("receiver-state", receiverState, receiverStateTrace),
        ("receiver-state-control", receiverStateControl, receiverStateTrace),
        ("receiver-cancel", receiverCancel, cancelTrace),
        ("receiver-cancel-control", receiverCancelControl, cancelTrace)] do
      IO.FS.writeBinFile (out ++ s!"/{name}.vbc") compiled.prog.encode
      IO.FS.writeFile (out ++ s!"/{name}.expected") expected
  IO.println "subtype dictionary contracts passed (checked Core, precise/escaping results, inference, member calls/coercion, state/order/rollback/cancellation)"
