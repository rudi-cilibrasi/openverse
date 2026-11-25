import OpenVerse.Front.Elab
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode

/-!
The storage audit of #572. Each case is one program compiled twice through the
compiler API: once with every parameter real, and once with only `Caller.Dummy`
marked `SParam.typeValue`. The real compile is always admitted.

* `refusals` execute what the dummy reached through some storage: the marked
  compile is refused.
* `forwards` never execute it: the marked compile is admitted.
* `conservative` never execute it either, yet the marked compile is refused
  today. These are the audit's precision findings, kept as they are so that a
  change to one of them is noticed.
* `matrix` and `overwrites` are generated: every kind of value, each way of
  using it, each storage, with and without a suspension in between.

Where `Caller` has one of the usual headers, the case is also run: a `Main`
calls it with a value, as `Dummy`, that stops the program with a user error
when executed. A refusal's real program must stop so, which shows that the
storage does carry the dummy to an executing use; the other programs must
finish, and a marked one must print what its real one prints.
-/

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
        typeValue := dummy && name == "Caller" && param.name == "Dummy" }
    return .fn p name ps tps specs (← ret.mapNamesM rename) (evidenceBody body)
  | .classDef p name nsp tps specs parents iface fields methods => do
    let rename (n : String) : Except String String :=
      pure (if n == "evidence" then SubtypeEvidence.family else n)
    let fields ← fields.mapM fun f => do return { f with ty := ← f.ty.mapNamesM rename }
    return .classDef p name nsp tps specs parents iface fields (← methods.mapM (roles dummy))
  | top => pure top

/-- `%` in a case stands for the type of a function value taking nothing. -/
private def ft : String := "type{_()<computes>:int}"

private def expand (source : String) : String := source.replace "%" ft

-- Keep function-value dispatch live: with no implementation it lowers to a user error.
private def callables : String :=
  "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:%=if(C?)then One else Two\nTrap()<computes>:int=Err()\n"

/-- A function value held in storage, then called. -/
private def fn (body : String) (prelude : String := "") (effect : String := "<transacts>")
    (result : String := "int") : String :=
  callables ++ prelude ++ "Caller(F:%,Dummy:%)" ++ effect ++ ":" ++ result ++ "=\n" ++ body

/-- The original report: a dummy `u` reaches the real conversion `P.Up`. -/
private def proof (body : String) (prelude : String := "") (effect : String := "<transacts>") : String :=
  prelude ++ "Caller(X:t,D:u,Dummy:u,P:evidence(evidence(vehicle,t),u) where t:type,u:type)" ++
    effect ++ ":int=\n" ++ body

/-- An object held in storage, then used as a method receiver. -/
private def obj (body : String) (prelude : String := "") (effect : String := "<transacts>") : String :=
  "base:=class<computes>{Read()<computes>:int=1}\nderived:=class<computes>(base){More()<computes>:int=7}\n" ++
    "trap:=class<computes>(derived){Read<override>()<computes>:int=Err();More<override>()<computes>:int=Err()}\n" ++
    prelude ++ "Caller(R:base,Dummy:base)" ++ effect ++ ":int=\n" ++ body

/-- The same, behind an interface whose method the dummy's class overrides. -/
private def goes (source : String) : String :=
  (source.replace "base:=class<computes>{" "goes:=interface<computes>{Go()<computes>:int}\nbase:=class<computes>(goes){Go<override>()<computes>:int=3;").replace
    "trap:=class<computes>(derived){" "trap:=class<computes>(derived){Go<override>()<computes>:int=Err();"

private def fcell : String :=
  "fcell:=class:\n    var Value:%\n    Put(V:%)<transacts>:void=set Value=V\n    Run()<transacts>:int=\n        G:=Value\n        G()\n"

private def sink : String :=
  "sink:=interface:\n    Put(V:%)<transacts>:void\nfcell:=class(sink):\n    var Value:%\n    Put<override>(V:%)<transacts>:void=set Value=V\n"

private def fbox : String := "fbox:=struct<computes>{Value:%}\n"

private def variance (body : String) : String :=
  "wide:=class<computes>{N:int=1}\nnarrow:=class<computes>(wide){}\nMake(W:wide)<computes>:narrow=narrow{}\nTrapMake(W:wide)<computes>:narrow=Err()\n" ++
    "Caller(F:type{_(:wide)<computes>:narrow},Dummy:type{_(:wide)<computes>:narrow})<transacts>:int=\n" ++ body

private def handler (body : String) : String :=
  "Log(N:int):void=Print(\"event {N}\")\nTrapLog(N:int):void=Err()\nCaller(F:type{_(:int):void},Dummy:type{_(:int):void}):int=\n" ++ body

private def accessors : String :=
  "acell:=class:\n    var Value<getter(GetValue)><setter(SetValue)>:%=external{}\n    var Held:?%=false\n" ++
  "    GetValue(:accessor)<transacts>:%=Held? or Err()\n    SetValue(:accessor,V:%)<transacts>:void=set Held=option{V}\n"

/-- The real program executes what `Dummy` reached; the marked one is refused. -/
private def refusals : List (String × String) := [
  -- each route in, for the storages that the generated cases give one route
  ("cell: compound append in a loop", fn "    var A:[]%=array{}\n    Rows:=for(I:=(1|2)):\n        set A+=array{Dummy}\n        I\n    if(G:=A[0])then G()else 0"),
  ("cell: swap in a loop", fn "    var A:%=F\n    var B:%=Dummy\n    Rows:=for(I:=(1|2),I=1):\n        Tmp:=A\n        set A=B\n        set B=Tmp\n        I\n    A()"),
  ("cell: generic helper's loop", fn "    Carry(Dummy,F)()" "Carry(A:v,B:v where v:type)<transacts>:v=\n    var S:v=B\n    Rows:=for(I:=(1|2)):\n        set S=A\n        I\n    S\n"),
  ("field: compound append to an array field", fn "    C:=acc{}\n    set C.Items+=array{Dummy}\n    if(G:=C.Items[0])then G()else 0" "acc:=class{var Items:[]%=array{}}\n"),
  ("field: swap of two fields", fn "    C:=two{A:=F,B:=Dummy}\n    Tmp:=C.A\n    set C.A=C.B\n    set C.B=Tmp\n    C.A()" "two:=class{var A:%;var B:%}\n"),
  ("local: swap of two array elements", fn "    var A:[]%=array{F,Dummy}\n    if(X:=A[0],Y:=A[1],set A[0]=Y,set A[1]=X){}\n    if(G:=A[0])then G()else 0"),
  ("local: swap of two map entries", fn "    var M:[int]%=map{0=>F,1=>Dummy}\n    if(X:=M[0],Y:=M[1],set M[0]=Y,set M[1]=X){}\n    if(G:=M[0])then G()else 0"),
  ("local: swap of two options", fn "    var O:?%=option{F}\n    var Q:?%=option{Dummy}\n    Tmp:=O\n    set O=Q\n    set Q=Tmp\n    if(G:=O?)then G()else 0"),
  ("local: swap of two structs' fields", fn "    var B:fbox=fbox{Value:=F}\n    var C:fbox=fbox{Value:=Dummy}\n    Tmp:=B.Value\n    set B.Value=C.Value\n    set C.Value=Tmp\n    B.Value()" fbox),
  ("local: helper's option", fn "    var O:?%=false\n    set O=Wrap(Dummy)\n    if(G:=O?)then G()else 0" "Wrap(V:v where v:type)<computes>:?v=option{V}\n"),
  ("local: helper's struct", fn "    var B:fbox=fbox{Value:=F}\n    set B=MakeBox(Dummy)\n    B.Value()" (fbox ++ "MakeBox(V:%)<computes>:fbox=fbox{Value:=V}\n")),
  ("local: helper's map", fn "    var M:[int]%=map{0=>F}\n    set M=Single(Dummy)\n    if(G:=M[0])then G()else 0" "Single(V:v where v:type)<computes>:[int]v=map{0=>V}\n"),
  -- a zero Sleep waits a tick (#724), so what follows it runs after the others' turn
  ("sleep: zero wait lets a cancelled arm's cleanup run", fn "    var Stored:%=Dummy\n    race:\n        block:\n            defer:\n                Value:=Stored()\n            loop:\n                Sleep(0.0)\n        block:\n            Sleep(0.1)\n            0" "" "<suspends>"),
  ("sleep: zero wait gives the spawning function its turn", fn "    spawn{Forever()}\n    Dummy()" "Forever()<suspends>:void=loop{Sleep(0.0)}\n" "<suspends>"),
  ("sleep: zero wait lets a sibling arm write first", fn "    var Stored:%=F\n    Values:=sync:\n        block:\n            Sleep(0.0)\n            Stored()\n        block:\n            NoWait()\n            set Stored=Dummy\n            0\n    Values(0)" "NoWait()<suspends>:void={}\n" "<suspends>"),
  ("sleep: minus zero waits as zero does", fn "    var Stored:%=F\n    Values:=sync:\n        block:\n            Sleep(-0.0)\n            Stored()\n        block:\n            NoWait()\n            set Stored=Dummy\n            0\n    Values(0)" "NoWait()<suspends>:void={}\n" "<suspends>"),
  ("sleep: zero wait in a helper lets a sibling arm write first", fn "    var Stored:%=F\n    Values:=sync:\n        block:\n            Tick()\n            Stored()\n        block:\n            NoWait()\n            set Stored=Dummy\n            0\n    Values(0)" "Tick()<suspends>:void=Sleep(0.0)\nNoWait()<suspends>:void={}\n" "<suspends>"),
  -- plain locals
  ("local: compound array append", fn "    var A:[]%=array{}\n    set A+=array{Dummy}\n    if(G:=A[0])then G()else 0"),
  ("local: swap through a temporary", fn "    var A:%=F\n    var B:%=Dummy\n    Tmp:=A\n    set A=B\n    set B=Tmp\n    A()"),
  ("local: tuple component", fn "    var T:tuple(%,%)=(F,F)\n    set T=(F,Dummy)\n    T(1)()"),
  ("local: option payload", fn "    var O:?%=false\n    set O=option{Dummy}\n    if(G:=O?)then G()else 0"),
  ("local: struct field", fn "    var B:fbox=fbox{Value:=F}\n    set B.Value=Dummy\n    B.Value()" fbox),
  ("local: struct copy keeps the dummy", fn "    var B:fbox=fbox{Value:=Dummy}\n    C:=B\n    set B.Value=F\n    C.Value()" fbox),
  ("local: array of options", fn "    var A:[]?%=array{option{F}}\n    if(set A[0]=option{Dummy}){}\n    if(O:=A[0],G:=O?)then G()else 0"),
  ("local: map of arrays", fn "    var M:[int][]%=map{0=>array{F}}\n    if(set M[0][0]=Dummy){}\n    if(G:=M[0][0])then G()else 0"),
  ("local: concatenated arrays", fn "    var A:[]%=array{F}\n    set A=A+array{Dummy}\n    if(G:=A[1])then G()else 0"),
  ("local: committed condition write", fn "    var Stored:%=F\n    if(set Stored=Dummy;1=1){}\n    Stored()"),
  -- loops and their cells
  ("loop: for body write", fn "    var Stored:%=F\n    Values:=for(I:=1..2):\n        set Stored=Dummy\n        I\n    Stored()"),
  ("loop: for clause write", fn "    var Stored:%=F\n    Values:=for(I:=1..2,W:=block{set Stored=Dummy;1}){I}\n    Stored()"),
  ("loop: choice producer body write", fn "    var Stored:%=F\n    Values:=for(I:=(1|2)):\n        set Stored=Dummy\n        I\n    Stored()"),
  ("loop: array cursor", fn "    Values:=for(G:array{F,Dummy}){G()}\n    Values.Length"),
  ("loop: map cursor", fn "    Values:=for(K->G:map{0=>Dummy}){G()}\n    Values.Length"),
  ("loop: choice of function values", fn "    Values:=for(G:=(F|Dummy)){G()}\n    Values.Length"),
  ("loop: first of function values", fn "    if(V:=first{G:=(Dummy|F);G()})then V else 0"),
  ("loop: break leaves the write", fn "    var Stored:%=F\n    loop:\n        for(I:=1..2):\n            set Stored=Dummy\n            break\n        break\n    Stored()"),
  -- object fields and aliases
  ("field: method writes its own field", fn "    C:=fcell{Value:=F}\n    C.Put(Dummy)\n    C.Run()" fcell),
  ("field: method write read directly", fn "    C:=fcell{Value:=F}\n    C.Put(Dummy)\n    C.Value()" fcell),
  ("field: written through an interface view", fn "    C:=fcell{Value:=F}\n    S:sink=C\n    S.Put(Dummy)\n    C.Value()" sink),
  ("field: two-level alias", fn "    C:=fcell{Value:=F}\n    O:=outer{Inner:=C}\n    set O.Inner.Value=Dummy\n    C.Value()" (fcell ++ "outer:=class{Inner:fcell}\n")),
  ("field: alias returned by a helper", fn "    C:=fcell{Value:=F}\n    A:=Same(C)\n    set A.Value=Dummy\n    C.Value()" (fcell ++ "Same(C:fcell)<computes>:fcell=C\n")),
  ("field: alias in an option", fn "    C:=fcell{Value:=F}\n    O:?fcell=option{C}\n    if(A:=O?)then set A.Value=Dummy\n    C.Value()" fcell),
  ("field: alias in a map", fn "    C:=fcell{Value:=F}\n    M:[int]fcell=map{0=>C}\n    if(A:=M[0])then set A.Value=Dummy\n    C.Value()" fcell),
  ("field: alias in a tuple", fn "    C:=fcell{Value:=F}\n    T:=(C,1)\n    set T(0).Value=Dummy\n    C.Value()" fcell),
  ("field: alias written in a loop", fn "    C:=fcell{Value:=F}\n    for(A:array{C}){set A.Value=Dummy}\n    C.Value()" fcell),
  ("field: alias through a var local", fn "    C:=fcell{Value:=F}\n    var A:fcell=fcell{Value:=F}\n    set A=C\n    set A.Value=Dummy\n    C.Value()" fcell),
  ("field: alias through a mutable link", fn "    C:=fcell{Value:=F}\n    L:=link{Target:=fcell{Value:=F}}\n    set L.Target=C\n    set L.Target.Value=Dummy\n    C.Value()" (fcell ++ "link:=class{var Target:fcell}\n")),
  ("field: alias through a struct copy", fn "    C:=fcell{Value:=F}\n    var H:holder=holder{Cell:=C}\n    Copy:=H\n    set Copy.Cell.Value=Dummy\n    H.Cell.Value()" (fcell ++ "holder:=struct{Cell:fcell}\n")),
  ("field: helper writes a nested alias", fn "    C:=fcell{Value:=F}\n    StoreIn(outer{Inner:=C},Dummy)\n    C.Value()" (fcell ++ "outer:=class{Inner:fcell}\nStoreIn(O:outer,V:%)<transacts>:void=set O.Inner.Value=V\n")),
  ("field: generic cell instance", fn "    C:=cell(%){Value:=F}\n    set C.Value=Dummy\n    C.Value()" "cell(v:type):=class{var Value:v}\n"),
  -- suspension
  ("wait: field written before, read after", fn "    C:=fcell{Value:=F}\n    set C.Value=Dummy\n    Sleep(0.01)\n    C.Value()" fcell "<suspends>"),
  ("wait: array written before, read after", fn "    var A:[]%=array{F}\n    if(set A[0]=Dummy){}\n    Sleep(0.01)\n    if(G:=A[0])then G()else 0" "" "<suspends>"),
  ("wait: option written before, read after", fn "    var O:?%=option{F}\n    set O=option{Dummy}\n    Sleep(0.01)\n    if(G:=O?)then G()else 0" "" "<suspends>"),
  -- concurrent arms
  ("sync: arms share an object field", fn "    C:=fcell{Value:=F}\n    Values:=sync:\n        block:\n            Sleep(0.2)\n            C.Value()\n        block:\n            Sleep(0.1)\n            set C.Value=Dummy\n            0\n    Values(0)" fcell "<suspends>"),
  ("race: an arm writes an array read afterwards", fn "    var A:[]%=array{F}\n    Winner:=race:\n        block:\n            if(set A[0]=Dummy){}\n            Sleep(0.1)\n            1\n        block:\n            Sleep(1.0)\n            2\n    if(G:=A[0])then G()else 0" "" "<suspends>"),
  ("sync: arms share an option", fn "    var O:?%=option{F}\n    Values:=sync:\n        block:\n            Sleep(0.2)\n            if(G:=O?)then G()else 0\n        block:\n            Sleep(0.1)\n            set O=option{Dummy}\n            0\n    Values(0)" "" "<suspends>"),
  ("spawn: task reads the field its starter wrote", fn "    C:=fcell{Value:=F}\n    set C.Value=Dummy\n    T:=spawn{Work(C)}\n    T.Await()" (fcell ++ "Work(C:fcell)<suspends>:int=\n    Sleep(0.01)\n    C.Value()\n") "<suspends>"),
  -- cleanup
  ("defer: reads the local at exit", fn "    var Stored:%=F\n    defer:\n        Value:=Stored()\n    set Stored=Dummy\n    0"),
  ("defer: reads the field at exit", fn "    C:=fcell{Value:=F}\n    defer:\n        Value:=C.Value()\n    set C.Value=Dummy\n    0" fcell),
  ("defer: captured immutable copy", fn "    Saved:=Dummy\n    defer:\n        Value:=Saved()\n    0"),
  -- arguments and constructors
  ("default: later parameter defaults to the dummy", fn "    Helper(Dummy)" "Helper(A:%,?B:%=A)<computes>:int=B()\n"),
  ("construct: temporary's field", fn "    fbox{Value:=Dummy}.Value()" fbox),
  ("construct: archetype field written first", fn "    fpair{B:=Dummy,A:=F}.B()" "fpair:=class{A:%;B:%}\n"),
  -- function-value conversions
  ("adapter: converted by class variance", variance "    G:type{_(:narrow)<computes>:wide}=Dummy\n    G(narrow{}).N"),
  ("adapter: stored after conversion", variance "    var G:type{_(:narrow)<computes>:wide}=F\n    set G=Dummy\n    G(narrow{}).N"),
  ("adapter: converted in an array", variance "    A:[]type{_(:narrow)<computes>:wide}=array{Dummy}\n    if(G:=A[0])then G(narrow{}).N else 0"),
  ("adapter: converted at a call", variance "    Use(Dummy)" |>.replace "Caller(" "Use(G:type{_(:narrow)<computes>:wide})<computes>:int=G(narrow{}).N\nCaller("),
  -- interpolation
  ("text: interpolated call", fn "    S:=\"{Dummy()}\"\n    S.Length"),
  ("text: write then read in one text", fn "    var Stored:%=F\n    S:=\"{block{set Stored=Dummy;1}}{Stored()}\"\n    S.Length"),
  -- refinement and instantiation
  ("refine: stored object cast", obj "    var S:base=R\n    set S=Dummy\n    if(D:=derived[S])then D.More()else 0"),
  ("refine: array element cast", obj "    var A:[]base=array{R}\n    if(set A[0]=Dummy){}\n    if(B:=A[0],D:=derived[B])then D.More()else 0"),
  ("generic: swapped pair", fn "    Swap(Dummy,F)(1)()" "Swap(A:t,B:u where t:type,u:type)<computes>:tuple(u,t)=(B,A)\n"),
  ("generic: wrapped in an array", fn "    if(G:=Wrap(Dummy)[0])then G()else 0" "Wrap(V:v where v:type)<computes>:[]v=array{V}\n"),
  ("generic: helper's own local", fn "    Hold(Dummy,F)()" "Hold(A:v,B:v where v:type)<transacts>:v=\n    var S:v=B\n    set S=A\n    S\n"),
  -- the original report's conversion through each storage
  ("proof: option payload", proof "    var O:?u=option{D}\n    set O=option{Dummy}\n    if(V:=O?)then P.Up(V).Up(X).N else 0"),
  ("proof: tuple component", proof "    var T:tuple(u,int)=(D,0)\n    set T=(Dummy,1)\n    P.Up(T(0)).Up(X).N"),
  ("proof: struct field", proof "    var B:sbox(u)=sbox(u){Value:=D}\n    set B.Value=Dummy\n    P.Up(B.Value).Up(X).N" "sbox(v:type):=struct<computes>{Value:v}\n"),
  ("proof: swap through a temporary", proof "    var A:u=D\n    var B:u=Dummy\n    T:=A\n    set A=B\n    set B=T\n    P.Up(A).Up(X).N"),
  ("proof: array cursor", proof "    Values:=for(V:array{D,Dummy}){P.Up(V).Up(X).N}\n    Values.Length"),
  ("proof: defer reads the local at exit", proof "    var Stored:u=D\n    defer:\n        Value:=P.Up(Stored).Up(X).N\n    set Stored=Dummy\n    0"),
  ("proof: for body write", proof "    var Stored:u=D\n    Values:=for(I:=1..2):\n        set Stored=Dummy\n        I\n    P.Up(Stored).Up(X).N"),
  ("proof: default argument", proof "    Use(X,Dummy,P)" "Use(X:t,A:u,P:evidence(evidence(vehicle,t),u),?B:u=A where t:type,u:type)<computes>:int=P.Up(B).Up(X).N\n"),
  ("proof: field written before a wait", proof "    C:=cell(u){Value:=D}\n    set C.Value=Dummy\n    Sleep(0.01)\n    P.Up(C.Value).Up(X).N" "cell(v:type):=class{var Value:v}\n" "<suspends>"),
  ("subscribe: handler called by Signal", handler "    E:=subscribable_event(int){}\n    C:=E.Subscribe(Dummy)\n    E.Signal(1)\n    0"),
  ("subscribe: handler stored first", handler "    var Stored:type{_(:int):void}=F\n    set Stored=Dummy\n    E:=subscribable_event(int){}\n    C:=E.Subscribe(Stored)\n    E.Signal(1)\n    0"),
  ("subscribe: event passed to a signalling helper", handler "    E:=subscribable_event(int){}\n    C:=E.Subscribe(Dummy)\n    Fire(E)\n    0" |>.replace "Caller(" "Fire(E:subscribable_event(int)):void=E.Signal(1)\nCaller("),
  ("define: chained definition", fn "    A:=B:=Dummy\n    A()"),
  ("defer: spawns a reader of the local", fn "    var Stored:%=F\n    defer:\n        spawn{Work(Stored)}\n    set Stored=Dummy\n    0" "Work(G:%)<suspends>:int=G()\n" ""),
  ("construct: constructor function", fn "    MakeCell(Dummy).Value()" (fcell ++ "MakeCell<constructor>(V:%)<transacts>:=fcell:\n    Value:=V\n")),
  ("construct: class block writes the field", fn "    late{Init:=Dummy}.Value()" "late:=class:\n    Init:%\n    var Value:%=One\n    block:set Value=Init\n"),
  -- the analysis' own simplifications: a condition that only seems to fail
  ("rollback: executes inside the failing condition", fn "    var Stored:%=F\n    if(set Stored=Dummy;V:=Stored();false?){}\n    0"),
  ("rollback: copied true commits", fn "    var Stored:%=F\n    if(set Stored=Dummy;X:=true;X?){}\n    Stored()"),
  ("rollback: failing literal overwritten", fn "    var Stored:%=F\n    if(set Stored=Dummy;var X:logic=false;set X=true;X?){}\n    Stored()"),
  ("rollback: option literal commits", fn "    var Stored:%=F\n    if(set Stored=Dummy;X:=option{1};Y:=X?){}\n    Stored()"),
  ("rollback: parameter decides", fn "    var Stored:%=F\n    if(set Stored=Dummy;Flag?){}\n    Stored()" |>.replace "Caller(F:%," "Caller(Flag:logic,F:%,"),
  ("rollback: negated failure commits", fn "    var Stored:%=F\n    if(set Stored=Dummy;not false?){}\n    Stored()"),
  ("rollback: failure in an or commits", fn "    var Stored:%=F\n    if(set Stored=Dummy;false? or 1=1){}\n    Stored()"),
  ("rollback: nested failing inside committed", fn "    var Stored:%=F\n    if(set Stored=Dummy;if(set Stored=F;false?){};1=1){}\n    Stored()"),
  ("rollback: array write then succeeding index", fn "    var A:[]%=array{F,F}\n    if(set A[0]=Dummy;set A[1]=F){}\n    if(G:=A[0])then G()else 0"),
  ("rollback: helper succeeds after its caller's write", fn "    var Stored:%=F\n    if(set Stored=Dummy;Always[]){}\n    Stored()" "Always()<transacts><decides>:void=1=1\n"),
  ("rollback: for filter passes one row", fn "    var Stored:%=F\n    Rows:=for(I:=1..2,block{set Stored=Dummy;I}>1){I}\n    Stored()"),
  ("rollback: first's kept alternative", fn "    var Stored:%=F\n    if(V:=first{I:=(1|2);set Stored=Dummy;I>1;I}){}\n    Stored()"),
  -- write-only destinations: a read the frame's own body does not make
  ("private: read only by a defer", fn "    var Stored:%=F\n    defer:\n        Value:=Stored()\n    Sleep(0.01)\n    set Stored=Dummy\n    Sleep(0.01)\n    0" "" "<suspends>"),
  ("private: read only by a later loop row", fn "    var Stored:%=F\n    var N:int=0\n    loop:\n        if(N>0)then Value:=Stored()\n        set Stored=Dummy\n        Sleep(0.01)\n        set N+=1\n        if(N>=2)then break\n    0" "" "<suspends>"),
  ("private: read only by a waiting branch", fn "    var Stored:%=F\n    branch:\n        Sleep(0.1)\n        Value:=Stored()\n    set Stored=Dummy\n    Sleep(1.0)\n    0" "" "<suspends>"),
  ("private: read only in an interpolation", fn "    var Stored:%=F\n    set Stored=Dummy\n    Sleep(0.01)\n    Print(\"{Stored()}\")\n    0" "" "<suspends>"),
  ("private: read only as a default argument", fn "    var Stored:%=F\n    set Stored=Dummy\n    Sleep(0.01)\n    Helper(Stored)" "Helper(A:%,?B:%=A)<computes>:int=B()\n" "<suspends>"),
  ("private: read only by a compound append", fn "    var A:[]%=array{F}\n    set A=array{Dummy}\n    Sleep(0.01)\n    set A+=array{F}\n    if(G:=A[0])then G()else 0" "" "<suspends>"),
  -- one allocation site, several objects
  ("site: factory's second object", fn "    A:=Make(F)\n    B:=Make(Dummy)\n    B.Value()" (fcell ++ "Make(V:%)<transacts>:fcell=fcell{Value:=V}\n")),
  ("site: loop's objects", fn "    Cells:=for(G:array{F,Dummy}){fcell{Value:=G}}\n    if(C:=Cells[1])then C.Value()else 0" fcell),
  ("site: var chooses between two objects", fn "    C:=fcell{Value:=F}\n    Other:=fcell{Value:=Dummy}\n    var P:fcell=C\n    if(Flag?)then set P=Other\n    P.Value()" fcell |>.replace "Caller(F:%," "Caller(Flag:logic,F:%,"),
  ("site: helper chooses between two objects", fn "    C:=fcell{Value:=F}\n    Other:=fcell{Value:=Dummy}\n    Choose(C,Other,true).Value()" (fcell ++ "Choose(A:fcell,B:fcell,C:logic)<computes>:fcell=if(C?)then B else A\n")),
  ("site: virtual method chooses between two objects", fn "    C:=fcell{Value:=F}\n    Other:=fcell{Value:=Dummy}\n    S:chooser=second{}\n    S.Choose(C,Other).Value()" (fcell ++ "chooser:=interface:\n    Choose(A:fcell,B:fcell)<computes>:fcell\nsecond:=class(chooser):\n    Choose<override>(A:fcell,B:fcell)<computes>:fcell=B\n")),
  ("site: object read from an array of both", fn "    C:=fcell{Value:=F}\n    Other:=fcell{Value:=Dummy}\n    Cs:=array{C,Other}\n    if(X:=Cs[1])then X.Value()else 0" fcell),
  ("site: carrier's own method", fn "    Other:=fcell{Value:=Dummy}\n    Other.Run()" fcell),
  ("site: carrier's bound method", fn "    Other:=fcell{Value:=Dummy}\n    M:=Other.Run\n    M()" fcell),
  ("site: carrier behind an interface", fn "    X:goer=runner{G:=Dummy}\n    X.Go()" "goer:=interface:\n    Go()<computes>:int\nrunner:=class(goer):\n    G:%\n    Go<override>()<computes>:int=\n        H:=G\n        H()\n"),
  ("site: carrier passed to a helper", fn "    RunCell(fcell{Value:=Dummy})" (fcell ++ "RunCell(C:fcell)<transacts>:int=C.Value()\n")),
  ("site: carrier swapped into a real object's link", fn "    L:=link{Target:=fcell{Value:=F}}\n    Keep:=L.Target\n    set L.Target=fcell{Value:=Dummy}\n    L.Target.Value()" (fcell ++ "link:=class{var Target:fcell}\n")),
  -- dispatch
  ("call: virtual method executes its argument", fn "    S:user=runs{}\n    S.Use(Dummy)" "user:=interface:\n    Use(G:%)<computes>:int\nruns:=class(user):\n    Use<override>(G:%)<computes>:int=G()\nskips:=class(user):\n    Use<override>(G:%)<computes>:int=0\n"),
  ("call: passed to a function value", fn "    Apply(Dummy)" "Call(G:%)<computes>:int=G()\nSkip(G:%)<computes>:int=0\nSel(C:logic)<computes>:type{_(:%)<computes>:int}=if(C?)then Call else Skip\n" |>.replace "Caller(F:%," "Caller(Apply:type{_(:%)<computes>:int},F:%,"),
  ("call: passed to a local function value", fn "    A:=Call\n    A(Dummy)" "Call(G:%)<computes>:int=G()\n"),
  ("call: passed to a chosen function value", fn "    Sel(true)(Dummy)" "Call(G:%)<computes>:int=G()\nSkip(G:%)<computes>:int=0\nSel(C:logic)<computes>:type{_(:%)<computes>:int}=if(C?)then Call else Skip\n"),
  ("call: passed to a bound method value", fn "    M:=runs{}.Use\n    M(Dummy)" "runs:=class:\n    Use(G:%)<computes>:int=G()\n"),
  ("call: passed to a stored function value", fn "    var A:type{_(:%)<computes>:int}=Skip\n    set A=Call\n    A(Dummy)" "Call(G:%)<computes>:int=G()\nSkip(G:%)<computes>:int=0\n"),
  ("call: passed to a function value in a field", fn "    H:=applier{A:=Call}\n    H.A(Dummy)" "Call(G:%)<computes>:int=G()\napplier:=class{A:type{_(:%)<computes>:int}}\n"),
  ("call: object passed to a function value", obj "    Apply(Dummy)" "Call(B:base)<computes>:int=B.Read()\nSkip(B:base)<computes>:int=0\nSel(C:logic)<computes>:type{_(:base)<computes>:int}=if(C?)then Call else Skip\n" |>.replace "Caller(R:base," "Caller(Apply:type{_(:base)<computes>:int},R:base,"),
  ("call: proof passed to a function value", proof "    Apply(Dummy,X)" "Call(V:evidence(vehicle,vehicle),X:vehicle)<computes>:int=V.Up(X).N\nSkip(V:evidence(vehicle,vehicle),X:vehicle)<computes>:int=0\nSel(C:logic)<computes>:type{_(:evidence(vehicle,vehicle),:vehicle)<computes>:int}=if(C?)then Call else Skip\n" |>.replace "Caller(X:t,D:u,Dummy:u,P:evidence(evidence(vehicle,t),u) where t:type,u:type)" "Caller(Apply:type{_(:evidence(vehicle,vehicle),:vehicle)<computes>:int},X:vehicle,Dummy:evidence(vehicle,vehicle))"),
  ("call: recursion swaps its arguments", fn "    Rec(F,Dummy,2)" "Rec(G:%,H:%,N:int)<computes>:int=if(N>0)then G()+Rec(H,G,N-1)else 0\n"),
  ("call: option default", fn "    O:?%=false\n    G:=O? or Dummy\n    G()"),
  ("call: stored constructor result", fn "    var Stored:fcell=fcell{Value:=F}\n    set Stored=MakeCell(Dummy)\n    Stored.Value()" (fcell ++ "MakeCell<constructor>(V:%)<transacts>:=fcell:\n    Value:=V\n")),
  -- recent features
  ("random: index chooses among both", fn "    Items:[]%=array{F,Dummy}\n    if(G:=Items[GetRandomInt(0,1)])then G()else 0"),
  ("random: dummy elements", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Dummy:[]reader,Real:reader)<transacts>:int=\n    if(Alias:=Dummy[GetRandomInt(0,1)])then Alias.Read()else 0\n"),
  ("module: constant compared with the dummy", "u:=class<unique><allocates><computes>{Read()<computes>:int=1}\nInstance:u=u{}\nCaller(Dummy:u)<transacts>:int=\n    if(Alias:=Dummy=Instance)then Alias.Read()else 0\n"),
  ("module: constant keys a weak map read elsewhere", fn "    if(set Functions[Instance]=Dummy){}\n    Get()" "u:=class<unique><allocates><computes><module_scoped_var_weak_map_key>{}\nInstance:u=u{}\nvar Functions:weak_map(u,%)=map{}\nGet()<transacts>:int=if(G:=Functions[Instance])then G()else 0\n"),
  ("archetype: later field's code reads the earlier write", fn "    var Stored:%=F\n    B:=ipair{Second:=block{set Stored=Dummy;1},First:=Stored()}\n    B.First" "ipair:=class{First:int;Second:int}\n"),
  ("break: for body leaves the outer loop after the write", fn "    var Stored:%=F\n    loop:\n        Rows:=for(I:=1..2):\n            set Stored=Dummy\n            break\n            I\n    Stored()"),
  ("branch: outlives its function and reads the field", fn "    C:=fcell{Value:=F}\n    Start(C)\n    set C.Value=Dummy\n    Sleep(1.0)\n    0" (fcell ++ "Start(C:fcell)<suspends>:void=\n    branch:\n        Sleep(0.1)\n        Value:=C.Value()\n") "<suspends>"),
  -- storage whose type says less than what it holds
  ("type: interface-typed local", obj "    var S:goes=R\n    set S=Dummy\n    S.Go()" |> goes),
  ("type: supertype local cast down", obj "    var S:base=R\n    set S=Dummy\n    if(B:=derived[S])then B.Read()else 0"),
  ("type: tuple used as an array", fn "    A:[]%=(F,Dummy)\n    if(G:=A[1])then G()else 0"),
  ("type: generic parameter at an interface bound", obj "    Go(Dummy)" "Go(V:v where v:subtype(base))<computes>:int=V.Read()\n"),
  ("type: generic local at an interface bound", obj "    Go(R,Dummy)" "Go(A:v,B:v where v:subtype(base))<transacts>:int=\n    var S:v=A\n    set S=B\n    S.Read()\n"),
  ("type: option of an interface in a map", obj "    var M:[int]?goes=map{0=>option{R}}\n    if(set M[0]=option{Dummy}){}\n    if(O:=M[0],V:=O?)then V.Go()else 0" |> goes),
  -- tuple columns
  ("tuple: columns swapped in place", fn "    var T:tuple(%,%)=(F,Dummy)\n    set T=(T(1),T(0))\n    T(0)()"),
  ("tuple: branches disagree on the column", fn "    T:=if(Flag?)then (F,Dummy) else (Dummy,F)\n    T(0)()" |>.replace "Caller(F:%," "Caller(Flag:logic,F:%,"),
  ("tuple: recursion swaps columns", fn "    Rec(F,Dummy,1)(0)()" "Rec(A:%,B:%,N:int)<computes>:tuple(%,%)=if(N>0)then Rec(B,A,N-1)else (A,B)\n"),
  ("tuple: spread into arguments", fn "    T:=(F,Dummy)\n    Second(T)" "Second(G:%,H:%)<computes>:int=H()\n"),
  ("tuple: element of an array of tuples", fn "    var A:[]tuple(%,%)=array{(F,F)}\n    if(set A[0]=(F,Dummy)){}\n    if(T:=A[0])then T(1)()else 0"),
  ("tuple: nested column", fn "    var T:tuple(int,tuple(%,%))=(0,(F,F))\n    set T=(1,(F,Dummy))\n    T(1)(1)()"),
  ("tuple: column across a wait", fn "    var T:tuple(%,%)=(F,F)\n    set T=(F,Dummy)\n    Sleep(0.01)\n    T(1)()" "" "<suspends>"),
  ("tuple: column through an option", fn "    var O:?tuple(%,%)=false\n    set O=option{(Dummy,F)}\n    if(T:=O?)then T(0)()else 0"),
  ("tuple: column of a helper's result in a field", fn "    C:=tcell{Value:=(F,F)}\n    set C.Value=Pair(F,Dummy)\n    C.Value(1)()" "tcell:=class{var Value:tuple(%,%)}\nPair(A:%,B:%)<computes>:tuple(%,%)=(A,B)\n"),
  ("accessor: setter stores what the getter reads", fn "    C:=acell{Value:=F}\n    set C.Value=Dummy\n    G:=C.Value\n    G()" accessors),
  ("accessor: constructed through the setter", fn "    C:=acell{Value:=Dummy}\n    G:=C.Value\n    G()" accessors),
  ("proof: text interpolation", proof "    var Stored:u=D\n    S:=\"{block{set Stored=Dummy;1}}{P.Up(Stored).Up(X).N}\"\n    S.Length")]

/-- Nothing executes the dummy, and the marked program is admitted. -/
private def forwards : List (String × String) := [
  -- reading a data field executes nothing
  ("object: data field of a stored dummy", "item:=class<computes>{N:int=1}\nCaller(R:item,Dummy:item)<transacts>:int=\n    var S:item=R\n    set S=Dummy\n    S.N"),
  -- a zero Sleep waits a tick (#724); a negative one does not wait
  ("sleep: zero wait lets the owner overwrite before a branch reads", fn "    var Stored:%=Dummy\n    branch:\n        Sleep(0.0)\n        Value:=Stored()\n    set Stored=F\n    Sleep(0.1)\n    0" "" "<suspends>"),
  ("sleep: an arm that does not wait completes its rush before a late return", fn "    Saved:=Later(Dummy,F)\n    Saved()" ("Later(V:v,R:v where v:type)<suspends>:v=\n    Release:=event(int){}\n    Value:=rush:\n        block:\n            Release.Await()\n            return V\n        block:\n            ARM\n            R\n    Release.Signal(0)\n    R\n".replace "ARM" "NoWait()" ++ "NoWait()<suspends>:void={}\n") "<suspends>"),
  -- plain locals
  ("local: swap through a temporary, real side", fn "    var A:%=F\n    var B:%=Dummy\n    Tmp:=A\n    set A=B\n    set B=Tmp\n    B()"),
  ("local: tuple real component", fn "    var T:tuple(%,%)=(F,F)\n    set T=(F,Dummy)\n    T(0)()"),
  ("local: option payload overwritten", fn "    var O:?%=false\n    set O=option{Dummy}\n    set O=option{F}\n    if(G:=O?)then G()else 0"),
  ("local: struct field overwritten", fn "    var B:fbox=fbox{Value:=Dummy}\n    set B.Value=F\n    B.Value()" fbox),
  ("local: struct copy precedes the dummy write", fn "    var B:fbox=fbox{Value:=F}\n    C:=B\n    set B.Value=Dummy\n    C.Value()" fbox),
  ("local: map entry rolled back", fn "    var M:[int]%=map{0=>F}\n    if(set M[0]=Dummy;false?){}\n    if(G:=M[0])then G()else 0"),
  ("local: array element overwritten", fn "    var A:[]%=array{Dummy}\n    set A=array{F}\n    if(G:=A[0])then G()else 0"),
  -- loops and their cells
  ("loop: failed iterations roll their write back", fn "    var Stored:%=F\n    Values:=for(I:=1..2,W:=block{set Stored=Dummy;1},false?){I}\n    Stored()"),
  ("loop: real write in the body", fn "    var Stored:%=Dummy\n    Values:=for(I:=1..2):\n        set Stored=F\n        Stored()\n    Values.Length"),
  ("loop: cursor over real elements", fn "    Unused:=array{Dummy}\n    Values:=for(G:array{F}){G()}\n    Values.Length"),
  -- object fields and aliases
  ("field: a separate object stays real", fn "    C:=fcell{Value:=F}\n    Other:=fcell{Value:=Dummy}\n    C.Value()" fcell),
  -- suspension
  ("wait: array overwritten after", fn "    var A:[]%=array{Dummy}\n    Sleep(0.01)\n    set A=array{F}\n    if(G:=A[0])then G()else 0" "" "<suspends>"),
  ("wait: struct field overwritten before", fn "    var B:fbox=fbox{Value:=Dummy}\n    set B.Value=F\n    Sleep(0.01)\n    B.Value()" fbox "<suspends>"),
  -- cleanup
  ("defer: reads the real overwrite at exit", fn "    var Stored:%=Dummy\n    defer:\n        Value:=Stored()\n    set Stored=F\n    0"),
  ("defer: writes the dummy nothing reads", fn "    var Stored:%=F\n    defer:\n        set Stored=Dummy\n    Stored()"),
  -- function-value conversions
  ("adapter: overwritten after conversion", variance "    var G:type{_(:narrow)<computes>:wide}=Dummy\n    set G=F\n    G(narrow{}).N"),
  -- interpolation
  ("text: read then write in one text", fn "    var Stored:%=F\n    S:=\"{Stored()}{block{set Stored=Dummy;1}}\"\n    S.Length"),
  -- refinement and instantiation
  ("refine: stored object cast after overwrite", obj "    var S:base=Dummy\n    set S=R\n    if(D:=derived[S])then D.More()else 0"),
  ("generic: swapped pair, real side", fn "    Swap(Dummy,F)(0)()" "Swap(A:t,B:u where t:type,u:type)<computes>:tuple(u,t)=(B,A)\n"),
  ("generic: helper's local overwritten", fn "    Hold(Dummy,F)()" "Hold(A:v,B:v where v:type)<transacts>:v=\n    var S:v=A\n    set S=B\n    S\n"),
  -- the original report's conversion through each storage
  ("proof: swap through a temporary, real side", proof "    var A:u=D\n    var B:u=Dummy\n    T:=A\n    set A=B\n    set B=T\n    P.Up(B).Up(X).N"),
  ("subscribe: real handler after overwrite", handler "    var Stored:type{_(:int):void}=Dummy\n    set Stored=F\n    E:=subscribable_event(int){}\n    C:=E.Subscribe(Stored)\n    E.Signal(1)\n    0"),
  -- the analysis' own simplifications: a condition that only seems to fail
  ("rollback: saved copy inside the condition is discarded", fn "    var Stored:%=F\n    var Saved:%=F\n    if(set Stored=Dummy;set Saved=Stored;false?){}\n    Saved()"),
  ("rollback: else arm reads after the failed write", fn "    var Stored:%=F\n    if(set Stored=Dummy;false?)then 0 else Stored()"),
  ("rollback: nested committed inside failing", fn "    var Stored:%=F\n    if(if(set Stored=Dummy;1=1){};false?){}\n    Stored()"),
  ("rollback: helper fails after its caller's write", fn "    var Stored:%=F\n    if(set Stored=Dummy;Never[]){}\n    Stored()" "Never()<transacts><decides>:void=false?\n"),
  -- write-only destinations: a read the frame's own body does not make
  ("private: never read", fn "    var Stored:%=F\n    set Stored=Dummy\n    Sleep(0.01)\n    set Stored=Dummy\n    0" "" "<suspends>"),
  -- one allocation site, several objects
  ("site: carrier returned unread", fn "    fcell{Value:=Dummy}" fcell (result := "fcell")),
  -- recent features
  ("random: dummy bound, real elements", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Items:[]reader,Dummy:int)<transacts>:int=\n    if(Alias:=Items[GetRandomInt(0,Dummy)])then Alias.Read()else 0\n"),
  ("module: constant is the value compared", "u:=class<unique><allocates><computes>{Read()<computes>:int=1}\nInstance:u=u{}\nCaller(Dummy:u)<transacts>:int=\n    if(Alias:=Instance=Dummy)then Alias.Read()else 0\n"),
  ("module: constant keys a weak map, real value", fn "    Unused:=Dummy\n    if(set Functions[Instance]=F){}\n    Get()" "u:=class<unique><allocates><computes><module_scoped_var_weak_map_key>{}\nInstance:u=u{}\nvar Functions:weak_map(u,%)=map{}\nGet()<transacts>:int=if(G:=Functions[Instance])then G()else 0\n"),
  ("archetype: earlier field's code precedes the write", fn "    var Stored:%=F\n    B:=ipair{First:=Stored(),Second:=block{set Stored=Dummy;1}}\n    B.First" "ipair:=class{First:int;Second:int}\n"),
  ("break: write after the break is never made", fn "    var Stored:%=F\n    loop:\n        Rows:=for(I:=1..2):\n            break\n            set Stored=Dummy\n            I\n    Stored()"),
  -- storage whose type says less than what it holds
  ("type: interface-typed local overwritten", obj "    var S:goes=Dummy\n    set S=R\n    S.Go()" |> goes),
  -- tuple columns
  ("tuple: columns swapped in place, real column", fn "    var T:tuple(%,%)=(F,Dummy)\n    set T=(T(1),T(0))\n    T(1)()"),
  ("tuple: nested real column", fn "    var T:tuple(int,tuple(%,%))=(0,(F,F))\n    set T=(1,(F,Dummy))\n    T(1)(0)()")]

/-- Nothing executes the dummy, yet the marked program is refused today: the
    precision the audit found missing, kept so that a change is noticed. -/
private def conservative : List (String × String) := [
  ("object: data field of a stored dummy after a wait", "item:=class<computes>{N:int=1}\nCaller(R:item,Dummy:item)<suspends>:int=\n    var S:item=R\n    set S=Dummy\n    Sleep(0.01)\n    S.N"),
  ("sleep: a negative duration does not wait", fn "    var Stored:%=F\n    Values:=sync:\n        block:\n            Sleep(-1.0)\n            Stored()\n        block:\n            NoWait()\n            set Stored=Dummy\n            0\n    Values(0)" "NoWait()<suspends>:void={}\n" "<suspends>"),
  ("sleep: a rush arm that waits a tick still precedes a late return", fn "    Saved:=Later(Dummy,F)\n    Saved()" ("Later(V:v,R:v where v:type)<suspends>:v=\n    Release:=event(int){}\n    Value:=rush:\n        block:\n            Release.Await()\n            return V\n        block:\n            ARM\n            R\n    Release.Signal(0)\n    R\n".replace "ARM" "Sleep(0.0)") "<suspends>"),
  -- object fields and aliases
  ("field: interface view of another object", fn "    C:=fcell{Value:=F}\n    Other:=fcell{Value:=F}\n    S:sink=Other\n    S.Put(Dummy)\n    C.Value()" sink),
  ("field: real overwrite", fn "    C:=fcell{Value:=Dummy}\n    set C.Value=F\n    C.Value()" fcell),
  ("field: rolled-back write", fn "    C:=fcell{Value:=F}\n    if(set C.Value=Dummy;false?){}\n    C.Value()" fcell),
  ("field: opaque forwarding", fn "    C:=fcell{Value:=F}\n    set C.Value=Dummy\n    C.Value" fcell (result := "%")),
  -- arguments and constructors
  ("default: default overridden by a real value", fn "    Helper(Dummy,?B:=F)" "Helper(A:%,?B:%=A)<computes>:int=B()\n"),
  ("construct: archetype's other field", fn "    fpair{B:=Dummy,A:=F}.A()" "fpair:=class{A:%;B:%}\n"),
  -- the analysis' own simplifications: a condition that only seems to fail
  ("rollback: copied false fails", fn "    var Stored:%=F\n    if(set Stored=Dummy;X:=false;X?){}\n    Stored()"),
  ("rollback: array write then failing index", fn "    var A:[]%=array{F}\n    if(set A[0]=Dummy;set A[5]=F){}\n    if(G:=A[0])then G()else 0"),
  ("rollback: for filter fails every row", fn "    var Stored:%=F\n    Rows:=for(I:=1..2,block{set Stored=Dummy;I}>5){I}\n    Stored()"),
  ("rollback: first's failed alternatives", fn "    var Stored:%=F\n    if(V:=first{I:=(1|2);set Stored=Dummy;I>5;I}){}\n    Stored()"),
  -- one allocation site, several objects
  ("site: factory's first object", fn "    A:=Make(F)\n    B:=Make(Dummy)\n    A.Value()" (fcell ++ "Make(V:%)<transacts>:fcell=fcell{Value:=V}\n")),
  ("site: saved real object after the link changes", fn "    L:=link{Target:=fcell{Value:=F}}\n    Keep:=L.Target\n    set L.Target=fcell{Value:=Dummy}\n    Keep.Value()" (fcell ++ "link:=class{var Target:fcell}\n")),
  -- tuple columns
  ("tuple: spread into arguments, real column", fn "    T:=(F,Dummy)\n    First(T)" "First(G:%,H:%)<computes>:int=G()\n"),
  ("tuple: real column across a wait", fn "    var T:tuple(%,%)=(F,F)\n    set T=(F,Dummy)\n    Sleep(0.01)\n    T(0)()" "" "<suspends>")]

private structure Kind where
  name : String
  ty : String
  real : String
  params : String
  prelude : String
  uses : List (String × (String → String))

private def common : String :=
  "sbox(v:type):=struct<computes>{Value:v}\ncell(v:type):=class{var Value:v}\nibox(v:type):=class{Value:v}\n" ++
  "Keep(V:v where v:type)<computes>:v=V\nHold(A:v,B:v where v:type)<transacts>:v=\n    var S:v=B\n    set S=A\n    S\n" ++
  "Store(C:cell(v),V:v where v:type)<transacts>:void=set C.Value=V\n"

private def kinds : List Kind := [
  { name := "function", ty := "%", real := "F", params := "F:%,Dummy:%",
    prelude := callables ++ "Run(G:%)<computes>:int=G()\ncarrier:=class:\n    G:%\n    Call()<computes>:int=\n        H:=G\n        H()\n",
    uses := [("call", fun e => s!"{e}()"), ("helper", fun e => s!"Run({e})"),
      ("carrier", fun e => s!"carrier\{G:={e}}.Call()")] },
  { name := "handler", ty := "type{_(:int):void}", real := "F",
    params := "F:type{_(:int):void},Dummy:type{_(:int):void}",
    prelude := "Log(N:int):void=Print(\"event {N}\")\nTrapLog(N:int):void=Err()\nFire(G:type{_(:int):void}):int=\n    E:=subscribable_event(int){}\n    C:=E.Subscribe(G)\n    E.Signal(1)\n    0\n",
    uses := [("subscribe", fun e => s!"Fire({e})")] },
  { name := "object", ty := "base", real := "R", params := "R:base,Dummy:base",
    prelude := "base:=class<computes>{Read()<computes>:int=1}\nderived:=class<computes>(base){More()<computes>:int=7}\n" ++
      "trap:=class<computes>(derived){Read<override>()<computes>:int=Err();More<override>()<computes>:int=Err()}\n" ++
      "Use(B:base)<computes>:int=B.Read()\n",
    uses := [("method", fun e => s!"{e}.Read()"), ("cast", fun e => s!"(if(Cast:=derived[{e}])then Cast.More()else 0)"),
      ("helper", fun e => s!"Use({e})")] },
  { name := "proof", ty := "u", real := "D",
    params := "X:t,D:u,Dummy:u,P:evidence(evidence(vehicle,t),u) where t:type,u:type",
    prelude := "UseP(X:t,V:u,P:evidence(evidence(vehicle,t),u) where t:type,u:type)<computes>:int=P.Up(V).Up(X).N\n",
    uses := [("up", fun e => s!"P.Up({e}).Up(X).N"), ("helper", fun e => s!"UseP(X,{e},P)")] }]

/-- Each storage holds `init`, has `put` written to it, and hands what it then
    reads to `use`. `wait` is empty, or a suspension between the write and the
    read; a storage that needs one gives none without it. -/
private def storages : List (String × (Kind → (init put wait : String) → (String → String) → Option String)) := [
  ("var", fun k init put wait use => some s!"    var S:{k.ty}={init}\n    set S={put}\n{wait}    {use "S"}"),
  ("swap", fun k init put wait use => some s!"    var S:{k.ty}={init}\n    var B:{k.ty}={put}\n    T:=S\n    set S=B\n    set B=T\n{wait}    {use "S"}"),
  ("array", fun k init put wait use => some s!"    var S:[]{k.ty}=array\{{init}}\n    if(set S[0]={put})\{}\n{wait}    if(V:=S[0])then {use "V"} else 0"),
  ("map", fun k init put wait use => some s!"    var S:[int]{k.ty}=map\{0=>{init}}\n    if(set S[0]={put})\{}\n{wait}    if(V:=S[0])then {use "V"} else 0"),
  ("option", fun k init put wait use => some s!"    var S:?{k.ty}=option\{{init}}\n    set S=option\{{put}}\n{wait}    if(V:=S?)then {use "V"} else 0"),
  ("tuple", fun k init put wait use => some s!"    var S:tuple({k.ty},int)=({init},0)\n    set S=({put},1)\n{wait}    {use "S(0)"}"),
  ("struct", fun k init put wait use => some s!"    var S:sbox({k.ty})=sbox({k.ty})\{Value:={init}}\n    set S.Value={put}\n{wait}    {use "S.Value"}"),
  ("field", fun k init put wait use => some s!"    S:=cell({k.ty})\{Value:={init}}\n    set S.Value={put}\n{wait}    {use "S.Value"}"),
  ("alias", fun k init put wait use => some s!"    S:=cell({k.ty})\{Value:={init}}\n    A:=S\n    set A.Value={put}\n{wait}    {use "S.Value"}"),
  ("helper-field", fun k init put wait use => some s!"    S:=cell({k.ty})\{Value:={init}}\n    Store(S,{put})\n{wait}    {use "S.Value"}"),
  ("helper-local", fun _ init put wait use => some s!"    S:=Hold({put},{init})\n{wait}    {use "S"}"),
  ("loop-cell", fun k init put wait use => some s!"    var S:{k.ty}={init}\n    Rows:=for(I:=(1|2)):\n        set S={put}\n        I\n{wait}    {use "S"}"),
  ("defer", fun k init put wait use => some s!"    var S:{k.ty}={init}\n    defer:\n        Seen:={use "S"}\n    set S={put}\n{wait}    0"),
  ("branch", fun k init put wait use => if wait.isEmpty then none else
    some s!"    var S:{k.ty}={init}\n    branch:\n        Sleep(0.1)\n        Seen:={use "S"}\n    set S={put}\n    Sleep(1.0)\n    0"),
  ("sync", fun k init put wait use => if wait.isEmpty then none else
    some s!"    var S:{k.ty}={init}\n    Rows:=sync:\n        block:\n            Sleep(0.2)\n            {use "S"}\n        block:\n            Sleep(0.1)\n            set S={put}\n            0\n    Rows(0)"),
  ("race", fun k init put wait use => if wait.isEmpty then none else
    some s!"    var S:{k.ty}={init}\n    Won:=race:\n        block:\n            set S={put}\n            Sleep(0.1)\n            1\n        block:\n            Sleep(1.0)\n            2\n    {use "S"}")]

/-- Storages with nothing to overwrite: only the dummy is ever in them. -/
private def carriers : List (String × (Kind → (wait : String) → (String → String) → String)) := [
  ("direct", fun _ wait use => s!"{wait}    {use "Dummy"}"),
  ("frozen-field", fun k wait use => s!"    S:=ibox({k.ty})\{Value:=Dummy}\n{wait}    {use "S.Value"}"),
  ("helper-return", fun _ wait use => s!"    S:=Keep(Dummy)\n{wait}    {use "S"}"),
  ("loop-carried", fun k wait use => s!"    var S:{k.ty}={k.real}\n    Rows:=for(I:=1..2):\n{wait.replace "    " "        "}        Seen:={use "S"}\n        set S=Dummy\n        Seen\n    Rows.Length"),
  ("cursor", fun k wait use => s!"{wait}    Rows:=for(V:array\{{k.real},Dummy})\{{use "V"}}\n    Rows.Length"),
  ("choice", fun k wait use => s!"{wait}    Rows:=for(V:=({k.real}|Dummy))\{{use "V"}}\n    Rows.Length")]

/-- Nothing between the write and the read, a wait, or the shortest wait:
    a zero `Sleep` waits a tick (#724). -/
private def modes : List (String × String × String) :=
  [("plain", "", ""), ("wait", "<suspends>", "    Sleep(0.01)\n"), ("tick", "<suspends>", "    Sleep(0.0)\n")]

/-- These storages wait by themselves, whatever the mode's wait is. -/
private def ownWait (storage mode : String) : Bool :=
  ["branch", "sync", "race"].contains storage && mode == "tick"

private def program (k : Kind) (effect body : String) : String :=
  common ++ k.prelude ++ s!"Caller({k.params}){effect}:int=\n" ++ body

/-- Every kind of value, used every way, out of every storage, in every
    mode: all refused. -/
private def matrix : List (String × String) := Id.run do
  let mut out := []
  for k in kinds do
    for (useName, use) in k.uses do
      for (mode, effect, wait) in modes do
        for (name, store) in storages do
          if ownWait name mode then continue
          if let some body := store k k.real "Dummy" wait use then
            out := (s!"{k.name}/{useName}/{name}/{mode}", program k effect body) :: out
          -- and once for each kind, the dummy as a helper's result
          if some useName == k.uses.head?.map (·.1) then
            if let some body := store k k.real "Keep(Dummy)" wait use then
              out := (s!"{k.name}/{useName}/{name}/{mode}/returned", program k effect body) :: out
        for (name, carry) in carriers do
          out := (s!"{k.name}/{useName}/{name}/{mode}", program k effect (carry k wait use)) :: out
  return out.reverse

/-- Whether the analysis follows a real value written over the dummy in this
    storage. Where it does not, it cannot tell that the write happens (an
    indexed write may fail, a loop may make no pass), or it holds every
    reference to an object's field, and every arm and task, to one answer. -/
private def followsOverwrite (kind use storage mode : String) : Bool :=
  ["var", "option", "tuple", "struct", "helper-local", "defer"].contains storage ||
  (storage == "swap" && mode == "plain") ||
  (storage == "branch" && ["function", "object"].contains kind && ["call", "method"].contains use)

/-- The dummy is in the storage first and a real value is written over it
    before the use: (label, source, admitted). -/
private def overwrites : List (String × String × Bool) := Id.run do
  let mut out := []
  for k in kinds do
    if let some (useName, use) := k.uses.head? then
      for (mode, effect, wait) in modes do
        for (name, store) in storages do
          if ownWait name mode then continue
          if let some body := store k "Dummy" k.real wait use then
            out := (s!"{k.name}/{useName}/{name}/{mode}/overwritten", program k effect body,
              followsOverwrite k.name useName name mode) :: out
  return out.reverse

private inductive Want where
  | refused
  | admitted
  | conservative
deriving BEq

private def Want.text : Want → String
  | .refused => "refusal"
  | .admitted => "forward"
  | .conservative => "conservative"

private def all : List (String × String × Want) :=
  refusals.map (fun (label, source) => (label, source, Want.refused)) ++
  forwards.map (fun (label, source) => (label, source, Want.admitted)) ++
  conservative.map (fun (label, source) => (label, source, Want.conservative)) ++
  matrix.map (fun (label, source) => (label, source, Want.refused)) ++
  overwrites.map (fun (label, source, admitted) =>
    (label, source, if admitted then Want.admitted else Want.conservative))

private def has (text part : String) : Bool := (text.splitOn part).length > 1

/-- A `Main` that calls `Caller` with a real value and, as `Dummy`, a value
    that stops the program with a user error when it is executed. It then
    waits, so that a task `Caller` left running gets to run as well. -/
private def driver (source : String) : Option String :=
  let call (arguments : String) : Option String :=
    some s!"Main()<suspends>:void=\n    Value:=Caller({arguments})\n    Sleep(10.0)\n    Print(\"end\")"
  if has source "Caller(F:%,Dummy:%)" then call "One,Trap"
  else if has source "Caller(F:type{_(:int):void},Dummy:type{_(:int):void})" then call "Log,TrapLog"
  else if has source "Caller(R:base,Dummy:base)" then call "base{},trap{}"
  else if has source "Caller(F:type{_(:wide)<computes>:narrow},Dummy:type{_(:wide)<computes>:narrow})" then
    call "Make,TrapMake"
  else none

private def compileCase (source : String) (dummy : Bool) (main : String := "Main():void={}") :
    Except String Compiled := do
  let tops ← parseProgram ("vehicle:=class<computes>{N:int=7}\n" ++ expand source ++ "\n" ++ main)
  elabProgram (← tops.mapM (roles dummy)) { parametricVarFields := true }

private inductive Verdict where
  | admitted (compiled : Compiled)
  | refused
  | broken (message : String)

private def verdict (source : String) (dummy : Bool) (main : String := "Main():void={}") : Verdict :=
  match compileCase source dummy main with
  | .ok c =>
    if c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys then .admitted c
    else .broken "Core checks"
  | .error message =>
    if has message "dummy type value cannot" then .refused else .broken message

private def Verdict.text : Verdict → String
  | .admitted _ => "admitted"
  | .refused => "refused"
  | .broken message => s!"ERROR {message}"

private inductive Ran where
  | finished (output : String)
  | trapped
  | other (what : String)
deriving BEq

private def ran (compiled : Compiled) : Ran :=
  match compiled.prog.runB 10000000 10000 with
  | .res (.ok _, output) => .finished (String.ofList (output.map Char.ofNat))
  | .res (.err .user, _) => .trapped
  | .res _ => .other "another result"
  | .fuel => .other "out of fuel"
  | .deep => .other "too deep"

private def Ran.text : Ran → String
  | .finished _ => "finished"
  | .trapped => "executed the dummy"
  | .other what => what

/-- One case: its verdicts and, where it can be driven, what its runs do.
    Returns the failures, and whether the case was driven. -/
private def check (label source : String) (want : Want) (artifacts : Option String) (index : Nat) :
    IO (List String × Bool) := do
  let mut failures : List String := []
  let wantDummy := want == .admitted
  for main in ["Main():void={}"] ++ (driver source).toList do
    let driven := main != "Main():void={}"
    let real := verdict source false main
    let dummy := verdict source true main
    let name := if driven then s!"{label} (driven)" else label
    match real with
    | .admitted compiledReal =>
      match dummy, wantDummy with
      | .admitted _, false => failures := s!"{name}: the marked program is admitted" :: failures
      | .refused, true => failures := s!"{name}: the marked program is refused" :: failures
      | .broken message, _ => failures := s!"{name}: the marked program: {message}" :: failures
      | _, _ => pure ()
      if driven then
        let realRan := ran compiledReal
        match want with
        | .refused =>
          unless realRan == .trapped do
            failures := s!"{name}: the real program {realRan.text}" :: failures
          if realRan == .trapped then
            if let some out := artifacts then
              IO.FS.writeBinFile s!"{out}/trap-{index}.vbc" compiledReal.prog.encode
        | _ =>
          match realRan with
          | .finished output =>
            if let .admitted compiledDummy := dummy then
              unless ran compiledDummy == realRan do
                failures := s!"{name}: the marked program's run differs from the real one's" :: failures
              if let some out := artifacts then
                IO.FS.writeBinFile s!"{out}/forward-{index}.vbc" compiledDummy.prog.encode
                IO.FS.writeFile s!"{out}/forward-{index}.expected" output
            else if let some out := artifacts then
              IO.FS.writeBinFile s!"{out}/forward-{index}.vbc" compiledReal.prog.encode
              IO.FS.writeFile s!"{out}/forward-{index}.expected" output
          | _ => failures := s!"{name}: the real program {realRan.text}" :: failures
    | _ => failures := s!"{name}: the real program: {real.text}" :: failures
  return (failures.reverse, (driver source).isSome)

/-- `report` prints every case's verdicts; otherwise the contracts are
    checked, and the driven programs are written to the directory given. -/
def main (args : List String) : IO Unit := do
  if args.head? == some "report" then
    for (label, source, want) in all do
      if let some part := args[1]? then
        unless has label part do continue
      let dummy := verdict source true
      let real := verdict source false
      let run := match driver source, verdict source false ((driver source).getD "") with
        | some _, .admitted compiled => (ran compiled).text
        | some _, other => other.text
        | none, _ => "not driven"
      IO.println s!"{want.text}\t{label}\treal={real.text}\tdummy={dummy.text}\trun={run}"
      if let .error message := compileCase source true then IO.println s!"    {message}"
    return
  let artifacts := args.head?
  let mut failures := 0
  let mut driven := 0
  let mut index := 0
  for (label, source, want) in all do
    let (failed, wasDriven) ← check label source want artifacts index
    for failure in failed do IO.println s!"FAIL {failure}"
    failures := failures + failed.length
    if wasDriven then driven := driven + 1
    index := index + 1
  if failures > 0 then throw (IO.userError s!"{failures} metadata storage audit contracts failed")
  let count (want : Want) := (all.filter (·.2.2 == want)).length
  IO.println s!"metadata storage audit contracts passed ({count .refused} real/dummy refusals, {count .admitted} forwarding/overwrite pairs, {count .conservative} recorded conservative refusals; {driven} driven by a run)"
