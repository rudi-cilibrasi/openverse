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
          (name == "IgnoreMeta" && param.name == "M") ||
          (name == "FrameOwner" && param.name == "Initial") }
    return .fn p name ps tps specs (← ret.mapNamesM rename) (evidenceBody body)
  | .classDef p name nsp tps specs parents iface fields methods => do
    let rename (n : String) : Except String String :=
      pure (if n == "evidence" then SubtypeEvidence.family else n)
    let fields ← fields.mapM fun f => do return { f with ty := ← f.ty.mapNamesM rename }
    return .classDef p name nsp tps specs parents iface fields (← methods.mapM (roles dummy))
  | top => pure top

private def caller (body : String) : String :=
  "Caller(X:t,D:u,Dummy:u,P:evidence(evidence(vehicle,t),u) where t:type,u:type)<transacts>:int=\n" ++ body

-- Keep these callable paths live even when Main does not invoke Caller.
-- With no implementations, function-value dispatch lowers to a user error.
private def callables (source : String) : String :=
  "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\n" ++ source

private def recursiveReaders : String :=
  "reader:=class<computes>{N:int=7}\n" ++
  "Maybe(R:v,M:v,N:int where v:type)<computes>:v=if(N>0)then Bridge(R,M,N-1)else R\n" ++
  "Bridge(R:v,M:v,N:int where v:type)<computes>:v=if(N>0)then Maybe(R,M,N-1)else M\n" ++
  "Hold(R:reader,M:reader)<suspends>:reader=\n    var Stored:reader=R\n    Sleep(0.1)\n    set Stored=M\n    Stored\n"

-- The initializer is declared metadata in both controls. A real replacement
-- clears each owner's cell independently before its borrowed reader resumes.
private def frameOwners (first second : String) : String := callables
  ("pair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){}\n" ++
   "FrameOwner(P:pair(a,b),E:event(int),Initial:type{_()<computes>:int},Replacement:type{_()<computes>:int} where a:type,b:type)<suspends>:int=\n    var Stored:type{_()<computes>:int}=Initial\n    branch:\n        if(D:=dup[P]):\n            E.Await()\n            Value:=Stored()\n    set Stored=Replacement\n    E.Signal(0)\n    0\n" ++
   "Caller(P:pair(a,b),E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int} where a:type,b:type)<suspends>:int=\n    var Shadow:type{_()<computes>:int}=Dummy\n    branch:\n        Sleep(1.0)\n        set Shadow=Dummy\n" ++
   s!"    FrameOwner(P,E,F,{first})\n    Other:=event(int)\{}\n    FrameOwner(P,Other,F,{second})\n    0")

private def liftedTask (body tail : String) (setup : String := "")
    (prologue : String := "") (initial : String := "Dummy") : String := callables
  ("pair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){}\n" ++
   "Caller(P:pair(a,b),E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int} where a:type,b:type)<suspends>:int=\n    var Stored:type{_()<computes>:int}=" ++ initial ++ "\n" ++ setup ++
   "    if(D:=dup[P]):\n        branch:\n" ++ prologue ++ "            E.Await()\n" ++ body ++ tail)

private def ordinaryBorrowedReader (overwrite : Bool) : String := callables
  ("Dup(N:int)<computes>:int=N|N\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:[]int=\n    var Stored:type{_()<computes>:int}=Dummy\n" ++
    (if overwrite then "    set Stored=F\n" else "") ++
    "    for(A:=(Dup(1)|Dup(2)),B:=(Dup(1)|Dup(2))):\n        Sleep(0.01)\n        Stored()")

private def moduleFunction (body : String) : String := callables
  ("session_key:=class<unique><module_scoped_var_weak_map_key>{}\nfunction_box:=class{Value:type{_()<computes>:int}}\nvar Functions:weak_map(session_key,type{_()<computes>:int})=map{}\nvar Optional:weak_map(session_key,?type{_()<computes>:int})=map{}\nvar Boxes:weak_map(session_key,function_box)=map{}\nCache:=module:\n    var NestedFunctions<public>:weak_map(session_key,type{_()<computes>:int})=map{}\nIdentity(V:v where v:type)<computes>:v=V\nIgnore(V:v,Real:type{_()<computes>:int} where v:type)<computes>:type{_()<computes>:int}=Real\nPut(Key:session_key,Value:type{_()<computes>:int})<transacts><decides>:void=set Functions[Key]=Value\nGet(Key:session_key)<transacts><decides>:type{_()<computes>:int}=Functions[Key]\n" ++
   "Caller(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n" ++ body)

private def returnedArgument (helper body : String) : String := callables
  ("UseFn(Value:type{_()<computes>:int})<computes>:int=Value()\nUseNamed(?Value:type{_()<computes>:int}=One)<computes>:int=Value()\nbox(v:type):=class<computes>{Value:v}\n" ++ helper ++
   "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=\n" ++ body)

private def returnedProof (helper body : String) : String :=
  "proof_box(v:type):=class<computes>{Value:v}\n" ++
  "UseProof(X:t,Proof:evidence(vehicle,t) where t:type)<computes>:int=Proof.Up(X).N\n" ++
  helper ++ "Caller(X:t,F:evidence(vehicle,t),Dummy:evidence(vehicle,t) where t:type)<computes>:int=\n" ++ body

private def activeRushCleanup (action overwrite : String) : String := callables
  ("Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    E:=event(int){}\n    branch:\n        R:=rush:\n            block:\n                defer:\n                    " ++ action ++
   "\n                Sleep(0.1)\n                E.Signal(1)\n                Sleep(1.0)\n                1\n            block:\n                Sleep(1.0)\n                1\n" ++ overwrite ++ "    E.Await()\n    0")

private def activeRushContinuation (body tail overwrite : String) : String := callables
  ("Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    E:=event(int){}\n    branch:\n        R:=rush:\n            block:\n                Sleep(0.1)\n                E.Signal(1)\n" ++ body ++
   "                1\n            block:\n                Sleep(1.0)\n                1\n" ++ tail ++ overwrite ++ "    E.Await()\n    0")

private def caseCapture (body : String) : String :=
  "pair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){C:int=4}\nCaller(P:pair(a,b),F:type{_()<computes>:int},Dummy:type{_()<computes>:int} where a:type,b:type)" ++ body

private def rangeCapture (body : String) : String :=
  "pair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){Lo:int=1;Hi:int=2}\nCaller(P:pair(a,b),F:type{_()<computes>:int},Dummy:type{_()<computes>:int} where a:type,b:type)" ++ body

private def constructorCapture (body : String) : String :=
  "pair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){C:int=4}\nrefbox:=class{Before:int=0;Value:int}\nvalbox:=struct{Before:int=0;Value:int}\nouter:=struct{Inner:refbox}\nCaller(P:pair(a,b),F:type{_()<computes>:int},Dummy:type{_()<computes>:int} where a:type,b:type)" ++ body

private def setIndexCapture (body : String) : String :=
  "pair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){Index:int=0}\ncell:=class{var Value:int=0}\nholder:=class{Items:[]cell}\nId(N:int)<computes>:int=N\nCaller(P:pair(a,b),F:type{_()<computes>:int},Dummy:type{_()<computes>:int} where a:type,b:type)" ++ body

private def namedCapture (body : String) : String :=
  "pair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){Index:int=0}\nSelect(?Index:int=0)<computes>:int=Index\nreader:=class<computes>{Pick(?Index:int=0)<computes>:int=Index}\nbox:=struct{Value:int}\nCaller(P:pair(a,b),F:type{_()<computes>:int},Dummy:type{_()<computes>:int} where a:type,b:type)" ++ body

private def cases : List (String × String) := [
  ("named call metadata capture", namedCapture "<transacts><decides>:int=\n    Select(?Index:=dup[P].Index+Dummy())"),
  ("named method metadata capture", namedCapture "<transacts><decides>:int=\n    reader{}.Pick(?Index:=dup[P].Index+Dummy())"),
  ("named field metadata capture", namedCapture "<transacts><decides>:int=\n    box{Value:=Select(?Index:=dup[P].Index+Dummy())}.Value"),
  ("set index array metadata capture", setIndexCapture "<transacts><decides>:int=\n    var A:[]int=array{0}\n    set A[dup[P].Index+Dummy()]=7\n    0"),
  ("set index object path metadata capture", setIndexCapture "<transacts><decides>:int=\n    H:=holder{Items:=array{cell{}}}\n    set H.Items[dup[P].Index+Dummy()].Value=7\n    0"),
  ("set index expression metadata capture", setIndexCapture "<transacts><decides>:int=\n    var A:[]int=array{0}\n    Id(set A[dup[P].Index+Dummy()]=7)"),
  ("constructor class metadata capture", constructorCapture "<transacts><decides>:int=refbox{Value:=dup[P].C+Dummy()}.Value"),
  ("constructor struct metadata capture", constructorCapture "<transacts><decides>:int=valbox{Value:=dup[P].C+Dummy()}.Value"),
  ("constructor nested metadata capture", constructorCapture "<transacts><decides>:int=outer{Inner:=refbox{Value:=dup[P].C+Dummy()}}.Inner.Value"),
  ("range lower metadata capture", rangeCapture "<transacts>:[]int=for(I:=dup[P].Lo+Dummy()..3){I}"),
  ("range upper metadata capture", rangeCapture "<transacts>:[]int=for(I:=0..dup[P].Hi+Dummy()){I}"),
  ("range first prefix metadata capture", rangeCapture "<transacts><decides>:int=first{Offset:=(0|1);I:=Offset+dup[P].Lo..Offset+dup[P].Hi+Dummy();I>1;I}"),
  ("conditional refined generator metadata object method", "pair(a:type,b:type):=class{A:a;B:b}\ndup(t:type):=class(pair(t,t)):\n    Items:[]int=array{1,2}\n    C:int=2\n    Read()<computes>:int=C\nCaller(Dummy:pair(a,b),Real:pair(a,b),N:int where a:type,b:type)<transacts>:[]int=\n    var P:pair(a,b)=Dummy\n    for(D:=dup[P],X:D.Items,Y:=(if(N>0)then(D.Read()|D.C)else 0)){Y}\n"),
  ("conditional refined generator read-False", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\npair(a:type, b:type) := class:\n    A:a\n    B:b\ndup(t:type) := class(pair(t, t)):\n    Items:[]t = array{}\n    C:int = 1\nCaller(P:pair(a,b),F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int where a:type,b:type)<transacts>:[]int=\n    var Stored:type{_()<computes>:int}=Dummy\n    for(D:=dup[P],X:D.Items,Y:=(if(N>0)then(Stored()|D.C)else 0)){Y}\n"),
  ("conditional refined generator write-False", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\npair(a:type, b:type) := class:\n    A:a\n    B:b\ndup(t:type) := class(pair(t, t)):\n    Items:[]t = array{}\n    C:int = 1\nCaller(P:pair(a,b),F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int where a:type,b:type)<transacts>:[]int=\n    var Stored:type{_()<computes>:int}=F\n    Values:=for(D:=dup[P],X:D.Items,Y:=(if(N>0)then block{set Stored=Dummy;(D.C|10)}else 0)){Y}\n    Value:=Stored()\n    Values\n"),
  ("case arm metadata capture", caseCapture "<transacts><decides>:int=case(1){1=>dup[P].C+Dummy(),_=>0}"),
  ("case scrutinee metadata capture", caseCapture "<transacts><decides>:int=case(dup[P].C+Dummy()){4=>1,_=>0}"),
  ("case pattern metadata capture", caseCapture "<transacts>:int=case(4){dup[P].C+Dummy()=>1,_=>0}"),
  ("post-return child pending metadata cleanup", activeRushContinuation
    "                branch:\n                    defer:\n                        Value:=Stored()\n                    loop:\n                        Sleep(1.0)\n                Sleep(1.0)\n"
    "" ""),
  ("post-return child delayed metadata read", activeRushContinuation
    "                branch:\n                    Sleep(0.1)\n                    Value:=Stored()\n                Sleep(1.0)\n"
    "" ""),
  ("post-return child delayed metadata write", activeRushContinuation
    "                branch:\n                    Sleep(0.1)\n                    set Stored=Dummy\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("post-return child delayed metadata cleanup", activeRushContinuation
    "                branch:\n                    defer:\n                        Value:=Stored()\n                    Sleep(0.1)\n                Sleep(1.0)\n"
    "" ""),
  ("post-return grandchild metadata read", activeRushContinuation
    "                branch:\n                    Sleep(0.1)\n                    branch:\n                        Sleep(0.1)\n                        Value:=Stored()\n                Sleep(1.0)\n"
    "" ""),
  ("primitive payload eq-direct-Dummy", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Alias:=Dummy=Real)then Alias.Read()else 0\n"),
  ("primitive payload eq-array-Dummy", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Values:=array{Dummy}=array{Real},Alias:=Values[0])then Alias.Read()else 0\n"),
  ("primitive payload eq-helper-Dummy", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nChoose(A:reader,B:reader)<computes><decides>:reader=A=B\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Alias:=Choose[Dummy,Real])then Alias.Read()else 0\n"),
  ("primitive payload ne-direct-Dummy", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Alias:=Dummy<>Real)then Alias.Read()else 0\n"),
  ("primitive payload ne-array-Dummy", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Values:=array{Dummy}<>array{Real},Alias:=Values[0])then Alias.Read()else 0\n"),
  ("primitive payload ne-helper-Dummy", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nChoose(A:reader,B:reader)<computes><decides>:reader=A<>B\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Alias:=Choose[Dummy,Real])then Alias.Read()else 0\n"),
  ("primitive payload index_metadata", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Dummy:[]reader,Index:int)<computes>:int=\n    if(Alias:=Dummy[Index])then Alias.Read()else 0\n"),
  ("primitive payload update_metadata", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Items:[]reader,Dummy:reader,Index:int)<computes>:int=\n    var Updated:[]reader=Items\n    if(set Updated[Index]=Dummy,Alias:=Updated[0])then Alias.Read()else 0\n"),
  ("primitive payload update_metadata_container", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Dummy:[]reader,Real:reader,Index:int)<computes>:int=\n    var Updated:[]reader=Dummy\n    if(set Updated[Index]=Real,Alias:=Updated[0])then Alias.Read()else 0\n"),
  ("primitive payload eq-right-operand-executes", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nInspect(R:reader)<computes>:reader=\n    Value:=R.Read()\n    R\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Alias:=Real=Inspect(Dummy))then Alias.Read()else 0\n"),
  ("primitive payload ne-right-operand-executes", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nInspect(R:reader)<computes>:reader=\n    Value:=R.Read()\n    R\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Alias:=Real<>Inspect(Dummy))then Alias.Read()else 0\n"),
  ("primitive payload index-operand-executes", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nIndex(R:reader)<computes>:int=R.Read()\nCaller(Items:[]reader,Dummy:reader)<computes>:int=\n    if(Alias:=Items[Index(Dummy)])then Alias.Read()else 0\n"),
  ("active cancellation late-MetadataRead", activeRushContinuation
    "                defer:\n                    Value:=Stored()\n                Sleep(1.0)\n"
    "" ""),
  ("active cancellation late-MetadataWrite", activeRushContinuation
    "                defer:\n                    set Stored=Dummy\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("active cancellation direct-MetadataRead", activeRushContinuation
    "                Value:=Stored()\n                Sleep(1.0)\n"
    "" ""),
  ("active cancellation direct-MetadataWrite", activeRushContinuation
    "                set Stored=Dummy\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("active cancellation afterrush-MetadataRead", activeRushContinuation
    ""
    "        defer:\n            Value:=Stored()\n        Sleep(1.0)\n" ""),
  ("active cancellation afterrush-MetadataWrite", activeRushContinuation
    ""
    "        defer:\n            set Stored=Dummy\n        Sleep(1.0)\n" "    set Stored=F\n"),
  ("running rush cleanup cannot execute metadata",
    activeRushCleanup "Value:=Stored()" ""),
  ("running rush cleanup cannot restore metadata to a real cell",
    activeRushCleanup "set Stored=Dummy" "    set Stored=F\n"),
  ("metadata returned proof argument Direct", returnedProof
    "Pass(M:v,R:v where v:type)<computes>:v=M\n"
    "    UseProof(X,Pass(Dummy,F))"),
  ("metadata returned proof argument Failable", returnedProof
    "Pass(M:v,R:v where v:type)<computes><decides>:v=block{true?;M}\n"
    "    if(V:=Pass[Dummy,F])then UseProof(X,V)else 0"),
  ("metadata returned proof argument Field", returnedProof
    "Pass(M:v,R:v where v:type)<computes>:proof_box(v)=proof_box(v){Value:=M}\n"
    "    UseProof(X,Pass(Dummy,F).Value)"),
  ("module function storage Direct", moduleFunction
    "    if(set Functions[Key]=Dummy,V:=Functions[Key])then V()else 0"),
  ("module function storage Unused", moduleFunction
    "    if(set Functions[Key]=Dummy){}\n    0"),
  ("module function storage Helper", moduleFunction
    "    if(Put[Key,Dummy],V:=Get[Key])then V()else 0"),
  ("module function storage Generic", moduleFunction
    "    if(set Functions[Key]=Identity(Dummy),V:=Functions[Key])then V()else 0"),
  ("module function storage Optional", moduleFunction
    "    if(set Optional[Key]=option{Dummy},Maybe:=Optional[Key],V:=Maybe?)then V()else 0"),
  ("module function storage Boxed", moduleFunction
    "    H:=function_box{Value:=Dummy}\n    if(set Boxes[Key]=H,V:=Boxes[Key])then V.Value()else 0"),
  ("module function storage Nested", moduleFunction
    "    if(set Cache.NestedFunctions[Key]=Dummy,V:=Cache.NestedFunctions[Key])then V()else 0"),
  ("module function storage Rollback", moduleFunction
    "    if(set Functions[Key]=Dummy;false?){}\n    0"),
  ("module function storage Overwrite", moduleFunction
    "    if(set Functions[Key]=Dummy;set Functions[Key]=F;V:=Functions[Key])then V()else 0"),
  ("metadata returned function argument Direct", returnedArgument
    "Pass(M:v,R:v where v:type)<computes>:v=M\n"
    "    UseFn(Pass(Dummy,F))"),
  ("metadata returned function argument Failable", returnedArgument
    "Pass(M:v,R:v where v:type)<decides><computes>:v=block{true?;M}\n"
    "    if(V:=Pass[Dummy,F])then UseFn(V)else 0"),
  ("metadata returned function argument Recursive", returnedArgument
    "Pass(M:v,R:v,N:int where v:type)<computes>:v=if(N>0)then Pass(M,R,N-1)else M\n"
    "    UseFn(Pass(Dummy,F,1))"),
  ("metadata returned function argument Field", returnedArgument
    "Pass(M:v,R:v where v:type)<computes>:box(v)=box(v){Value:=M}\n"
    "    UseFn(Pass(Dummy,F).Value)"),
  ("metadata returned function argument Named", returnedArgument
    "Pass(M:v,R:v where v:type)<computes>:v=M\n"
    "    UseNamed(?Value:=Pass(Dummy,F))"),
  ("lifted writer cannot put metadata into an initially real cell",
    liftedTask "            set Stored=Dummy\n" "    E.Signal(0)\n    Stored()" (initial := "F")),
  ("lifted real-cell write is checked without a later read",
    liftedTask "            set Stored=Dummy\n" "    E.Signal(0)\n    0" (initial := "F")),
  ("lifted task can execute metadata without a metadata cell",
    liftedTask "            Value:=Dummy()\n" "    E.Signal(0)\n    0" (initial := "F")),
  ("lifted branch cleanup sees the actual owner's data mode",
    liftedTask "" "    0" "    defer:\n        set Stored=F\n"
      "            defer:\n                set Stored=Dummy\n"),
  ("nonescaping borrowed metadata reader", ordinaryBorrowedReader false),
  ("lifted branch survives its helper and writes metadata",
    liftedTask "            set Stored=Dummy\n" "    set Stored=F\n    E.Signal(0)\n    Stored()"),
  ("lifted branch metadata write is checked even without a later read",
    liftedTask "            set Stored=Dummy\n" "    set Stored=F\n    E.Signal(0)\n    0"),
  ("lifted branch survives its helper and executes metadata",
    liftedTask "            Value:=Stored()\n" "    E.Signal(0)\n    0"),
  ("recursive producer cannot hide a borrowed metadata write", callables
    "Digit(N:int)<computes>:int=if(N>0)then (Digit(N-1)|N)else 0\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    branch:\n        Values:=for(A:=(Digit(1)|Digit(1)),B:=(Digit(1)|Digit(1))):\n            E.Await()\n            set Stored=Dummy\n            0\n    set Stored=F\n    E.Signal(0)\n    Stored()"),
  ("first borrowed owner cannot borrow the second owner's overwrite", frameOwners "Dummy" "F"),
  ("second borrowed owner cannot borrow the first owner's overwrite", frameOwners "F" "Dummy"),
  ("borrowed frame metadata write after real overwrite", callables
    "Dup(N:int)<computes>:int=N|N\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    Values:=for(A:=(Dup(1)|Dup(2)),B:=(Dup(1)|Dup(2))):\n        Sleep(0.01)\n        set Stored=Dummy\n        0\n    Stored()"),
  ("borrowed frame immutable alias survives real overwrite", callables
    "Dup(N:int)<computes>:int=N|N\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:[]int=\n    var Stored:type{_()<computes>:int}=Dummy\n    Saved:=Stored\n    set Stored=F\n    for(A:=(Dup(1)|Dup(2)),B:=(Dup(1)|Dup(2))):block{Sleep(0.01);Saved()}"),
  ("borrowed frame metadata read in cancellation", callables
    "Dup(N:int)<computes>:int=N|N\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:[]int=\n    var Stored:type{_()<computes>:int}=Dummy\n    for(A:=(Dup(1)|Dup(2)),B:=(Dup(1)|Dup(2))):\n        defer:\n            Value:=Stored()\n        loop{Sleep(1.0)}\n        0"),
  ("outer metadata-only local loses mode across loop iterations", callables "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    var N:int=0\n    loop:\n        if(N>0)then set Stored=Dummy\n        set Stored=F\n        Sleep(0.01)\n        set N+=1\n        if(N>=2)then break\n    0"),
  ("outer shared local retains data mode across loop iterations", callables "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    loop:\n        set Stored=Dummy\n        Sleep(0.01)\n        break\n    Stored()"),
  ("fresh loop local still rejects metadata execution", callables "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    loop:\n        var Stored:type{_()<computes>:int}=Dummy\n        Sleep(0.01)\n        Value:=Stored()\n        break\n    0"),
  ("live helper shared initializer", recursiveReaders ++
    "Caller(F:reader,Dummy:reader)<suspends>:reader=Hold(F,Dummy)"),
  ("shared frame reused after real overwrite", callables "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    Values:=sync:\n        block:\n            Sleep(0.2)\n            Stored()\n        block:\n            Sleep(0.1)\n            set Stored=Dummy\n    Values(0)"),
  ("shared frame forwarded after real overwrite", callables "Keep(V:v where v:type)<computes>:v=V\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    Values:=sync:\n        block:\n            Sleep(0.2)\n            Keep(Stored)()\n        block:\n            Sleep(0.1)\n            set Stored=Dummy\n    Values(0)"),
  ("shared evidence reused after real overwrite", "Caller(X:t,D:u,Dummy:u,P:evidence(evidence(vehicle,t),u) where t:type,u:type)<suspends>:int=\n    var Stored:u=Dummy\n    set Stored=D\n    Values:=sync:\n        block:\n            Sleep(0.2)\n            P.Up(Stored).Up(X).N\n        block:\n            Sleep(0.1)\n            set Stored=Dummy\n    Values(0)"),
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
  ("named call real overwrite", namedCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    Select(?Index:=dup[P].Index+Stored())"),
  ("named method real overwrite", namedCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    reader{}.Pick(?Index:=dup[P].Index+Stored())"),
  ("named field real overwrite", namedCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    box{Value:=Select(?Index:=dup[P].Index+Stored())}.Value"),
  ("set index array real overwrite", setIndexCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    var A:[]int=array{0}\n    set A[dup[P].Index+Stored()]=7\n    0"),
  ("set index object path real overwrite", setIndexCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    H:=holder{Items:=array{cell{}}}\n    set H.Items[dup[P].Index+Stored()].Value=7\n    0"),
  ("set index expression real overwrite", setIndexCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    var A:[]int=array{0}\n    Id(set A[dup[P].Index+Stored()]=7)"),
  ("constructor class real overwrite", constructorCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    refbox{Value:=dup[P].C+Stored()}.Value"),
  ("constructor struct real overwrite", constructorCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    valbox{Value:=dup[P].C+Stored()}.Value"),
  ("constructor nested real overwrite", constructorCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    outer{Inner:=refbox{Value:=dup[P].C+Stored()}}.Inner.Value"),
  ("range lower real overwrite", rangeCapture "<transacts>:[]int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    for(I:=dup[P].Lo+Stored()..3){I}"),
  ("range upper real overwrite", rangeCapture "<transacts>:[]int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    for(I:=0..dup[P].Hi+Stored()){I}"),
  ("range first prefix real overwrite", rangeCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    first{Offset:=(0|1);I:=Offset+dup[P].Lo..Offset+dup[P].Hi+Stored();I>1;I}"),
  ("conditional refined generator real overwritten object method", "pair(a:type,b:type):=class{A:a;B:b}\ndup(t:type):=class(pair(t,t)):\n    Items:[]int=array{1,2}\n    C:int=2\n    Read()<computes>:int=C\nCaller(Dummy:pair(a,b),Real:pair(a,b),N:int where a:type,b:type)<transacts>:[]int=\n    var P:pair(a,b)=Dummy\n    set P=Real\n    for(D:=dup[P],X:D.Items,Y:=(if(N>0)then(D.Read()|D.C)else 0)){Y}\n"),
  ("conditional refined generator read-True", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\npair(a:type, b:type) := class:\n    A:a\n    B:b\ndup(t:type) := class(pair(t, t)):\n    Items:[]t = array{}\n    C:int = 1\nCaller(P:pair(a,b),F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int where a:type,b:type)<transacts>:[]int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    for(D:=dup[P],X:D.Items,Y:=(if(N>0)then(Stored()|D.C)else 0)){Y}\n"),
  ("conditional refined generator write-True", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\npair(a:type, b:type) := class:\n    A:a\n    B:b\ndup(t:type) := class(pair(t, t)):\n    Items:[]t = array{}\n    C:int = 1\nCaller(P:pair(a,b),F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int where a:type,b:type)<transacts>:[]int=\n    var Stored:type{_()<computes>:int}=F\n    Values:=for(D:=dup[P],X:D.Items,Y:=(if(N>0)then block{set Stored=F;(D.C|10)}else 0)){Y}\n    Value:=Stored()\n    Values\n"),
  ("case arm real overwrite", caseCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    case(1){1=>dup[P].C+Stored(),_=>0}"),
  ("case scrutinee real overwrite", caseCapture "<transacts><decides>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    case(dup[P].C+Stored()){4=>1,_=>0}"),
  ("case pattern real overwrite", caseCapture "<transacts>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    case(4){dup[P].C+Stored()=>1,_=>0}"),
  ("post-return child pending real cleanup", activeRushContinuation
    "                branch:\n                    defer:\n                        Value:=Stored()\n                    loop:\n                        Sleep(1.0)\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("post-return child delayed real read", activeRushContinuation
    "                branch:\n                    Sleep(0.1)\n                    Value:=Stored()\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("post-return child delayed real write", activeRushContinuation
    "                branch:\n                    Sleep(0.1)\n                    set Stored=F\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("post-return child delayed real cleanup", activeRushContinuation
    "                branch:\n                    defer:\n                        Value:=Stored()\n                    Sleep(0.1)\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("post-return grandchild real read", activeRushContinuation
    "                branch:\n                    Sleep(0.1)\n                    branch:\n                        Sleep(0.1)\n                        Value:=Stored()\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("unreached post-return child metadata read", activeRushContinuation
    "                Sleep(1.0)\n                branch:\n                    Sleep(0.1)\n                    Value:=Stored()\n                Sleep(1.0)\n"
    "" ""),
  ("unreached post-return child real read", activeRushContinuation
    "                Sleep(1.0)\n                branch:\n                    Sleep(0.1)\n                    Value:=Stored()\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("primitive payload eq-direct-Real", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Alias:=Real=Dummy)then Alias.Read()else 0\n"),
  ("primitive payload eq-array-Real", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Values:=array{Real}=array{Dummy},Alias:=Values[0])then Alias.Read()else 0\n"),
  ("primitive payload eq-helper-Real", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nChoose(A:reader,B:reader)<computes><decides>:reader=A=B\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Alias:=Choose[Real,Dummy])then Alias.Read()else 0\n"),
  ("primitive payload ne-direct-Real", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Alias:=Real<>Dummy)then Alias.Read()else 0\n"),
  ("primitive payload ne-array-Real", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Values:=array{Real}<>array{Dummy},Alias:=Values[0])then Alias.Read()else 0\n"),
  ("primitive payload ne-helper-Real", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nChoose(A:reader,B:reader)<computes><decides>:reader=A<>B\nCaller(Real:reader,Dummy:reader)<computes>:int=\n    if(Alias:=Choose[Real,Dummy])then Alias.Read()else 0\n"),
  ("primitive payload index_real", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Items:[]reader,Dummy:int)<computes>:int=\n    if(Alias:=Items[Dummy])then Alias.Read()else 0\n"),
  ("primitive payload update_real", "reader:=class<unique>{N:int;Read()<computes>:int=N}\nCaller(Items:[]reader,Real:reader,Dummy:int)<computes>:int=\n    var Updated:[]reader=Items\n    if(set Updated[Dummy]=Real,Alias:=Updated[0])then Alias.Read()else 0\n"),
  ("active cancellation late-RealRead", activeRushContinuation
    "                defer:\n                    Value:=Stored()\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("active cancellation late-RealWrite", activeRushContinuation
    "                defer:\n                    set Stored=F\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("active cancellation direct-RealRead", activeRushContinuation
    "                Value:=Stored()\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("active cancellation direct-RealWrite", activeRushContinuation
    "                set Stored=F\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("active cancellation afterwait-MetadataRead", activeRushContinuation
    "                Sleep(1.0)\n                defer:\n                    Value:=Stored()\n                Sleep(1.0)\n"
    "" ""),
  ("active cancellation afterwait-RealRead", activeRushContinuation
    "                Sleep(1.0)\n                defer:\n                    Value:=Stored()\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("active cancellation afterwait-MetadataWrite", activeRushContinuation
    "                Sleep(1.0)\n                defer:\n                    set Stored=Dummy\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("active cancellation afterwait-RealWrite", activeRushContinuation
    "                Sleep(1.0)\n                defer:\n                    set Stored=F\n                Sleep(1.0)\n"
    "" "    set Stored=F\n"),
  ("active cancellation afterrush-RealRead", activeRushContinuation
    ""
    "        defer:\n            Value:=Stored()\n        Sleep(1.0)\n" "    set Stored=F\n"),
  ("active cancellation afterrush-RealWrite", activeRushContinuation
    ""
    "        defer:\n            set Stored=F\n        Sleep(1.0)\n" "    set Stored=F\n"),
  ("running rush cleanup reads a real overwrite",
    activeRushCleanup "Value:=Stored()" "    set Stored=F\n"),
  ("running rush cleanup writes ordinary data",
    activeRushCleanup "set Stored=F" "    set Stored=F\n"),
  ("real returned proof argument Direct", returnedProof
    "Pass(M:v,R:v where v:type)<computes>:v=R\n"
    "    UseProof(X,Pass(Dummy,F))"),
  ("real returned proof argument Failable", returnedProof
    "Pass(M:v,R:v where v:type)<computes><decides>:v=block{true?;R}\n"
    "    if(V:=Pass[Dummy,F])then UseProof(X,V)else 0"),
  ("real returned proof argument Field", returnedProof
    "Pass(M:v,R:v where v:type)<computes>:proof_box(v)=proof_box(v){Value:=R}\n"
    "    UseProof(X,Pass(Dummy,F).Value)"),
  ("module function storage Real", moduleFunction
    "    if(set Functions[Key]=F,V:=Functions[Key])then V()else 0"),
  ("module function storage IgnoreMetadata", moduleFunction
    "    if(set Functions[Key]=Ignore(Dummy,F),V:=Functions[Key])then V()else 0"),
  ("module function storage RealHelper", moduleFunction
    "    if(Put[Key,Ignore(Dummy,F)],V:=Get[Key])then V()else 0"),
  ("module function storage RealRollback", moduleFunction
    "    if(set Functions[Key]=F){}\n    if(set Functions[Key]=Ignore(Dummy,F);false?){}\n    if(V:=Functions[Key])then V()else 0"),
  ("module function storage RealOptional", moduleFunction
    "    if(set Optional[Key]=option{Ignore(Dummy,F)},Maybe:=Optional[Key],V:=Maybe?)then V()else 0"),
  ("module function storage RealBoxed", moduleFunction
    "    H:=function_box{Value:=Ignore(Dummy,F)}\n    if(set Boxes[Key]=H,V:=Boxes[Key])then V.Value()else 0"),
  ("real returned function argument Direct", returnedArgument
    "Pass(M:v,R:v where v:type)<computes>:v=R\n"
    "    UseFn(Pass(Dummy,F))"),
  ("real returned function argument Failable", returnedArgument
    "Pass(M:v,R:v where v:type)<decides><computes>:v=block{true?;R}\n"
    "    if(V:=Pass[Dummy,F])then UseFn(V)else 0"),
  ("real returned function argument Recursive", returnedArgument
    "Pass(M:v,R:v,N:int where v:type)<computes>:v=if(N>0)then Pass(M,R,N-1)else R\n"
    "    UseFn(Pass(Dummy,F,1))"),
  ("real returned function argument Field", returnedArgument
    "Pass(M:v,R:v where v:type)<computes>:box(v)=box(v){Value:=R}\n"
    "    UseFn(Pass(Dummy,F).Value)"),
  ("real returned function argument Named", returnedArgument
    "Pass(M:v,R:v where v:type)<computes>:v=R\n"
    "    UseNamed(?Value:=Pass(Dummy,F))"),
  ("canceled lifted writer leaves an initially real cell alone",
    liftedTask "            set Stored=Dummy\n" "    0" (initial := "F")),
  ("canceled lifted task does not execute its metadata receiver",
    liftedTask "            Value:=Dummy()\n" "    0" (initial := "F")),
  ("lifted task reads an initially real cell",
    liftedTask "            Value:=Stored()\n" "    E.Signal(0)\n    0" (initial := "F")),
  ("actual owner cleanup precedes its lifted branch cleanup",
    liftedTask "" "    0" "    defer:\n        set Stored=F\n"
      "            defer:\n                Value:=Stored()\n"),
  ("nonescaping borrowed reader retains the cheap real overwrite", ordinaryBorrowedReader true),
  ("lifted branch is canceled by its actual owner before Signal",
    liftedTask "            set Stored=Dummy\n" "    set Stored=F\n    0"),
  ("lifted reader observes its actual owner's real overwrite",
    liftedTask "            Value:=Stored()\n" "    set Stored=F\n    E.Signal(0)\n    0"),
  ("borrowed owners retain separate real overwrites", frameOwners "F" "F"),
  ("borrowed frame reader sees a real overwrite before Signal", callables
    "Dup(N:int)<computes>:int=N|N\nCaller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    branch:\n        Values:=for(A:=(Dup(1)|Dup(2)),B:=(Dup(1)|Dup(2))):\n            E.Await()\n            Stored()\n    set Stored=F\n    E.Signal(0)\n    0"),
  ("opaque borrowed mutable frame", callables
    "Dup(N:int)<computes>:int=N|N\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:[]type{_()<computes>:int}=\n    var Stored:type{_()<computes>:int}=Dummy\n    for(A:=(Dup(1)|Dup(2)),B:=(Dup(1)|Dup(2))):block{Sleep(0.01);Stored}"),
  ("fresh shared local on each loop iteration", callables "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var N:int=0\n    loop:\n        var Stored:type{_()<computes>:int}=Dummy\n        set Stored=F\n        Sleep(0.01)\n        Value:=Stored()\n        set N+=1\n        if(N>=2)then break\n    N"),
  ("fresh shared local on each for iteration", callables "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:[]int=\n    for(N:=0..1):\n        var Stored:type{_()<computes>:int}=Dummy\n        set Stored=F\n        Sleep(0.01)\n        Stored()"),
  ("opaque recursive initializer through helper", recursiveReaders ++
    "Caller(F:reader,Dummy:reader)<suspends>:reader=Hold(Maybe(F,Dummy,3),Dummy)"),
  ("opaque recursive initializer through two helpers", recursiveReaders ++
    "Keep(V:v where v:type)<computes>:v=V\nCaller(F:reader,Dummy:reader)<suspends>:reader=Hold(Keep(Maybe(F,Dummy,3)),Dummy)"),
  ("opaque recursive initializer with reordered helper arguments", recursiveReaders ++
    "Flip(M:reader,R:reader)<suspends>:reader=Hold(R,M)\nCaller(F:reader,Dummy:reader)<suspends>:reader=Flip(Dummy,Maybe(F,Dummy,3))"),
  ("opaque recursive shared initializer", "Maybe(R:v,M:v,N:int where v:type)<computes>:v=if(N>0)then Bridge(R,M,N-1)else R\nBridge(R:v,M:v,N:int where v:type)<computes>:v=if(N>0)then Maybe(R,M,N-1)else M\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:type{_()<computes>:int}=\n    var Stored:type{_()<computes>:int}=Maybe(F,Dummy,3)\n    Sleep(0.1)\n    set Stored=Dummy\n    Stored"),
  ("shared real overwrite", "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    Sleep(0.1)\n    Stored()"),
  ("shared rolled back real overwrite", "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:type{_()<computes>:int}=\n    var Stored:type{_()<computes>:int}=Dummy\n    if(set Stored=F;false?){}\n    Sleep(0.1)\n    set Stored=Dummy\n    Stored"),
  ("opaque nonshared real transition", "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:type{_()<computes>:int}=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    set Stored=Dummy\n    Stored"),
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
