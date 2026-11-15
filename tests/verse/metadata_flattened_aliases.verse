One()<computes>:int=1
Two()<computes>:int=2
Pick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two
FlatEvents(X:[][]t where t:type):[]t=Concatenate(X)
Work(E:event(int))<suspends>:int=E.Await()
FlatSignal(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    Flat:[]event(int)=Concatenate(array{array{E}})
    if(Alias:=Flat[0])then Alias.Signal(0)
    Stored()
UnrelatedSignal(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    Flat:[]event(int)=Concatenate(array{array{Other}})
    if(Alias:=Flat[0])then Alias.Signal(0)
    Stored()
NestedSignal(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    Flat:[]event(int)=Concatenate(Concatenate(array{array{array{E}}}))
    if(Alias:=Flat[0])then Alias.Signal(0)
    Stored()
HelperSignal(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    Flat:[]event(int)=FlatEvents(array{array{E}})
    if(Alias:=Flat[0])then Alias.Signal(0)
    Stored()
ConcatSignal(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    Flat:[]event(int)=Concatenate(array{E},array{Other})
    if(Alias:=Flat[0])then Alias.Signal(0)
    Stored()
FlatAwait(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        Flat:=Concatenate(array{array{E}})
        if(Alias:=Flat[0]):
            Alias.Await()
            set Stored=Dummy
    set Stored=F
    E.Signal(0)
    Stored()
FlatTask(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    Other:=event(int){}
    T:=spawn{Work(E)}
    Tasks:=Concatenate(array{array{T}})
    var Stored:type{_()<computes>:int}=Dummy
    if(Alias:=Tasks[0]):
        branch:
            Alias.Await()
            set Stored=Dummy
        set Stored=F
        E.Signal(0)
        Stored()
    else:
        0
UnrelatedTask(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    Other:=event(int){}
    T:=spawn{Work(E)}
    Tasks:=Concatenate(array{array{T}})
    var Stored:type{_()<computes>:int}=Dummy
    if(Alias:=Tasks[0]):
        branch:
            Alias.Await()
            set Stored=Dummy
        set Stored=F
        Other.Signal(0)
        Stored()
    else:
        0
Main()<suspends>:void=
    Print("FlatSignal {FlatSignal(event(int){},One,Two)}")
    Print("UnrelatedSignal {UnrelatedSignal(event(int){},One,Two)}")
    Print("NestedSignal {NestedSignal(event(int){},One,Two)}")
    Print("HelperSignal {HelperSignal(event(int){},One,Two)}")
    Print("ConcatSignal {ConcatSignal(event(int){},One,Two)}")
    Print("FlatAwait {FlatAwait(event(int){},One,Two)}")
    Print("FlatTask {FlatTask(event(int){},One,Two)}")
    Print("UnrelatedTask {UnrelatedTask(event(int){},One,Two)}")
