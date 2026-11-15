One()<computes>:int=1
Two()<computes>:int=2
Pick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two
holder:=class{var E:event(int)}
Early(H:holder,E:event(int),C:logic)<transacts>:int=
    if(C?):
        set H.E=E
        return 0
    0
Loop(H:holder,E:event(int),C:logic)<transacts>:int=
    loop:
        if(C?):
            set H.E=E
            return 0
        else:
            break
    0
Receiver(H:holder,E:event(int),C:logic)<transacts>:holder=
    if(C?):
        set H.E=E
        return H
    H
Both(H:holder,E:event(int),C:logic)<transacts>:int=
    if(C?):
        set H.E=E
        return 0
    else:
        return 0
Condition(H:holder,E:event(int),C:logic)<transacts>:int=
    if(set H.E=E;C?):
        return 0
    0
Inner(H:holder,E:event(int),C:logic)<transacts>:int=
    if(C?):
        set H.E=E
        return 0
    0
Nested(H:holder,E:event(int),C:logic)<transacts>:int=Inner(H,E,C)
Make(C:logic)<transacts>:holder=
    if(C?):
        return holder{E:=event(int){}}
    holder{E:=event(int){}}
EarlyWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    N:=Early(H,E,true)
    H.E.Signal(0)
    Stored()
LoopWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    N:=Loop(H,E,true)
    H.E.Signal(0)
    Stored()
ReceiverWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    N:=Receiver(H,E,true)
    N.E.Signal(0)
    Stored()
BothWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    N:=Both(H,E,true)
    H.E.Signal(0)
    Stored()
ConditionWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    N:=Condition(H,E,true)
    H.E.Signal(0)
    Stored()
NestedWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    N:=Nested(H,E,true)
    H.E.Signal(0)
    Stored()
Unrelated(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    N:=Early(H,Other,true)
    H.E.Signal(0)
    Stored()
Rollback(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    if(N:=Early(H,E,true);false?){}
    H.E.Signal(0)
    Stored()
FreshReturned(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    N:=Make(true)
    N.E.Signal(0)
    Stored()
Main()<suspends>:void=
    Print("EarlyWrite {EarlyWrite(event(int){},One,Two)}")
    Print("LoopWrite {LoopWrite(event(int){},One,Two)}")
    Print("ReceiverWrite {ReceiverWrite(event(int){},One,Two)}")
    Print("BothWrite {BothWrite(event(int){},One,Two)}")
    Print("ConditionWrite {ConditionWrite(event(int){},One,Two)}")
    Print("NestedWrite {NestedWrite(event(int){},One,Two)}")
    Print("Unrelated {Unrelated(event(int){},One,Two)}")
    Print("Rollback {Rollback(event(int){},One,Two)}")
    Print("FreshReturned {FreshReturned(event(int){},One,Two)}")
