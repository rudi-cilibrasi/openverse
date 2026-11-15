One()<computes>:int=1
Two()<computes>:int=2
Pick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two
holder:=class<unique>{var E:event(int)}
Same(X:t where t:subtype(comparable))<transacts><decides>:t=X=X
SendEq(A:holder,B:holder,N:int):void=
    if(N>0)then SendEq(B,A,N-1)else:
        if(Alias:=A=A)then Alias.E.Signal(0)
SendNe(A:holder,B:holder,N:int):void=
    if(N>0)then SendNe(B,A,N-1)else:
        if(Alias:=A<>B)then Alias.E.Signal(0)
SendLeft(A:holder,B:holder,N:int):void=
    if(N>0)then SendLeft(A,B,N-1)else:
        if(Alias:=A<>B)then Alias.E.Signal(0)
EqWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    if(Alias:=H=H)then set Alias.E=E
    H.E.Signal(0)
    Stored()
NeWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    if(Alias:=H<>K)then set Alias.E=E
    H.E.Signal(0)
    Stored()
ArrayWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    if(Aliases:=array{H}=array{H},Alias:=Aliases[0])then set Alias.E=E
    H.E.Signal(0)
    Stored()
TupleWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    if(Pair:=(H,0)=(H,0),Alias:=Pair(0))then set Alias.E=E
    H.E.Signal(0)
    Stored()
GenericWrite(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    if(Alias:=Same[H])then set Alias.E=E
    H.E.Signal(0)
    Stored()
ReadUnrelated(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    if(Alias:=H=H)then Alias.E.Signal(0)
    H.E.Signal(0)
    Stored()
LeftOnly(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    if(Alias:=H<>K)then set Alias.E=Other
    H.E.Signal(0)
    Stored()
OtherObject(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    if(Alias:=K=K)then set Alias.E=E
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
    K:=holder{E:=E}
    if(Alias:=H=H;set Alias.E=E;false?)then {}
    H.E.Signal(0)
    Stored()
RecursiveEq(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    SendEq(H,K,1)
    Stored()
RecursiveNe(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    SendNe(H,K,1)
    Stored()
RecursiveLeft(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=E}
    SendLeft(H,K,1)
    Stored()
Main()<suspends>:void=
    Print("EqWrite {EqWrite(event(int){},One,Two)}")
    Print("NeWrite {NeWrite(event(int){},One,Two)}")
    Print("ArrayWrite {ArrayWrite(event(int){},One,Two)}")
    Print("TupleWrite {TupleWrite(event(int){},One,Two)}")
    Print("GenericWrite {GenericWrite(event(int){},One,Two)}")
    Print("ReadUnrelated {ReadUnrelated(event(int){},One,Two)}")
    Print("LeftOnly {LeftOnly(event(int){},One,Two)}")
    Print("OtherObject {OtherObject(event(int){},One,Two)}")
    Print("Rollback {Rollback(event(int){},One,Two)}")
    Print("RecursiveEq {RecursiveEq(event(int){},One,Two)}")
    Print("RecursiveNe {RecursiveNe(event(int){},One,Two)}")
    Print("RecursiveLeft {RecursiveLeft(event(int){},One,Two)}")
