One()<computes>:int=1
Two()<computes>:int=2
Pick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two
Count(N:int)<computes>:int=if(N>0)then Count(N-1)else 0
holder:=class{var E:event(int)}
Change(H:holder,E:event(int),N:int)<transacts>:int=if(N>0)then Change(H,E,N-1)else block{set H.E=E;0}
Select(A:event(int),B:event(int),N:int)<computes>:event(int)=if(N>0)then Select(B,A,N-1)else A
ReadOnly(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    Alias:=holder{E:=Other}
    N:=Count(1)
    Alias.E.Signal(N)
    Stored()
Writing(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    Alias:=holder{E:=Other}
    N:=Change(Alias,E,1)
    Alias.E.Signal(N)
    Stored()
Returning(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    Alias:=holder{E:=Select(Other,E,1)}
    N:=Count(1)
    Alias.E.Signal(N)
    Stored()
Main()<suspends>:void=
    Print("readonly {ReadOnly(event(int){},One,Two)}")
    Print("writable {Writing(event(int){},One,Two)}")
    Print("returned {Returning(event(int){},One,Two)}")
