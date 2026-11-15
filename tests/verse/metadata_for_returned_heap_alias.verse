One()<computes>:int=1
Two()<computes>:int=2
Pick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two
holder:=class{var E:event(int)}
Change(H:holder,E:event(int),C:logic)<transacts>:int=
    Values:=for(I:=0..0):
        set H.E=E
        return 0
    0
Caller(E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    N:=Change(H,E,true)
    H.E.Signal(N)
    Stored()
Main()<suspends>:void=
    Print("ForWrite {Caller(event(int){},One,Two)}")
