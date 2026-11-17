One()<computes>:int=1
Two()<computes>:int=2
Values(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:type{_()<computes>:int}=
    var Stored:type{_()<computes>:int}=Dummy
    for(I:=1..N):
        set Stored=Stored
        if(I=2):return Stored|Stored
    Stored|Stored
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:int=
    if(Saved:=Values(F,Dummy,N))then 1 else 0
Main()<transacts>:void={}
