One()<computes>:int=1
Two()<computes>:int=2
Values(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:type{_()<computes>:int}=
    var Stored:type{_()<computes>:int}=Dummy
    if(N>=1):set Stored=Stored
    if(N>=2):
        set Stored=Stored
        return Stored|Stored
    Stored|Stored
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:int=
    if(Saved:=Values(F,Dummy,N))then 1 else 0
Main()<transacts>:void={}
