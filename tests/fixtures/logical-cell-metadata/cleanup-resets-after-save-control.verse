One()<computes>:int=1
Two()<computes>:int=2
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:type{_()<computes>:int}=
    var Stored:type{_()<computes>:int}=Dummy
    defer:set Stored=F
    if(N>=1):
        set Stored=Stored
    if(N>=2):
        set Stored=Stored
        return Stored|Stored
    Stored|Stored
Main()<transacts>:void=for(V:=Caller(One,Two,3)){Print("value {V()}")}
