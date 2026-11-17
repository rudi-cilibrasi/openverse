One()<computes>:int=1
Two()<computes>:int=2
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:int=
    var Stored:type{_()<computes>:int}=F
    var Other:type{_()<computes>:int}=F
    if(N>=1):
        set Stored=Dummy
        set Other=F
    if(N>=2):
        set Stored=Dummy
        set Other=F
        return Stored()|Stored()
    Stored()|Stored()
Main()<transacts>:void=for(V:=Caller(One,Two,3)){Print("value {V}")}
