One()<computes>:int=1
Two()<computes>:int=2
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:int=
    var Stored:type{_()<computes>:int}=F
    var Other:type{_()<computes>:int}=F
    for(I:=1..N):
        set Stored=Dummy
        set Other=F
        if(I=2):return Other()|Other()
    Other()|Other()
Main()<transacts>:void=for(V:=Caller(One,Two,3)){Print("value {V}")}
