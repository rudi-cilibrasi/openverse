One()<computes>:int=1
Two()<computes>:int=2
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:type{_()<computes>:int}=
    var Stored:type{_()<computes>:int}=F
    for(I:=1..N):
        set Stored=Stored
        if(I=2):return block{set Stored=Dummy;F}|Stored
    block{set Stored=Dummy;F}|Stored
Main()<transacts>:void=for(V:=Caller(One,Two,3)){Print("value {V()}")}
