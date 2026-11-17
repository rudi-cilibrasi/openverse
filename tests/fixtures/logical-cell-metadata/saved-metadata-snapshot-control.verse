One()<computes>:int=1
Two()<computes>:int=2
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:int=
    var Stored:type{_()<computes>:int}=Dummy
    Saved:=Stored
    set Stored=F
    if(N>=1):
        set Stored=Stored
    if(N>=2):
        set Stored=Stored
        return Saved()|Saved()
    Saved()|Saved()
Main()<transacts>:void=for(V:=Caller(One,Two,3)){Print("value {V}")}
