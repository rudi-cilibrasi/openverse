One()<computes>:int=1
Two()<computes>:int=2
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:int=
    var Stored:tuple(type{_()<computes>:int},type{_()<computes>:int})=(F,F)
    set Stored=(Dummy,F)
    if(N>=1):
        set Stored=Stored
    if(N>=2):
        set Stored=Stored
        return Stored(1)()|Stored(1)()
    Stored(1)()|Stored(1)()
Main()<transacts>:void=for(V:=Caller(One,Two,3)){Print("value {V}")}
