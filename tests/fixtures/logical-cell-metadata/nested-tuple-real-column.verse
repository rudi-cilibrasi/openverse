One()<computes>:int=1
Two()<computes>:int=2
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:int=
    var Stored:tuple(type{_()<computes>:int},tuple(type{_()<computes>:int},type{_()<computes>:int}))=(F,(F,F))
    set Stored=(Dummy,(F,Dummy))
    for(I:=1..N):
        set Stored=Stored
        if(I=2):return Stored(1)(0)()|Stored(1)(0)()
    Stored(1)(0)()|Stored(1)(0)()
Main()<transacts>:void=for(V:=Caller(One,Two,3)){Print("value {V}")}
