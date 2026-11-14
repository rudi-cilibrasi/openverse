One()<computes>:int=1
Two()<computes>:int=2

Caller(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:void=
    var Count:int=0
    loop:
        var Stored:type{_()<computes>:int}=G
        set Stored=F
        Sleep(0.01)
        Print("loop {Stored()}")
        set Count+=1
        if(Count>=2)then break
    for(N:=0..1):
        var Stored:type{_()<computes>:int}=G
        set Stored=F
        Sleep(0.01)
        Print("for {Stored()}")

Main()<suspends>:void=Caller(One,Two)
