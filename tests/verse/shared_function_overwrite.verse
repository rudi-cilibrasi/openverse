One()<computes>:int=1
Two()<computes>:int=2

Caller(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=G
    set Stored=F
    Values:=sync:
        block:
            Sleep(0.2)
            Stored()
        block:
            Sleep(0.1)
            set Stored=G
    Values(0)

Main()<suspends>:void=Print("{Caller(One,Two)}")
