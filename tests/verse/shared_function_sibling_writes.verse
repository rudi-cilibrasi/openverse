One()<computes>:int=1
Two()<computes>:int=2

Sync(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=G
    Values:=sync:
        block:
            Sleep(0.1)
            set Stored=G
            Sleep(0.5)
            0
        block:
            set Stored=F
            Sleep(0.5)
            0
        block:
            Sleep(0.2)
            Stored()
    Values(2)

Race(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=G
    race:
        block:
            Sleep(0.1)
            set Stored=G
            Sleep(0.5)
            0
        block:
            set Stored=F
            Sleep(0.5)
            0
        block:
            Sleep(0.2)
            Stored()

Rush(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=G
    rush:
        block:
            Sleep(0.1)
            set Stored=G
            Sleep(0.5)
            0
        block:
            set Stored=F
            Sleep(0.5)
            0
        block:
            Sleep(0.2)
            Stored()

Main()<suspends>:void=
    Print("sync {Sync(One,Two)}")
    Print("race {Race(One,Two)}")
    Print("rush {Rush(One,Two)}")
