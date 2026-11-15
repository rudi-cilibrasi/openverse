One()<computes>:int=1
Two()<computes>:int=2

BranchLate(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=G
    branch:
        Sleep(0.1)
        set Stored=G
    set Stored=F
    Sleep(0.2)
    Stored()

RushLate(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=G
    Value:=rush:
        block:
            Sleep(0.1)
            set Stored=G
            Sleep(1.0)
            0
        block:
            Sleep(0.05)
            0
    set Stored=F
    Sleep(0.2)
    Stored()

BranchEarly(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=G
    branch:
        Sleep(0.2)
        set Stored=F
    Sleep(0.1)
    Stored()

BranchCanceled(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=G
    branch:
        Sleep(0.1)
        set Stored=G
        Print("uncanceled branch")
    set Stored=F
    Stored()

RushCanceled(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=G
    Value:=rush:
        block:
            Sleep(0.1)
            set Stored=G
            Print("uncanceled rush")
            Sleep(1.0)
            0
        block:
            Sleep(0.05)
            0
    set Stored=F
    Stored()

Cleanup(G:type{_()<computes>:int})<suspends>:void=
    var Stored:type{_()<computes>:int}=G
    Value:=race:
        block:
            defer:
                Print("cleanup {Stored()}")
            loop{Sleep(1.0)}
        block:
            Sleep(0.1)
            0

AliasCleanup(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:void=
    var Stored:type{_()<computes>:int}=G
    Saved:=Stored
    Value:=race:
        block:
            defer:
                Print("alias {Saved()}")
            set Stored=F
            loop{Sleep(1.0)}
        block:
            Sleep(0.1)
            0

Main()<suspends>:void=
    Print("branch late {BranchLate(One,Two)}")
    Print("rush late {RushLate(One,Two)}")
    Print("branch early {BranchEarly(One,Two)}")
    Print("branch canceled {BranchCanceled(One,Two)}")
    Print("rush canceled {RushCanceled(One,Two)}")
    Cleanup(Two)
    AliasCleanup(One,Two)
