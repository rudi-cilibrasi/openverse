One()<computes>:int=1
Two()<computes>:int=2
reader:=class<computes>{Read()<computes>:int=7}
Use(V:reader)<computes>:int=V.Read()

HelperCleanup(R:reader)<suspends>:void=
    Value:=race:
        block:
            defer:
                Print("helper cleanup {Use(R)}")
            loop{Sleep(1.0)}
        block:
            Sleep(0.1)
            0

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

SignalWrite(E:event(int),F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=G
    branch:
        E.Await()
        set Stored=G
    set Stored=F
    E.Signal(0)
    Stored()

NestedCleanup(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:void=
    var Stored:type{_()<computes>:int}=G
    defer:
        Print("nested cleanup {Stored()}")
    Values:=sync:
        block:
            defer:
                set Stored=F
            loop{Sleep(1.0)}
        block:
            loop{Sleep(1.0)}

BranchCleanupOrder(F:type{_()<computes>:int},G:type{_()<computes>:int})<suspends>:void=
    var Stored:type{_()<computes>:int}=G
    defer:
        Print("parent cleanup {Stored()}")
    branch:
        defer:
            set Stored=F
            Print("branch cleanup")
        loop{Sleep(1.0)}
    loop{Sleep(1.0)}

Main()<suspends>:void=
    Print("branch late {BranchLate(One,Two)}")
    Print("rush late {RushLate(One,Two)}")
    Print("branch early {BranchEarly(One,Two)}")
    Print("branch canceled {BranchCanceled(One,Two)}")
    Print("rush canceled {RushCanceled(One,Two)}")
    Cleanup(Two)
    AliasCleanup(One,Two)
    HelperCleanup(reader{})
    T:=spawn{NestedCleanup(One,Two)}
    Sleep(0.1)
    T.Cancel()
    B:=spawn{BranchCleanupOrder(One,Two)}
    Sleep(0.1)
    B.Cancel()
    E:=event(int){}
    Print("signal {SignalWrite(E,One,Two)}")
