One()<computes>:int=1
Two()<computes>:int=2

Direct()<suspends>:int=
    E:=event(int){}
    var Stored:type{_()<computes>:int}=Two
    branch:
        E.Await()
        set Stored=Two
    set Stored=One
    E.Signal(0)
    Stored()

Unrelated()<suspends>:int=
    E:=event(int){}
    Other:=event(int){}
    var Stored:type{_()<computes>:int}=Two
    branch:
        E.Await()
        set Stored=Two
    set Stored=One
    Alias:=Other
    Alias.Signal(0)
    Stored()

Timer()<suspends>:int=
    E:=event(int){}
    var Stored:type{_()<computes>:int}=Two
    branch:
        Sleep(0.1)
        set Stored=Two
    set Stored=One
    E.Signal(0)
    Stored()

Rollback(Again:logic)<suspends>:int=
    E:=event(int){}
    var Stored:type{_()<computes>:int}=Two
    branch:
        E.Await()
        set Stored=Two
    set Stored=One
    if(E.Signal(0);false?){}
    if(Again?)then E.Signal(0)
    Stored()

Wait(E:event(int))<suspends>:void=
    Sleep(0.1)
    E.Await()

HelperTimer()<suspends>:int=
    E:=event(int){}
    var Stored:type{_()<computes>:int}=Two
    branch:
        Wait(E)
        set Stored=Two
    set Stored=One
    E.Signal(0)
    Stored()

Completed()<suspends>:int=
    E:=event(int){}
    var Stored:type{_()<computes>:int}=Two
    branch:
        E.Await()
        set Stored=Two
    E.Signal(0)
    set Stored=One
    E.Signal(0)
    Stored()

Ordered()<suspends>:int=
    E:=event(int){}
    var Stored:type{_()<computes>:int}=Two
    branch:
        E.Await()
        set Stored=One
    branch:
        E.Await()
        Print("ordered read {Stored()}")
    E.Signal(0)
    Stored()

OwnerCleanup(ListenerFirst:logic)<suspends>:void=
    E:=event(int){}
    var Stored:type{_()<computes>:int}=Two
    if(ListenerFirst?)then:
        branch:
            E.Await()
            Print("owner cleanup {Stored()}")
        branch:
            defer:
                E.Signal(0)
            loop{Sleep(1.0)}
    else:
        branch:
            defer:
                E.Signal(0)
            loop{Sleep(1.0)}
        branch:
            E.Await()
            Print("unexpected canceled listener")

Main()<suspends>:void=
    Print("direct {Direct()}")
    Print("unrelated {Unrelated()}")
    Print("timer {Timer()}")
    Print("rollback {Rollback(false)}")
    Print("resignal {Rollback(true)}")
    Print("helper timer {HelperTimer()}")
    Print("completed {Completed()}")
    Print("ordered {Ordered()}")
    OwnerCleanup(true)
    OwnerCleanup(false)
