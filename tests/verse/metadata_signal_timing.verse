One()<computes>:int=1
Two()<computes>:int=2
holder:=class{E:event(int)}

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
    Box:=holder{E:=Other}
    Box.E.Signal(0)
    Aliases:=array{Other}
    if(Target:=Aliases[0])then Target.Signal(0)
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

HandshakeWorker(E:sticky_event(task(int)))<suspends>:int=
    Me:=E.Await()
    7

TaskCompletion()<suspends>:int=
    E:=sticky_event(task(int)){}
    T:=spawn{HandshakeWorker(E)}
    var Stored:type{_()<computes>:int}=Two
    branch:
        T.Await()
        set Stored=Two
    set Stored=One
    E.Signal(T)
    Stored()

EventWorker(E:event(int))<suspends>:int=E.Await()

CanceledWorker()<suspends>:int=
    E:=event(int){}
    T:=spawn{EventWorker(E)}
    var Stored:type{_()<computes>:int}=Two
    branch:
        T.Await()
        set Stored=Two
    set Stored=One
    T.Cancel()
    E.Signal(0)
    Stored()

ArmReturn(V:v,R:v where v:type)<suspends>:v=
    defer:
        Print("helper owner cleanup")
    Value:=race:
        block:
            defer:
                Print("helper arm cleanup")
            Sleep(0.1)
            return V
        block:
            defer:
                Print("helper loser cleanup")
            Sleep(1.0)
            R
    R

LateArmReturn(V:v,R:v where v:type)<suspends>:v=
    Release:=event(int){}
    Value:=rush:
        block:
            defer:
                Print("late arm cleanup")
            Release.Await()
            return V
        block:
            Sleep(0.0)
            R
    Release.Signal(0)
    R

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
    Print("task completion {TaskCompletion()}")
    Print("canceled worker {CanceledWorker()}")
    Saved:=ArmReturn(Two,One)
    Print("helper return {Saved()}")
    Later:=LateArmReturn(Two,One)
    Print("late helper return {Later()}")
