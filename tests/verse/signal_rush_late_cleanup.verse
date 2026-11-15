One()<computes>:int=1
Two()<computes>:int=2
Pick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two
LateRead(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    E:=event(int){}
    branch:
        R:=rush:
            block:
                Sleep(0.1)
                E.Signal(1)
                defer:
                    Print("late read {Stored()}")
                Sleep(1.0)
                1
            block:
                Sleep(1.0)
                1
    E.Await()
    0
LateWrite(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    E:=event(int){}
    branch:
        R:=rush:
            block:
                Sleep(0.1)
                E.Signal(1)
                defer:
                    Print("late write before {Stored()}")
                    set Stored=Dummy
                    Print("late write after {Stored()}")
                Sleep(1.0)
                1
            block:
                Sleep(1.0)
                1
    set Stored=F
    E.Await()
    0
AfterWait(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    E:=event(int){}
    branch:
        R:=rush:
            block:
                Sleep(0.1)
                E.Signal(1)
                Sleep(1.0)
                defer:
                    Print("unreachable cleanup {Stored()}")
                Sleep(1.0)
                1
            block:
                Sleep(1.0)
                1
    E.Await()
    0
Main()<suspends>:void=
    Print("LateRead owner returned {LateRead(One,Two)}")
    Sleep(2.0)
    Print("LateWrite owner returned {LateWrite(One,Two)}")
    Sleep(2.0)
    Print("AfterWait owner returned {AfterWait(One,Two)}")
    Sleep(2.0)
    Print("main done")
