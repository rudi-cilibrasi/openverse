Main()<suspends>:void=
    E:=sticky_event(int){}
    if(E.Signal(7),false?) then Print("bad")
    race:
        block:
            X:=E.Await()
            Print("bad {X}")
        block:
            Sleep(1.0)
            Print("empty")
