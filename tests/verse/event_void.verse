# event() is an event without a value: E.Signal() and E.Await() (#156)
Door := class:
    Opened:event() = event(){}
    Name:string
Guard(D:Door, Tag:string)<suspends>:void =
    D.Opened.Await()
    Print("{Tag} sees {D.Name} open")
Main()<suspends>:void =
    D := Door{Name := "north"}
    A := spawn{Guard(D, "a")}
    B := spawn{Guard(D, "b")}
    Sleep(1.0)
    D.Opened.Signal()
    A.Await()
    B.Await()
    E:event() = event(){}
    race:
        E.Await()
        Sleep(0.5)
    Print("end")
