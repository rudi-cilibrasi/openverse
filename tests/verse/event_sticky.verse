# sticky_event(t) latches its last signal: a later Await gives it at once (#156)
Waiter(Tag:string, E:sticky_event(int))<suspends>:void =
    Print("{Tag} got {E.Await()}")
Main()<suspends>:void =
    E := sticky_event(int){}
    A := spawn{Waiter("early", E)}
    Sleep(1.0)
    E.Signal(5)
    A.Await()
    B := spawn{Waiter("late", E)}
    B.Await()
    E.Signal(6)
    Print("now {E.Await()}")
    Ready:sticky_event() = sticky_event(){}
    Ready.Signal()
    Ready.Await()
    Plain:event(int) = sticky_event(int){}
    Plain.Signal(7)
    Print("end")
