# FIFO event resumption (#513, --event-fifo) for the other kinds of event:
# a sticky_event's waiters, and a subscribable_event's, whose subscribed
# functions run first, inside Signal; and waiters in the arms of one task's
# sync, which go on when their task does, at the turn of the first of them
# to have waited (arm2, before F), in the arms' order (arm1, then arm2)
Waiter(E:event(int), Tag:string, Delay:float)<suspends>:void =
    Sleep(Delay)
    V := E.Await()
    Print("got {Tag} {V}")
Note(V:int):void = Print("subscribed {V}")
SignalLater(E:event(int), Delay:float, V:int)<suspends>:void =
    Sleep(Delay)
    E.Signal(V)
Main()<suspends>:void =
    S := sticky_event(int){}
    A := spawn{Waiter(S, "sA", 0.1)}
    B := spawn{Waiter(S, "sB", 0.0)}
    Sleep(0.2)
    S.Signal(1)
    A.Await()
    B.Await()
    U := subscribable_event(int){}
    Sub := U.Subscribe(Note)
    C := spawn{Waiter(U, "uC", 0.1)}
    D := spawn{Waiter(U, "uD", 0.0)}
    Sleep(0.2)
    U.Signal(2)
    C.Await()
    D.Await()
    E := event(int){}
    F := spawn{Waiter(E, "F", 0.0)}
    G := spawn{SignalLater(E, 0.1, 3)}
    sync:
        block:
            Sleep(0.05)
            V := E.Await()
            Print("got arm1 {V}")
        block:
            V := E.Await()
            Print("got arm2 {V}")
    F.Await()
    G.Await()
