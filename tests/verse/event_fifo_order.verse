# FIFO event resumption (#513, --event-fifo): the tasks a Signal wakes go on
# in the order they began to wait, not the scheduler's (Main, then spawn
# order): spawned tasks, Main itself and a branch
Waiter(E:event(int), Tag:string, Delay:float)<suspends>:void =
    Sleep(Delay)
    Print("wait {Tag}")
    V := E.Await()
    Print("got {Tag} {V}")
Signaller(E:event(int), Delay:float, V:int)<suspends>:void =
    Sleep(Delay)
    Print("signal {V}")
    E.Signal(V)
    Print("returned {V}")
Main()<suspends>:void =
    E := event(int){}
    A := spawn{Waiter(E, "A", 0.2)}
    B := spawn{Waiter(E, "B", 0.0)}
    S := spawn{Signaller(E, 0.4, 7)}
    branch:
        Sleep(0.1)
        Print("wait br")
        V := E.Await()
        Print("got br {V}")
    Sleep(0.3)
    Print("wait Main")
    V := E.Await()
    Print("got Main {V}")
    A.Await()
    B.Await()
    S.Await()
