# Awaiters run inside Signal (#513): a cancelled wait's record is no waiter
Waiter(E:event(int), Tag:string, Delay:float)<suspends>:void =
    Sleep(Delay)
    V := E.Await()
    Print("got {Tag} {V}")
Timeout(E:event(int))<suspends>:void =
    Sleep(0.1)
    race:
        E.Await()
        Sleep(0.1)
    Sleep(0.2)
    V := E.Await()
    Print("got T {V}")
Main()<suspends>:void =
    E := event(int){}
    X := spawn{Waiter(E, "X", 0.0)}
    T := spawn{Timeout(E)}
    Y := spawn{Waiter(E, "Y", 0.3)}
    Sleep(0.5)
    E.Signal(1)
    X.Await()
    Y.Await()
    T.Await()
