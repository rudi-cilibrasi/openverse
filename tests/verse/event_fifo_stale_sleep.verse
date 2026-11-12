# FIFO (#513): a cancelled wait's record does not run its task
Sleeper(Tag:string, Delay:float)<suspends>:void =
    Sleep(Delay)
    Print("{Tag} woke from sleep")
Twice(E:event(int))<suspends>:void =
    race:
        block:
            V := E.Await()
            Print("got T (race) {V}")
        Sleep(0.1)
    Print("T race lost the wait")
    Sleep(0.4)
    Print("T woke from sleep")
Main()<suspends>:void =
    E := event(int){}
    X := spawn{Waiter(E)}
    R := spawn{Sleeper("R", 0.5)}
    T := spawn{Twice(E)}
    Sleep(0.5)
    Print("signal")
    E.Signal(1)
    R.Await()
    T.Await()
    X.Await()
Waiter(E:event(int))<suspends>:void =
    V := E.Await()
    Print("got X {V}")
