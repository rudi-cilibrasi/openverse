# (#513) --event-fifo: a rush in a spawned task; its losing arm, a task of its
# own, began to wait before another task and goes on first when a third
# task signals
Waiter(E:event(int))<suspends>:void =
    V := E.Await()
    Print("task {V}")
Racer(E:event(int))<suspends>:void =
    rush:
        block:
            V := E.Await()
            Print("loser {V}")
        block:
            Sleep(0.0)
            Print("winner")
    Print("racer after")
    Sleep(0.0)
    Print("racer done")
Signaller(E:event(int))<suspends>:void =
    Sleep(0.0)
    E.Signal(1)
    Print("signalled")
Main()<suspends>:void =
    E := event(int){}
    spawn{Racer(E)}
    spawn{Waiter(E)}
    spawn{Signaller(E)}
    Sleep(0.1)
    Print("done")
