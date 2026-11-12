# (#513) --event-fifo: a rush arm that goes on after the rush (a task of its
# own then) began to wait before the spawned task; signalled before its
# first turn as a task, it still goes on first
Waiter(E:event(int))<suspends>:void =
    V := E.Await()
    Print("task {V}")
Main()<suspends>:void =
    E := event(int){}
    rush:
        block:
            V := E.Await()
            Print("loser {V}")
        block:
            spawn{Waiter(E)}
            Sleep(0.0)
            Print("winner")
    E.Signal(1)
    Print("signalled")
    Sleep(0.1)
    Print("done")
