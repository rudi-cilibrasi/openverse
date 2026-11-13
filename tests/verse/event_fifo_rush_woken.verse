# (#513) --event-fifo: the winning arm signals before it ends, while the
# other arm is still the function's: once the rush ends, that arm, a task of
# its own, goes on first, as it began to wait first
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
            Sleep(0.01)
            E.Signal(2)
            Print("winner")
    Print("after rush")
    Sleep(0.1)
    Print("done")
