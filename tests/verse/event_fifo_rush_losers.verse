# Awaiters run inside Signal (#513): two arms that go on after the rush, one
# waiting when it ends, the other later: each goes on inside the Signal that
# reaches it, in the order its wait began
Waiter(E:event(int))<suspends>:void =
    V := E.Await()
    Print("task {V}")
Main()<suspends>:void =
    E := event(int){}
    rush:
        block:
            V := E.Await()
            Print("first loser {V}")
        block:
            spawn{Waiter(E)}
            Sleep(0.01)
            Print("winner")
        block:
            Sleep(0.01)
            Sleep(0.01)
            V := E.Await()
            Print("second loser {V}")
    E.Signal(1)
    Print("signalled")
    Sleep(0.01)
    Sleep(0.01)
    E.Signal(2)
    Sleep(0.1)
    Print("done")
