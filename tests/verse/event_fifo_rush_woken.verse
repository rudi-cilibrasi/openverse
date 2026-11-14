# Awaiters run inside Signal (the Book's ch. 14: "the first completer
# wins"; #513): the second arm signals while the first waits; the first is
# resumed inside that Signal and ends, then the spawned waiter has its turn;
# the second arm goes on to its end after the Signal; the first ended first,
# so it won the rush
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
