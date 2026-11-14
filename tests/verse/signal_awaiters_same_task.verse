# Awaiters run inside Signal, also an arm of the signalling task's own sync
# (the Book's tests, Event.versetest:21-32): the collecting arm receives
# each value inside the Signal that sends it, and ends inside the last one
Collect(E:event(int))<suspends>:void =
    for (I := 1..3):
        V := E.Await()
        Print("got {V}")
Send(E:event(int))<suspends>:void =
    for (I := 1..3):
        Print("send {I}")
        E.Signal(I)
        Print("sent {I}")
Main()<suspends>:void =
    E := event(int){}
    sync:
        Collect(E)
        Send(E)
    Print("both done")
