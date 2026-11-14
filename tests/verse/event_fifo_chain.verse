# Awaiters run inside Signal (the Book's API, event's Signal; #513): a
# chain. A (spawned first, waiting last) is resumed after B and signals F,
# where C has waited since the start: C goes on inside A's Signal, before A
# goes on, and all of it before the first Signal returns
W(Tag:string, E:event(int))<suspends>:void =
    V := E.Await()
    Print("{Tag} got {V}")
Relay(E:event(int), F:event(int))<suspends>:void =
    Sleep(0.05)
    V := E.Await()
    Print("A got {V}")
    F.Signal(V + 10)
    Print("A relayed")
Main()<suspends>:void =
    E := event(int){}
    F := event(int){}
    A := spawn{Relay(E, F)}
    C := spawn{W("C", F)}
    B := spawn{W("B", E)}
    Sleep(0.1)
    E.Signal(1)
    Print("signalled")
    A.Await()
    B.Await()
    C.Await()
    Print("end")
