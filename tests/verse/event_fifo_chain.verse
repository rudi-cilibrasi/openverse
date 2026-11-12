# FIFO event resumption (#513, --event-fifo): a chain. A (spawned first, waiting last) is woken
# after B, and signals F, where C has waited since the start: C goes on after every task the
# first Signal woke. The default order runs A, then C, then B.
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
