# Awaiters run inside Signal (#513): one Signal wakes B and both arms of T's
# race, B first (it waited first). r1, the earlier arm, wins at its turn;
# r2, woken but not yet resumed, is cancelled with the race and does not go
# on; all of it before the Signal returns
W(Tag:string, E:event(int))<suspends>:void =
    V := E.Await()
    Print("{Tag} got {V}")
Racer(E:event(int))<suspends>:void =
    Sleep(0.05)
    race:
        block:
            V := E.Await()
            Print("r1 got {V}")
        block:
            V := E.Await()
            Print("r2 got {V}")
    Print("T after race")
Main()<suspends>:void =
    E := event(int){}
    T := spawn{Racer(E)}
    B := spawn{W("B", E)}
    Sleep(0.1)
    E.Signal(7)
    Print("signalled")
    T.Await()
    B.Await()
    Print("end")
