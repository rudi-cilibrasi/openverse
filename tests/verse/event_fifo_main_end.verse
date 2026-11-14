# Awaiters run inside Signal (#513): Main's own arm is resumed inside its
# other arm's Signal, then the spawned waiter; Main ends after both
Waiter(E:event(int), Tag:string)<suspends>:void =
    V := E.Await()
    Print("got {Tag} {V}")
Main()<suspends>:void =
    E := event(int){}
    sync:
        block:
            V := E.Await()
            Print("got Main {V}")
        block:
            Sleep(0.1)
            B := spawn{Waiter(E, "B")}
            Sleep(0.1)
            E.Signal(1)
    Print("Main ends")
