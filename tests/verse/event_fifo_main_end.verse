# FIFO (#513): Main goes on first and ends, which ends the program
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
