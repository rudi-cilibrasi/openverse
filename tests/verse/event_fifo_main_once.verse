# FIFO (#513): Main, woken by a task's Signal, ends once
Sig(E:event(int))<suspends>:void =
    Sleep(0.01)
    E.Signal(7)
Main()<suspends>:void =
    E := event(int){}
    S := spawn{Sig(E)}
    V := E.Await()
    Print("got Main {V}; Main ends")
