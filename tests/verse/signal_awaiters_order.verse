# Awaiters run inside Signal (the Book's API, event's Signal: "resumed
# first, in the order they suspended ... Each resumed task runs until it
# blocks again before the next one is given a turn"): B waits first, then
# A, then C; each is resumed in that order and runs to its next wait, all
# before the Signal returns to Main
Waiter(Name:string, E:event(int), Pause:float)<suspends>:void =
    Sleep(Pause)
    Print("{Name} waits")
    V := E.Await()
    Print("{Name} got {V}")
    Sleep(1.0)
    Print("{Name} ends")
Main()<suspends>:void =
    E := event(int){}
    spawn{Waiter("A", E, 2.0)}
    spawn{Waiter("B", E, 1.0)}
    spawn{Waiter("C", E, 3.0)}
    Sleep(5.0)
    Print("main signals")
    E.Signal(7)
    Print("main after signal")
