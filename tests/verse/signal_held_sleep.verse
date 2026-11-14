# Inside a Signal only an awaiter's turn goes on: the sleeping arm of the
# woken task, due at the same tick, waits for its task's turn in the
# scheduler's pass (the Book's API, Sleep: the timer resumes a sleep, not
# the Signal)
Root(E:event(int))<suspends>:void =
    sync:
        block:
            Sleep(1.0)
            Print("sleeper wakes")
        block:
            V := E.Await()
            Print("awaiter got {V}")
    Print("root ends")
Main()<suspends>:void =
    E := event(int){}
    spawn{Root(E)}
    Sleep(1.0)
    Print("main signals")
    E.Signal(1)
    Print("main after signal")
    Sleep(1.0)
