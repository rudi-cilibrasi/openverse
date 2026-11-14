# A task that ends inside a Signal made in a failure context that fails:
# its end and what its awaiter did are undone with the context (output
# included), the task and the awaiter back where they waited, as a Signal's
# awaiters are (Coroutines/Concurrency.versetest:1562-1580); the next
# Signal resumes them for real.
Ender(E:event(int))<suspends>:int =
    X := E.Await()
    Print("ender got {X}")
    X
Watcher(T:task(int))<suspends>:void =
    Print("watcher got {T.Await()}")
Main()<suspends>:void =
    E := event(int){}
    T := spawn{Ender(E)}
    spawn{Watcher(T)}
    if:
        E.Signal(1)
        false?
    Print("rolled back")
    E.Signal(2)
    Print("end")
