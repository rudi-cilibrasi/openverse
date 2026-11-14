# A task that ends inside a Signal (an awaiter of the event that ends)
# resumes its own awaiters there, depth first, before the Signal's round
# goes on; an awaiter that signals an event inside the end runs that
# event's round in its turn; the signaller sees all of it when Signal
# returns (the Book's API, task, Await, and event, Signal; Bugs/FORT-1088027
# …:6-9; Coroutines/SpawnAndTask.versetest:688-737). Main ends right after,
# with no tick passing.
Ender(E:event(int))<suspends>:int =
    X := E.Await()
    Print("ender got {X}")
    X + 1
Watcher(T:task(int), F:event(int))<suspends>:void =
    V := T.Await()
    Print("watcher got {V}")
    F.Signal(V * 10)
    Print("watcher signalled")
Listener(F:event(int))<suspends>:void =
    Print("listener got {F.Await()}")
Late(E:event(int))<suspends>:void =
    Print("late got {E.Await()}")
Main()<suspends>:void =
    E := event(int){}
    F := event(int){}
    T := spawn{Ender(E)}
    spawn{Listener(F)}
    spawn{Watcher(T, F)}
    spawn{Late(E)}
    E.Signal(1)
    Print("signal returned")
