# a defer calls an immediate function that spawns a task whose first run
# cancels the task being unwound (not running, not yet done). Expected:
# V defer once, killer done, end.
Killer(T:task(int))<suspends>:void =
    T.Cancel()
    Print("killer done")
StartKiller(T:task(int)):void =
    spawn{Killer(T)}
V(Me:event(task(int)))<suspends>:int =
    T := Me.Await()
    defer:
        Print("V defer")
        StartKiller(T)
    Sleep(5.0)
    1
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{V(Me)}
    Me.Signal(S)
    Sleep(0.5)
    S.Cancel()
    Sleep(0.5)
    Print("end")
