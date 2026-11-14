# An await of a task while it is being cancelled: a defer of the task being
# cancelled starts (through an immediate function) a task whose first run
# awaits it. A task cancelling, as one cancelled, never resumes its
# awaiters (the Book's API, task, Await: "Every other phase suspends"): the
# awaiter waits for ever, and the unwinding goes on (#261: before, the
# awaiter was cancelled in its first run).
Waiter(T:task(int))<suspends>:void =
    defer:
        Print("waiter defer")
    Print("waiter got {T.Await()}")
StartWaiter(T:task(int)):void =
    spawn{Waiter(T)}
V(Me:event(task(int)))<suspends>:int =
    T := Me.Await()
    defer:
        Print("V outer defer")
    defer:
        Print("V inner defer")
        StartWaiter(T)
    Sleep(5.0)
    1
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{V(Me)}
    Me.Signal(S)
    Sleep(0.5)
    S.Cancel()
    Print("main cancelled V")
    Sleep(0.5)
    Print("end")
