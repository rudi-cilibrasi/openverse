# #261: a task is marked cancelled and done before it unwinds. A defer of
# the task being cancelled starts (through an immediate function) a task
# whose first run awaits it: that one now sees a cancelled task at once,
# and is cancelled in its first run, in the middle of the unwinding; before
# #261 it waited, and was cancelled at the scheduler's next pass.
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
