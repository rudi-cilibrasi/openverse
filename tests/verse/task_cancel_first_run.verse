# a spawned task's first run awaits a cancelled task, and waits there for
# ever (the Book's API, task, Await): no task is cancelled, the one that
# spawned it goes on (#253: before, the awaiting task was cancelled)
W()<suspends>:int =
    Sleep(9.0)
    1
F()<suspends>:int =
    defer:
        Print("F defer")
    T := spawn{W()}
    T.Cancel()
    T.Await()
Main()<suspends>:void =
    defer:
        Print("Main defer")
    spawn{F()}
    Sleep(0.1)
    Print("main goes on")
