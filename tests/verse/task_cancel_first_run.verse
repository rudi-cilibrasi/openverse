# awaiting a cancelled task during a spawned task's first run cancels the
# spawned task, not the one being resumed (#253)
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
