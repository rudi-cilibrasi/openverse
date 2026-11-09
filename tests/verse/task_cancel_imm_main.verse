# no suspends Main: a task runs only up to its first wait; F's first wait
# awaits a cancelled task
W()<suspends>:int =
    Sleep(9.0)
    1
F()<suspends>:int =
    defer:
        Print("F defer")
    T := spawn{W()}
    T.Cancel()
    T.Await()
Main():void =
    spawn{F()}
    Print("main end")
