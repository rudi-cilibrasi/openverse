# no suspends Main: a task runs only up to its first wait; F's first wait
# awaits a cancelled task, where it stays (the Book's API: a cancelled task
# never resumes its awaiters): the program ends with Main, F's defer not run
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
