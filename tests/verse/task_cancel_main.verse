# Main awaiting a cancelled task is cancelled: its defers run and the program ends (#156)
W()<suspends>:int =
    Sleep(10.0)
    1
Stopper(T:task(int))<suspends>:void =
    Sleep(1.0)
    T.Cancel()
Main()<suspends>:void =
    defer:
        Print("main unwound")
    T := spawn{W()}
    spawn{Stopper(T)}
    Print("got {T.Await()}")
    Print("never")
