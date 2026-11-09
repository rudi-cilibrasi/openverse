# a branch that awaits a cancelled task in its first run is cancelled, and
# its function goes on (#253)
W()<suspends>:int =
    Sleep(9.0)
    1
G(X:t where t:type)<suspends>:t =
    defer:
        Print("G defer")
    T := spawn{W()}
    T.Cancel()
    branch:
        defer:
            Print("branch defer")
        T.Await()
        Print("never")
    Sleep(0.5)
    Print("G end")
    X
Main()<suspends>:void =
    Print("{G(7)}")
    Print("main end")
