# the same in generic functions, twice (#253)
W(X:t where t:type)<suspends>:t =
    Sleep(9.0)
    X
F(X:t where t:type)<suspends>:t =
    defer:
        Print("F defer")
    T := spawn{W(X)}
    T.Cancel()
    T.Await()
Main()<suspends>:void =
    defer:
        Print("Main defer")
    spawn{F(1)}
    spawn{F("s")}
    Sleep(0.1)
    Print("main goes on")
