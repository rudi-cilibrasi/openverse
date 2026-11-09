A(Me:event(task(int)))<suspends>:int =
    defer:
        Print("A defer")
    T := Me.Await()
    branch:
        defer:
            Print("B1 defer")
        Sleep(0.2)
        branch:
            defer:
                Print("B2 defer")
            T.Cancel()
            Print("B2 goes on")
            Sleep(0.1)
            Print("B2 never")
        Print("B1 goes on")
        Sleep(0.1)
        Print("B1 never")
    Sleep(1.0)
    Print("never")
    1
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{A(Me)}
    Me.Signal(S)
    Sleep(2.0)
    Print("end")
