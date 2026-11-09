Idle()<suspends>:void =
    defer:
        Print("U defer")
    Sleep(0.5)
    Print("U end")
A(Me:event(task(int)))<suspends>:int =
    defer:
        Print("A defer")
    T := Me.Await()
    branch:
        defer:
            Print("B defer")
        Sleep(0.2)
        spawn{Idle()}
        branch:
            defer:
                Print("B3 defer")
            T.Cancel()
            Print("B3 goes on")
            Sleep(0.1)
            Print("B3 never")
        Print("B goes on")
        Sleep(0.1)
        Print("B never")
    Sleep(1.0)
    Print("never")
    1
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{A(Me)}
    Me.Signal(S)
    Sleep(2.0)
    Print("end")
