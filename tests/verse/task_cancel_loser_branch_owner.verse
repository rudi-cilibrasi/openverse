A(Me:event(task(int)))<suspends>:int =
    defer:
        Print("A defer")
    T := Me.Await()
    X := rush:
        block:
            defer:
                Print("loser defer")
            Sleep(0.2)
            branch:
                defer:
                    Print("B defer")
                T.Cancel()
                Print("B goes on")
                Sleep(0.1)
                Print("B never")
            Print("loser goes on")
            Sleep(0.2)
            0
        block:
            Sleep(0.05)
            5
    Print("A got {X}")
    Sleep(1.0)
    Print("never")
    1
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{A(Me)}
    Me.Signal(S)
    Sleep(2.0)
    Print("end")
