# a rush loser cancels the task whose function holds the rush: as a branch
# does, it goes on until it waits next, and the task is cancelled then (#260)
A(Me:event(task(int)))<suspends>:int =
    defer:
        Print("A defer")
    T := Me.Await()
    X := rush:
        block:
            defer:
                Print("loser defer")
            Sleep(0.2)
            T.Cancel()
            Print("after cancel")
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
