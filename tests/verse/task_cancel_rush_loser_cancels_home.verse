# A rush loser (its own task after the rush) cancels the task whose function
# contains the rush; A is suspended, so it unwinds at once, and its exit
# cancels the loser that is running Cancel(). Expected as
# branch_cancels_home_later: A defer / loser defer / end
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
