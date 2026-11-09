# A (resumed by the scheduler) starts a branch whose first run cancels A,
# which is running. Expected: A at its next wait: branch cancelled A /
# A after branch / A defer / branch defer / end
A(Me:event(task(int)))<suspends>:int =
    defer:
        Print("A defer")
    T := Me.Await()
    branch:
        defer:
            Print("branch defer")
        T.Cancel()
        Print("branch cancelled A")
        Sleep(0.5)
        Print("branch end")
    Print("A after branch")
    Sleep(1.0)
    Print("never")
    1
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{A(Me)}
    Me.Signal(S)
    Sleep(2.0)
    Print("end")
