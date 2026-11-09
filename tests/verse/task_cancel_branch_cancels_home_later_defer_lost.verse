# as task_cancel_branch_cancels_home_later, and the branch then calls H,
# which has a defer and waits: every defer entered runs once (#260)
H()<suspends>:void =
    defer:
        Print("H defer")
    Print("H runs")
    Sleep(0.2)
    Print("H end")
A(Me:event(task(int)))<suspends>:int =
    defer:
        Print("A defer")
    T := Me.Await()
    branch:
        defer:
            Print("branch defer")
        Sleep(0.2)
        T.Cancel()
        Print("after cancel")
        H()
        Print("branch end")
    Sleep(1.0)
    Print("never")
    1
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{A(Me)}
    Me.Signal(S)
    Sleep(2.0)
    Print("end")
