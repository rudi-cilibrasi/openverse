# (#260, #261) as branch_cancels_home_later, and after Cancel()
# the branch calls H, which has a defer and waits. The branch was already
# unwound (its defer ran) and is stopped at H's wait: H's defer never runs.
# Expected: every defer that was entered runs once (H defer included).
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
