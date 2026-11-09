# A task cancels itself, then starts a branch before its next wait.
# Expected: the branch's first run prints "branch runs", then the task
# reaches its wait and is cancelled: "selfstop defer" and the branch's
# "branch defer" (cancelled when its function exits), then "end".
SelfStop(Me:event(task(int)))<suspends>:int =
    defer:
        Print("selfstop defer")
    T := Me.Await()
    T.Cancel()
    branch:
        defer:
            Print("branch defer")
        Print("branch runs")
        Sleep(0.5)
        Print("branch end")
    Print("still running until it waits")
    Sleep(1.0)
    Print("never")
    1
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{SelfStop(Me)}
    Me.Signal(S)
    Sleep(2.0)
    Print("end")
