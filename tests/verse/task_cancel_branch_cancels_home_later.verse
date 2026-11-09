# a branch, resumed by the scheduler, cancels the task whose function started
# it: the task is running while the branch runs, so it is cancelled when the
# branch waits next, and the branch goes on until then (#260)
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
        Sleep(0.2)
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
