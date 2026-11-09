# (#260, #261) A starts a branch that, resumed later by the
# scheduler (A is waiting, so not "running"), cancels A. A unwinds at once,
# and its exit cancels its branches, among them the branch that is running
# Cancel(): its defer runs, and then it goes on running ("after cancel")
# until its next wait. Expected: no code of the branch runs after its defer,
# e.g. A defer / after cancel / branch defer / end (a running branch
# cancelled at its next wait, as a running task is)
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
