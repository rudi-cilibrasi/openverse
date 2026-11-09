# (#260) a branch
# that cancels the task running its own function is stopped while it runs.
# Its defer runs at once, in the middle of its code, and its code then goes
# on ("B goes on" after "B defer"). Expected, as for a task that cancels
# itself: B unwinds at its next wait, so "B goes on" then "B defer".
F(Me:event(task(int)))<suspends>:int =
    defer:
        Print("F defer")
    branch:
        defer:
            Print("B defer")
        T := Me.Await()
        T.Cancel()
        Print("B goes on")
        Sleep(0.1)
        Print("B never")
    Sleep(5.0)
    0
Main()<suspends>:void =
    Me := event(task(int)){}
    T := spawn{F(Me)}
    Sleep(0.5)
    Me.Signal(T)
    Sleep(1.0)
    Print("end")
