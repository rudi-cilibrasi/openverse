# a branch that cancels the task running its own function goes on until it
# waits next; the task is cancelled then, its branch stopped with it (#260)
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
