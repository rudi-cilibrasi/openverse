# P (resumed by the scheduler) spawns C, whose first run cancels P, which is
# running. Expected: P is cancelled at its next wait (as a task cancelling
# itself is); C goes on: C cancelled P / P after spawn / P defer / C end / end
C(Parent:task(int))<suspends>:int =
    defer:
        Print("C defer")
    Parent.Cancel()
    Print("C cancelled P")
    Sleep(0.5)
    Print("C end")
    0
P(Me:event(task(int)))<suspends>:int =
    defer:
        Print("P defer")
    T := Me.Await()
    spawn{C(T)}
    Print("P after spawn")
    Sleep(1.0)
    Print("never")
    1
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{P(Me)}
    Me.Signal(S)
    Sleep(2.0)
    Print("end")
