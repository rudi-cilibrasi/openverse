# P (resumed by the scheduler) spawns C, whose first run spawns G, whose
# first run cancels P (two levels up, P running). Expected: P is cancelled
# at its next wait; C and G go on:
# G cancelled P / C goes on / P goes on / P defer / G end / C end / end
G(P:task(int))<suspends>:int =
    P.Cancel()
    Print("G cancelled P")
    Sleep(0.2)
    Print("G end")
    0
C(P:task(int))<suspends>:int =
    spawn{G(P)}
    Print("C goes on")
    Sleep(0.3)
    Print("C end")
    0
P(Me:event(task(int)))<suspends>:int =
    defer:
        Print("P defer")
    T := Me.Await()
    spawn{C(T)}
    Print("P goes on")
    Sleep(1.0)
    Print("never")
    1
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{P(Me)}
    Me.Signal(S)
    Sleep(2.0)
    Print("end")
