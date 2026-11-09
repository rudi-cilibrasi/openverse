# A task cancels itself (it is resumed by the scheduler, not in a first run),
# then spawns C before its next wait. Expected (LANGUAGE.md: a task that
# cancels itself is cancelled at its next wait; C is an unrelated task):
#   still running until it waits / selfstop defer / C end / C defer / end
C()<suspends>:int =
    defer:
        Print("C defer")
    Sleep(0.5)
    Print("C end")
    0
SelfStop(Me:event(task(int)))<suspends>:int =
    defer:
        Print("selfstop defer")
    T := Me.Await()
    T.Cancel()
    spawn{C()}
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
