# An awaiter whose task an earlier awaiter of the same round cancels does
# not go on at its turn: it unwinds when it is cancelled
First(E:event(int), Other:task(void))<suspends>:void =
    V := E.Await()
    Print("first got {V}, cancels second")
    Other.Cancel()
Second(E:event(int))<suspends>:void =
    defer:
        Print("second unwinds")
    Sleep(0.1)
    V := E.Await()
    Print("second got {V}")
Main()<suspends>:void =
    E := event(int){}
    T2 := spawn{Second(E)}
    spawn{First(E, T2)}
    Sleep(1.0)
    E.Signal(5)
    Print("main after signal")
