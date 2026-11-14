# An awaiter that signals the same event again, while the first Signal's
# round is in flight, reaches the awaits registered since it began; the
# outer round goes on after (the Book's tests,
# FORT-1126351_reentrant_signal_probe: "still resumes every parked awaiter")
Again(E:event(int), Other:event(int))<suspends>:void =
    V := E.Await()
    Print("again got {V}")
    Other.Signal(V)
    E.Signal(V + 10)
    Print("again done")
Parker(E:event(int), Other:event(int))<suspends>:void =
    V := Other.Await()
    Print("parker got {V}, parks on E")
    W := E.Await()
    Print("parker got {W}")
Outer(E:event(int))<suspends>:void =
    V := E.Await()
    Print("outer got {V}")
Main()<suspends>:void =
    E := event(int){}
    O := event(int){}
    spawn{Again(E, O)}
    spawn{Outer(E)}
    spawn{Parker(E, O)}
    E.Signal(1)
    Print("main after signal")
