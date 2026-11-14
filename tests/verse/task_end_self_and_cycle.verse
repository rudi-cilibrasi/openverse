# A task that awaits itself, and two tasks that await each other: the
# awaited task is active, so the Await suspends ("Every other phase
# suspends", the Book's API, task, Await), and it cannot complete while its
# own code waits there. Itself's arm awaiting its own task loses its race to
# a timer (and deregisters), so Itself ends and Main, which awaits it, goes
# on; a and b wait for ever, and the program ends with Main, their defers
# not run.
Itself(Me:event(task(int)))<suspends>:int =
    T := Me.Await()
    R := race:
        T.Await()
        block:
            Sleep(0.1)
            7
    Print("itself: the timer won with {R}")
    R
Pair(Other:event(task(int)), N:string)<suspends>:int =
    O := Other.Await()
    defer:
        Print("{N} defer")
    Print("{N} awaits the other")
    O.Await()
Main()<suspends>:void =
    Me := event(task(int)){}
    S := spawn{Itself(Me)}
    Me.Signal(S)
    Print("itself ended with {S.Await()}")
    EA := event(task(int)){}
    EB := event(task(int)){}
    A := spawn{Pair(EA, "a")}
    B := spawn{Pair(EB, "b")}
    EA.Signal(B)
    EB.Signal(A)
    Sleep(0.5)
    Print("a and b still wait")
