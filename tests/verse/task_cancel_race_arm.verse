# A race arm awaits a cancelled task in a first run, and so waits (the Book's
# API, task, Await); the other arm sleeps, then ends and wins, and the arm
# that awaits is cancelled as any loser. Expected: arm b defer / F got 2 /
# F defer / main goes on
W()<suspends>:int =
    Sleep(9.0)
    1
F()<suspends>:int =
    defer:
        Print("F defer")
    T := spawn{W()}
    T.Cancel()
    X := race:
        T.Await()
        block:
            defer:
                Print("arm b defer")
            Sleep(0.3)
            2
    Print("F got {X}")
    X
Main()<suspends>:void =
    spawn{F()}
    Sleep(1.0)
    Print("main goes on")
