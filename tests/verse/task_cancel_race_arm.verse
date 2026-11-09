# A race arm awaits a cancelled task in a first run; the other arm sleeps.
# Expected: F is cancelled at its wait: arm b defer / F defer / main goes on
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
    Print("never {X}")
    X
Main()<suspends>:void =
    spawn{F()}
    Sleep(1.0)
    Print("main goes on")
