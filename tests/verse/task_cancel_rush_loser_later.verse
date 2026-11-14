# a rush loser (registered, not run at once) that awaits a cancelled task
# later, when the scheduler resumes it: it waits there until F's exit stops
# it. Expected: F got 5 / F end / F defer / loser defer / main end
W()<suspends>:int =
    Sleep(9.0)
    1
F(T:task(int))<suspends>:int =
    defer:
        Print("F defer")
    X := rush:
        block:
            defer:
                Print("loser defer")
            Sleep(0.1)
            T.Await()
        block:
            Sleep(0.05)
            5
    Print("F got {X}")
    Sleep(0.3)
    Print("F end")
    X
Main()<suspends>:void =
    T := spawn{W()}
    T.Cancel()
    spawn{F(T)}
    Sleep(1.0)
    Print("main end")
