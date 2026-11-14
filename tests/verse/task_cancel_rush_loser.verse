# F's first run: a rush whose arm 1 awaits a cancelled task (and waits),
# while arm 2 ends at once and wins; arm 1 goes on as a loser task, still
# waiting, until F's exit stops it. Expected: F got 5 / F end / F defer /
# loser defer / main end
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
            T.Await()
        # (Sleep(0.0) completes at once: an arm that can suspend, as every
        # arm of a rush must, and ends without waiting)
        block:
            Sleep(0.0)
            5
    Print("F got {X}")
    Sleep(0.2)
    Print("F end")
    X
Main()<suspends>:void =
    T := spawn{W()}
    T.Cancel()
    spawn{F(T)}
    Sleep(1.0)
    Print("main end")
