# A race arm awaits a cancelled task (and so waits), the next arm wins at
# once; F then ends in its first run. Does F end normally, or is it
# cancelled after it ended (its task marked cancelled)?
W()<suspends>:int =
    Sleep(9.0)
    1
F(T:task(int))<suspends>:int =
    defer:
        Print("F defer")
    X := race:
        T.Await()
        # (Sleep(0.0) completes at once: an arm that can suspend, as every
        # arm of a race must, and ends without waiting)
        block:
            Sleep(0.0)
            5
    Print("F got {X}")
    X
Main()<suspends>:void =
    T := spawn{W()}
    T.Cancel()
    U := spawn{F(T)}
    Print("main awaits")
    Print("main got {U.Await()}")
    Print("main end")
