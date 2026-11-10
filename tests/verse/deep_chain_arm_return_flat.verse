# no recursion: a chain of five suspends functions makes the program resume
# waiting frames directly (#362);
# a sync arm returns while the other arm's chain waits forever
A3()<suspends>:int =
    Sleep(Inf)
    3
A2()<suspends>:int = A3() + 1
A1()<suspends>:int = A2() + 1
F()<suspends>:int =
    sync:
        A1()
        block:
            Sleep(0.0)
            return 5
    0
Main()<suspends>:void =
    X := F()
    Print("F gave {X}")
    Sleep(0.0)
    Print("main done")
