# (#362) a rush arm returns while an earlier arm's chain (recorded) waits; the arm
# that returns is nested in a race inside the rush arm (ret 2 through two
# constructs)
Deep(N:int)<suspends>:int =
    defer:
        Print("deep {N} unwinds")
    if (N = 0):
        Sleep(0.1)
        Print("deep leaf woke")
        0
    else:
        Deep(N - 1) + 1
F()<suspends>:int =
    rush:
        Deep(3)
        block:
            race:
                Sleep(1.0)
                block:
                    Sleep(0.01)
                    return 5
            1
    0
Main()<suspends>:void =
    Print("F gave {F()}")
    Sleep(0.01)
    Print("main after sleep")
    Sleep(0.2)
    Print("main done")
