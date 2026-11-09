# At a function's exit, its branches and rush losers stop last started first,
# each unwinding whole: what it started (a rush it waits in) first (#254).
F1()<suspends>:int =
    branch:
        defer:
            Print("B1 defer")
        Sleep(0.3)
        X := rush:
            block:
                defer:
                    Print("B1 arm 1")
                Sleep(5.0)
                1
            block:
                defer:
                    Print("B1 arm 2")
                Sleep(5.0)
                2
    branch:
        defer:
            Print("B2 defer")
        Sleep(5.0)
    Sleep(0.5)
    0
F2()<suspends>:int =
    X := rush:
        block:
            defer:
                Print("A defer")
            Sleep(0.3)
            Y := rush:
                block:
                    defer:
                        Print("A inner 1")
                    Sleep(5.0)
                    1
                block:
                    Sleep(5.0)
                    2
            Y
        block:
            defer:
                Print("B defer")
            Sleep(5.0)
            2
        block:
            Sleep(0.1)
            3
    Sleep(0.5)
    X
Main()<suspends>:void =
    Print("{F1()}")
    Print("{F2()}")
