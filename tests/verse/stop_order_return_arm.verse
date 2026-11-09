# a function exiting by return from a race arm and from a sync arm (#254, from the review of #258)
F()<suspends>:int =
    defer:
        Print("F defer")
    branch:
        defer:
            Print("A defer")
        Sleep(0.1)
        branch:
            defer:
                Print("A.1 defer")
            Sleep(5.0)
        Sleep(5.0)
    branch:
        defer:
            Print("B defer")
        Sleep(5.0)
    X := race:
        block:
            defer:
                Print("arm1 defer")
            Sleep(0.3)
            return 7
        block:
            defer:
                Print("arm2 defer")
            Sleep(5.0)
            2
    X
G()<suspends>:int =
    defer:
        Print("G defer")
    branch:
        defer:
            Print("A defer")
        Sleep(0.1)
        X := rush:
            block:
                defer:
                    Print("A.r1 defer")
                Sleep(5.0)
                1
            block:
                defer:
                    Print("A.r2 defer")
                Sleep(5.0)
                2
        Sleep(5.0)
    branch:
        defer:
            Print("B defer")
        Sleep(5.0)
    Y := sync:
        block:
            defer:
                Print("s1 defer")
            branch:
                defer:
                    Print("s1.b defer")
                Sleep(5.0)
            Sleep(5.0)
            1
        block:
            defer:
                Print("s2 defer")
            Sleep(0.3)
            return 8
            2
    Y(0)
Main()<suspends>:void =
    Print("{F()}")
    Print("{G()}")
