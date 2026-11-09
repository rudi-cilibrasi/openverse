# a branch with a rush inside whose losers have defers: (a) the branch still (#254, from the review of #258)
# running, (b) the branch ended while its rush losers go on
F()<suspends>:int =
    branch:
        defer:
            Print("B defer")
        X := rush:
            block:
                defer:
                    Print("R1 defer")
                Sleep(5.0)
                1
            block:
                defer:
                    Print("R2 defer")
                Sleep(5.0)
                2
            block:
                Sleep(0.1)
                3
        Print("B got {X}")
        Sleep(5.0)
    branch:
        defer:
            Print("C defer")
        Sleep(5.0)
    Sleep(0.5)
    0
G()<suspends>:int =
    branch:
        defer:
            Print("B ended")
        X := rush:
            block:
                defer:
                    Print("R1 defer")
                Sleep(5.0)
                1
            block:
                defer:
                    Print("R2 defer")
                Sleep(5.0)
                2
            block:
                Sleep(0.1)
                3
        Print("B got {X}")
    branch:
        defer:
            Print("C defer")
        Sleep(5.0)
    Sleep(0.5)
    0
Main()<suspends>:void =
    Print("{F()}")
    Print("{G()}")
