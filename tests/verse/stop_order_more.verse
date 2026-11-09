# (a) a rush winner arm whose own inner rush left a loser going on (#254, from the review of #258)
F()<suspends>:int =
    X := rush:
        block:
            Y := rush:
                block:
                    defer:
                        Print("inner loser defer")
                    Sleep(5.0)
                    1
                block:
                    Sleep(0.1)
                    2
            Y
        block:
            defer:
                Print("outer loser defer")
            Sleep(5.0)
            3
    branch:
        defer:
            Print("C defer")
        Sleep(5.0)
    Sleep(0.5)
    X
# (b) a function with nested branches cancelled as a race loser
G()<suspends>:int =
    defer:
        Print("G defer")
    branch:
        defer:
            Print("G.A defer")
        branch:
            defer:
                Print("G.A.1 defer")
            Sleep(5.0)
        Sleep(5.0)
    branch:
        defer:
            Print("G.B defer")
        Sleep(5.0)
    Sleep(5.0)
    1
H()<suspends>:int =
    race:
        G()
        block:
            Sleep(0.5)
            2
# (c) a branch whose race arm (cancelled by the winner) started a branch
K()<suspends>:int =
    branch:
        defer:
            Print("K.A defer")
        X := race:
            block:
                defer:
                    Print("K.A race loser defer")
                branch:
                    defer:
                        Print("K.A.loser.b defer")
                    Sleep(5.0)
                Sleep(5.0)
                1
            block:
                Sleep(0.1)
                2
        Print("K.A won {X}")
        Sleep(5.0)
    branch:
        defer:
            Print("K.B defer")
        Sleep(5.0)
    Sleep(0.5)
    0
Main()<suspends>:void =
    defer:
        Print("Main defer")
    Print("{F()}")
    Print("{H()}")
    Print("{K()}")
    branch:
        defer:
            Print("Main.A defer")
        branch:
            defer:
                Print("Main.A.1 defer")
            Sleep(5.0)
        Sleep(5.0)
    branch:
        defer:
            Print("Main.B defer")
        Sleep(5.0)
    Sleep(0.5)
