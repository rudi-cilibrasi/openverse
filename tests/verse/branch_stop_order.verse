# a function's branches and rush losers are stopped last started first, by
# when they started, also when one starts inside another (#187)
F()<suspends>:int =
    defer:
        Print("F defer")
    branch:
        defer:
            Print("outer branch defer")
        Sleep(0.1)
        branch:
            defer:
                Print("inner branch defer")
            Sleep(5.0)
        Sleep(5.0)
    branch:
        defer:
            Print("second branch defer")
        Sleep(5.0)
    Sleep(1.0)
    0
G(N:int)<suspends>:int =
    X := rush:
        block:
            Sleep(0.2)
            1
        block:
            defer:
                Print("loser {N} defer")
            Sleep(5.0)
            2
    branch:
        defer:
            Print("late branch {N} defer")
        Sleep(5.0)
    Sleep(0.5)
    X
Main()<suspends>:void =
    Print("{F()}")
    # the same call site twice: the frame is reused, its stopped sites cleared
    var I:int = 0
    loop:
        if (I = 2) then break
        Print("{G(I)}")
        set I += 1
