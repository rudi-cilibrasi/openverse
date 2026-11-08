# a function's own defers run first, then its branches are stopped, last started first, whether it returns or is cancelled (#156)
F(Tag:string, D:float)<suspends>:void =
    defer:
        Print("{Tag} F defer")
    branch:
        defer:
            Print("{Tag} B1 defer")
        Sleep(10.0)
    branch:
        defer:
            Print("{Tag} B2 defer")
        Sleep(10.0)
    Sleep(D)
    Print("{Tag} F end")
Main()<suspends>:void =
    F("normal", 0.1)
    race:
        F("cancelled", 1.0)
        Sleep(0.5)
    Print("main end")
