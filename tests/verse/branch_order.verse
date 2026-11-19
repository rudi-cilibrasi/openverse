# a task's branches are stopped last started first: after its own defers when it ends, before them when it is cancelled (#156, #724: the
# task's, not the function's, which no longer stops them when it returns; Epic's Verse VM, UEFN 43.12, branch-cancel-order)
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
