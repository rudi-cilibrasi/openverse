# a rush whose losers start branches (#254, from the review of #258)
# (#724: a branch and a rush's arm that goes on are children of the task whose
# code started them, stopped when that task ends, after its own defers: Epic's
# Verse VM, UEFN 43.12; no longer when the function that started them exits.)
F()<suspends>:int =
    defer:
        Print("F defer")
    X := rush:
        block:
            defer:
                Print("L1 defer")
            branch:
                defer:
                    Print("L1.b defer")
                Sleep(5.0)
            Sleep(0.2)
            branch:
                defer:
                    Print("L1.c defer")
                Sleep(5.0)
            Sleep(5.0)
            1
        block:
            Sleep(0.1)
            2
        block:
            defer:
                Print("L3 defer")
            Sleep(0.3)
            branch:
                defer:
                    Print("L3.b defer")
                Sleep(5.0)
            Sleep(5.0)
            3
    branch:
        defer:
            Print("G defer")
        Sleep(5.0)
    Sleep(1.0)
    X
Main()<suspends>:void = Print("{F()}")
