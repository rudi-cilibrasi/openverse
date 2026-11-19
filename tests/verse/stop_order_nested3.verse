# nested branches 3 levels deep (#254, from the review of #258)
# (#724: a branch and a rush's arm that goes on are children of the task whose
# code started them, stopped when that task ends, after its own defers: Epic's
# Verse VM, UEFN 43.12; no longer when the function that started them exits.)
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
            Sleep(0.1)
            branch:
                defer:
                    Print("A.1.1 defer")
                Sleep(5.0)
            branch:
                defer:
                    Print("A.1.2 defer")
                Sleep(5.0)
            Sleep(5.0)
        branch:
            defer:
                Print("A.2 defer")
            Sleep(5.0)
        Sleep(5.0)
    branch:
        defer:
            Print("B defer")
        Sleep(0.3)
        branch:
            defer:
                Print("B.1 defer")
            Sleep(5.0)
        Sleep(5.0)
    Sleep(1.0)
    0
Main()<suspends>:void = Print("{F()}")
