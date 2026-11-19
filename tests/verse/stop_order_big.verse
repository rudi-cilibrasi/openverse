# a larger program of branches, rushes and their stop order (#254, from the review of #258)
# (#724: a branch and a rush's arm that goes on are children of the task whose
# code started them, stopped when it ends, after its defers, or is cancelled,
# before them (Epic's Verse VM, UEFN 43.12); not when their function exits.)
F()<suspends>:int =
    branch:
        defer:
            Print("T defer")
        Sleep(0.1)
        branch:
            defer:
                Print("T.1 defer")
            Sleep(0.1)
            branch:
                defer:
                    Print("T.1.1 defer")
                Sleep(0.1)
                branch:
                    defer:
                        Print("T.1.1.1 defer")
                    Sleep(0.1)
                    branch:
                        defer:
                            Print("T.1.1.1.1 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    branch:
                        defer:
                            Print("T.1.1.1.2 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    Sleep(9.0)
                branch:
                    defer:
                        Print("T.1.1.2 defer")
                    Sleep(0.1)
                    branch:
                        defer:
                            Print("T.1.1.2.1 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    branch:
                        defer:
                            Print("T.1.1.2.2 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    Sleep(9.0)
                Sleep(9.0)
            branch:
                defer:
                    Print("T.1.2 defer")
                Sleep(0.1)
                branch:
                    defer:
                        Print("T.1.2.1 defer")
                    Sleep(0.1)
                    branch:
                        defer:
                            Print("T.1.2.1.1 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    branch:
                        defer:
                            Print("T.1.2.1.2 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    Sleep(9.0)
                branch:
                    defer:
                        Print("T.1.2.2 defer")
                    Sleep(0.1)
                    branch:
                        defer:
                            Print("T.1.2.2.1 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    branch:
                        defer:
                            Print("T.1.2.2.2 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    Sleep(9.0)
                Sleep(9.0)
            Sleep(9.0)
        branch:
            defer:
                Print("T.2 defer")
            Sleep(0.1)
            branch:
                defer:
                    Print("T.2.1 defer")
                Sleep(0.1)
                branch:
                    defer:
                        Print("T.2.1.1 defer")
                    Sleep(0.1)
                    branch:
                        defer:
                            Print("T.2.1.1.1 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    branch:
                        defer:
                            Print("T.2.1.1.2 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    Sleep(9.0)
                branch:
                    defer:
                        Print("T.2.1.2 defer")
                    Sleep(0.1)
                    branch:
                        defer:
                            Print("T.2.1.2.1 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    branch:
                        defer:
                            Print("T.2.1.2.2 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    Sleep(9.0)
                Sleep(9.0)
            branch:
                defer:
                    Print("T.2.2 defer")
                Sleep(0.1)
                branch:
                    defer:
                        Print("T.2.2.1 defer")
                    Sleep(0.1)
                    branch:
                        defer:
                            Print("T.2.2.1.1 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    branch:
                        defer:
                            Print("T.2.2.1.2 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    Sleep(9.0)
                branch:
                    defer:
                        Print("T.2.2.2 defer")
                    Sleep(0.1)
                    branch:
                        defer:
                            Print("T.2.2.2.1 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    branch:
                        defer:
                            Print("T.2.2.2.2 defer")
                        Sleep(0.1)
                        Sleep(9.0)
                    Sleep(9.0)
                Sleep(9.0)
            Sleep(9.0)
        Sleep(9.0)
    branch:
        defer:
            Print("C defer")
        branch:
            defer:
                Print("C.c defer")
            branch:
                defer:
                    Print("C.c.c defer")
                branch:
                    defer:
                        Print("C.c.c.c defer")
                    branch:
                        defer:
                            Print("C.c.c.c.c defer")
                        branch:
                            defer:
                                Print("C.c.c.c.c.c defer")
                            branch:
                                defer:
                                    Print("C.c.c.c.c.c.c defer")
                                branch:
                                    defer:
                                        Print("C.c.c.c.c.c.c.c defer")
                                    branch:
                                        defer:
                                            Print("C.c.c.c.c.c.c.c.c defer")
                                        Sleep(9.0)
                                    Sleep(9.0)
                                Sleep(9.0)
                            Sleep(9.0)
                        Sleep(9.0)
                    Sleep(9.0)
                Sleep(9.0)
            Sleep(9.0)
        Sleep(9.0)
    Sleep(2.0)
    0
Main()<suspends>:void = Print("{F()}")
