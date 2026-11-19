# The owner returns inside this arm's Signal. The active arm finishes
# without another wait, so its current step can complete the rush and
# continue after it while pending siblings remain cancelled.
# (#724: a branch and a rush's arm that goes on are children of the task whose
# code started them, stopped when it ends, after its defers, or is cancelled,
# before them (Epic's Verse VM, UEFN 43.12); not when their function exits.)
Owner()<suspends>:int=
    defer:
        Print("probe owner cleanup 0")
    E:=event(int){}
    branch:
        R:=rush:
            block:
                defer:
                    Print("probe active cleanup 0")
                Sleep(0.1)
                E.Signal(1)
                Print("probe after signal 0")
                1
            block:
                defer:
                    Print("probe other cleanup 0")
                Sleep(1.0)
                Print("probe wrong other 0")
                1
        Print("probe after rush 0")
    E.Await()
    Print("probe owner done 0")
    1
Main()<suspends>:void=
    N:=Owner()
    Print("main continued")
    Sleep(1.0)
    Print("main done")
