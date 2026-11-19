# A Signal resumes the owner, which returns while this rush arm runs.
# Pending siblings stop immediately; the active arm reaches its next wait
# before cancellation runs its saved cleanup.
# (#724: a branch and a rush's arm that goes on are children of the task whose
# code started them, stopped when that task ends, after its own defers: Epic's
# Verse VM, UEFN 43.12; no longer when the function that started them exits.)
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
                Sleep(1.0)
                Print("probe wrong active 0")
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
