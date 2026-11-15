# A Signal resumes the owner, which returns while this rush arm runs.
# Pending siblings stop immediately; the active arm reaches its next wait
# before cancellation runs its saved cleanup.
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
