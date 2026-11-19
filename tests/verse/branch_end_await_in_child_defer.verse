# A spawned task's children are stopped when its call ends, before the task
# is done and its awaiters resume (Epic's Verse VM, UEFN 43.12,
# followup-conc/branch-end-before-awaiter). An Await of the task made
# meanwhile, by a task spawned in a child's defer, waits for it to be done,
# and is resumed after the awaiters that registered before it (#724; the
# scheduler model, sched_gen seed 5100): until then it got the result at
# once, before the task was done.
holder := class:
    var T:?task(int) = false
Awaiter(H:holder, Tag:string)<suspends>:void =
    if (T := H.T?):
        V := T.Await()
        Print("{Tag} awaiter got {V}")
StartAwaiter(H:holder, Tag:string):void = spawn{Awaiter(H, Tag)}
Runner(H:holder)<suspends>:int =
    branch:
        defer:
            Print("branch cleanup")
            StartAwaiter(H, "late")
            Print("branch cleanup done")
        Sleep(10.0)
    Sleep(0.1)
    Print("runner ending")
    5
Main()<suspends>:void =
    H := holder{}
    T := spawn{Runner(H)}
    set H.T = option{T}
    spawn{Awaiter(H, "early")}
    V := T.Await()
    Print("main got {V}")
    Sleep(0.1)
    Print("end")
