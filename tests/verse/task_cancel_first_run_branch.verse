# a branch that awaits a cancelled task in its first run waits there (the
# Book's API, task, Await) until its task ends, which stops it, after the
# task's own code (#253: before, it was cancelled at once; #724: before, its
# function's exit stopped it)
W()<suspends>:int =
    Sleep(9.0)
    1
G(X:t where t:type)<suspends>:t =
    defer:
        Print("G defer")
    T := spawn{W()}
    T.Cancel()
    branch:
        defer:
            Print("branch defer")
        T.Await()
        Print("never")
    Sleep(0.5)
    Print("G end")
    X
Main()<suspends>:void =
    Print("{G(7)}")
    Print("main end")
