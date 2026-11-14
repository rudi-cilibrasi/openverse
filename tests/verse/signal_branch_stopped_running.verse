# A branch's Signal resumes its own function, which ends and stops the
# branch while it runs: the branch goes on to its next wait, then unwinds
Owner(Done:event(int), Go:event(int))<suspends>:void =
    branch:
        defer:
            Print("branch unwinds")
        Go.Await()
        Print("branch signals")
        Done.Signal(1)
        Print("branch goes on")
        Go.Await()
        Print("branch resumes again")
    V := Done.Await()
    Print("owner got {V}, ends")
Main()<suspends>:void =
    D := event(int){}
    G := event(int){}
    spawn{Owner(D, G)}
    G.Signal(2)
    Print("main after first signal")
    G.Signal(3)
    Print("main ends")
