# sync runs its arms concurrently and gives their values in order; race gives the first to finish and cancels the others, running their defers (#156)
Worker(Name:string, N:int, D:float)<suspends>:int =
    var I:int = 0
    loop:
        if (I >= N) then break
        Sleep(D)
        set I += 1
        Print("{Name} {I}")
    I * 10
Main()<suspends>:void =
    R := sync:
        Worker("a", 3, 1.0)
        Worker("b", 2, 1.5)
    Print("{R(0)} {R(1)}")
    W := race:
        block:
            Sleep(2.0)
            "slow"
        block:
            Sleep(1.0)
            "fast"
    Print(W)
    X := race:
        block:
            defer:
                Print("loser cleaned up")
            Sleep(5.0)
            1
        block:
            Sleep(1.0)
            2
    Print("{X}")
    # (an arm that ends without waiting wins at once, and the arms after it
    # never start; every arm can suspend, the Book's rule, so this one
    # starts with Sleep(0.0), which completes at once)
    Y := race:
        block:
            Sleep(0.0)
            Print("first")
            7
        block:
            Print("never")
            Sleep(1.0)
            8
    Print("{Y}")
