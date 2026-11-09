# a generator with a var its clauses set: an alternative after its call of itself sees the value it saw before it (#246)
Steps(N:int)<transacts><decides>:int =
    N > 0
    var S:int = N * 2
    set S += 1
    Print("step {N}")
    S | Steps[N - 1] | S + 100
Main():void =
    for (X := Steps[3]):
        Print("got {X}")
