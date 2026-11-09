# a set in the argument of a generator's call of itself, in a for: the alternatives after the call see it, also when the call's clauses fail (#246)
Gen(N:int)<transacts><decides>:int =
    N > 0
    var K:int = 0
    N | Gen[(set K += 1; N - 1)] | K * 100
Main():void =
    for (X := Gen[2]) { Print("all {X}") }
