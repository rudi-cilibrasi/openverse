# a set in the argument of a generator's call of itself, where the first success is taken: undone with that call's rejected values, so the next alternative sees the name as it was (#246 step 2)
Gen(N:int)<computes><decides>:int =
    N > 0
    var K:int = 0
    Gen[(set K = 1; N - 1)] | K
Main():void =
    if (X := Gen[1]) then Print("first {X}")
