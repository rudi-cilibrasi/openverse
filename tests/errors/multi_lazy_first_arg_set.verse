# expect: 6:8: a set in an argument of Gen's call of itself: where the first success is taken, it would not be undone
# (#246, review of #267) the next alternative would see the set, which the Verse Calculus undoes with the call's values the if rejects
Gen(N:int)<computes><decides>:int =
    N > 0
    var K:int = 0
    Gen[(set K = 1; N - 1)] | K
Main():void =
    if (X := Gen[1]) then Print("first {X}")
