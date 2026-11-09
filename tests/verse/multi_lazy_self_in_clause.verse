# a generator whose clause has an if taking its own first value: computed eagerly, F$all, as its call of itself is not a whole alternative (#246, review of #267)
Gen(N:int)<computes><decides>:int =
    N > 0
    Z := if (Y := Gen[N - 1], Y > 1) then Y * 10 else 0
    Z + N | Gen[N - 1]
Main():void =
    for (X := Gen[3]) { Print("{X}") }
