# the same in a value: computed eagerly (#246, review of #267)
Gen(N:int)<computes><decides>:int =
    N > 0
    (if (Y := Gen[N - 1], Y > 1) then Y * 10 else 0) + N | Gen[N - 1]
Main():void =
    for (X := Gen[3]) { Print("{X}") }
