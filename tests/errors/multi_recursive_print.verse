# expect: 6:0: Count has several values and is recursive, or called by a recursive one, and it may print (Show does)
# (its call of itself inside an alternative: all its values computed at a call, F$all, not taken lazily, #246)
Show(X:int)<computes>:int =
    Print("x")
    X
Count(N:int)<computes><decides>:int =
    N > 0
    Show(N) | Count[N - 1] + 0
Main():void =
    for (X := Count[3]) { Print("{X}") }
