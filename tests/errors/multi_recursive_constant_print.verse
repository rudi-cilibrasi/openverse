# expect: 4:0: Count has several values and is recursive, or called by a recursive one, and it may print (K does)
# (its call of itself inside an alternative: all its values computed at a call, F$all, not taken lazily, #246)
K:int = (Print("constant"); 7)
Count(N:int)<computes><decides>:int =
    N > 0
    K | Count[N - 1] + 0
Main():void =
    for (X := Count[2]) { Print("{X}") }
