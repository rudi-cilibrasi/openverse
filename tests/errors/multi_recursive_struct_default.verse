# expect: 5:0: Count has several values and is recursive, or called by a recursive one, and it may print
# (a choice after its call of itself: all its values computed at a call, F$all, not taken lazily, #246, #283)
pt := struct<computes>:
    X:int = (Print("struct field"); 0)
Count(N:int)<computes><decides>:int =
    N > 0
    pt{}.X + N | Count[N - 1] + (0 | 1)
Main():void = if (X := Count[3], X < 3) then Print("first {X}")
