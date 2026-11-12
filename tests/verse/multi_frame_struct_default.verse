# (its call of itself with code after it: taken lazily, the code a return frame that runs on each of its values, #283)
pt := struct<computes>:
    X:int = (Print("struct field"); 0)
Count(N:int)<computes><decides>:int =
    N > 0
    pt{}.X + N | Count[N - 1] + 0
Main():void = if (X := Count[3], X < 3) then Print("first {X}")
