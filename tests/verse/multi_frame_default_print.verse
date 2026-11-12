# (its call of itself with code after it: taken lazily, the code a return frame that runs on each of its values, #283)
H(X:int, ?D:int = (Print("default"); 0))<computes>:int = X + D
Count(N:int)<computes><decides>:int =
    N > 0
    H(N) | Count[N - 1] + 0
Main():void = if (X := Count[3], X < 3) then Print("first {X}")
