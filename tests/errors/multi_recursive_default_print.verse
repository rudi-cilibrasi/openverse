# expect: 3:0: Count has several values and is recursive, or called by a recursive one, and it may print
H(X:int, ?D:int = (Print("default"); 0))<computes>:int = X + D
Count(N:int)<computes><decides>:int =
    N > 0
    H(N) | Count[N - 1]
Main():void = if (X := Count[3], X < 3) then Print("first {X}")
