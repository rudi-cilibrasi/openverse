# (#283) Choice points in sequence: a choice after its call of itself, in a <computes> function that prints (a parameter's default): taken lazily, where the first success is taken.
H(X:int, ?D:int = (Print("default"); 0))<computes>:int = X + D
Count(N:int)<computes><decides>:int =
    N > 0
    H(N) | Count[N - 1] + (0 | 1)
Main():void = if (X := Count[3], X < 3) then Print("first {X}")
