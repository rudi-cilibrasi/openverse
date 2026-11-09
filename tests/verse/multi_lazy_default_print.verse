# a value that prints through a parameter's default, rejected by the if's next clause: undone with it, as for a choice (#246)
H(X:int, ?D:int = (Print("default"); 0))<computes>:int = X + D
Count(N:int)<computes><decides>:int =
    N > 0
    H(N) | Count[N - 1]
Main():void = if (X := Count[3], X < 3) then Print("first {X}")
