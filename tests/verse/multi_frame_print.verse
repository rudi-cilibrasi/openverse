# (its call of itself with code after it: taken lazily, the code a return frame that runs on each of its values, #283)
Show(X:int)<computes>:int =
    Print("x")
    X
Count(N:int)<computes><decides>:int =
    N > 0
    Show(N) | Count[N - 1] + 0
Main():void =
    for (X := Count[3]) { Print("{X}") }
