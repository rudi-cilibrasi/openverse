# (its call of itself with code after it: taken lazily, the code a return frame that runs on each of its values, #283)
K:int = (Print("constant"); 7)
Count(N:int)<computes><decides>:int =
    N > 0
    K | Count[N - 1] + 0
Main():void =
    for (X := Count[2]) { Print("{X}") }
