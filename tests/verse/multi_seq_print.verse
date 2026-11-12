# (#283) Choice points in sequence: a choice after its call of itself, in a <computes> function that prints: taken lazily.
Show(X:int)<computes>:int =
    Print("x")
    X
Count(N:int)<computes><decides>:int =
    N > 0
    Show(N) | Count[N - 1] + (0 | 1)
Main():void =
    for (X := Count[3]) { Print("{X}") }
