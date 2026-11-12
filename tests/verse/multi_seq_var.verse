# (#283) Choice points in sequence: a choice of blocks that set a var, followed by a choice with a call of itself, in a <computes> function: taken lazily; each alternative sees the var as the one before left it.
R(N:int)<computes><decides>:int =
    N > 0
    var K:int = 0
    X := (set K += 1; K) | (set K += 1; K)
    K | R[N - 1]
Main():void = for (X := R[1]) { Print("{X}") }
