# (#283) Choice points in sequence: a choice after its call of itself, in a <computes> function that prints (a constant it reads): taken lazily.
K:int = (Print("constant"); 7)
Count(N:int)<computes><decides>:int =
    N > 0
    K | Count[N - 1] + (0 | 1)
Main():void =
    for (X := Count[2]) { Print("{X}") }
