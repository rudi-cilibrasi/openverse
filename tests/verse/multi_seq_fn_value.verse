# (#283) Choice points in sequence: a choice after its call of itself, in a <computes> function that prints (a function value): taken lazily.
Count(Op:type{_(:int)<computes>:int}, N:int)<computes><decides>:int =
    N > 0
    Op(N) | Count[Op, N - 1] + (0 | 1)
Loud(N:int)<computes>:int =
    Print("loud")
    N
Main():void =
    for (X := Count[Loud, 2]) { Print("{X}") }
