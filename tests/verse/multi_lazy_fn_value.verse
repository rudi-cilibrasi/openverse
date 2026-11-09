# a function value as a parameter of a lazily taken function, saved with its items, in a for (#246)
Count(Op:type{_(:int)<computes>:int}, N:int)<computes><decides>:int =
    N > 0
    Op(N) | Count[Op, N - 1]
Loud(N:int)<computes>:int =
    Print("loud")
    N
Main():void =
    for (X := Count[Loud, 2]) { Print("{X}") }
