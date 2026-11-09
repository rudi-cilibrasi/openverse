# expect: 2:0: Count has several values and is recursive, or called by a recursive one, and it may print (Loud does)
Count(Op:type{_(:int)<computes>:int}, N:int)<computes><decides>:int =
    N > 0
    Op(N) | Count[Op, N - 1]
Loud(N:int)<computes>:int =
    Print("loud")
    N
Main():void =
    for (X := Count[Loud, 2]) { Print("{X}") }
