# expect: 3:0: Count has several values and is recursive, or called by a recursive one, and it may print (K does)
K:int = (Print("constant"); 7)
Count(N:int)<computes><decides>:int =
    N > 0
    K | Count[N - 1]
Main():void =
    for (X := Count[2]) { Print("{X}") }
