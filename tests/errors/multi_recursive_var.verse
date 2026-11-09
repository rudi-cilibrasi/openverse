# expect: 2:0: R has several values and is recursive, or called by a recursive one, and it has a var or a set
R(N:int)<computes><decides>:int =
    N > 0
    var K:int = 0
    X := (set K += 1; K) | (set K += 1; K)
    K | R[N - 1]
Main():void = for (X := R[1]) { Print("{X}") }
