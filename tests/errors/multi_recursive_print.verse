# expect: 5:0: Count has several values and is recursive, or called by a recursive one, and it may print (Show does)
Show(X:int)<computes>:int =
    Print("x")
    X
Count(N:int)<computes><decides>:int =
    N > 0
    Show(N) | Count[N - 1]
Main():void =
    for (X := Count[3]) { Print("{X}") }
