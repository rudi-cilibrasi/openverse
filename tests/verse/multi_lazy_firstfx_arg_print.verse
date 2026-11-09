# the argument of a generator's call of itself prints, where the first success is taken: once per call on the way to the value taken (#246 step 2)
Show(N:int)<computes>:int =
    Print("show {N}")
    N
Count(N:int)<computes><decides>:int =
    N > 0
    N | Count[Show(N) - 1]
Main():void =
    if (X := Count[3], X < 2):
        Print("{X}")
