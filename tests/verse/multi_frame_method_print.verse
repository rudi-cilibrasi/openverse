# (its call of itself with code after it: taken lazily, the code a return frame that runs on each of its values, #283)
printer := class:
    Show(N:int)<computes>:int =
        Print("show {N}")
        N
Count(O:printer, N:int)<computes><decides>:int =
    N > 0
    O.Show(N) | Count[O, N - 1] + 0
Main():void =
    if (X := Count[printer{}, 3]) then Print("first {X}")
