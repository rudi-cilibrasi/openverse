# expect: 7:0: Count has several values and is recursive, or called by a recursive one, and it may print (printer.Show does)
# (its call of itself inside an alternative: all its values computed at a call, F$all, not taken lazily, #246)
printer := class:
    Show(N:int)<computes>:int =
        Print("show {N}")
        N
Count(O:printer, N:int)<computes><decides>:int =
    N > 0
    O.Show(N) | Count[O, N - 1] + 0
Main():void =
    if (X := Count[printer{}, 3]) then Print("first {X}")
