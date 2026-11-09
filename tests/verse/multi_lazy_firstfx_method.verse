# a clause printing through a method, where the first success is taken (#246 step 2)
printer := class:
    Show(N:int)<computes>:int =
        Print("show {N}")
        N
Count(O:printer, N:int)<computes><decides>:int =
    N > 0
    O.Show(N) > 0
    N | Count[O, N - 1]
Main():void =
    if (X := Count[printer{}, 3], X < 2) then Print("first {X}")
