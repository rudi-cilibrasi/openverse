# a value computed by a method that prints, in an if (#246)
printer := class:
    Show(N:int)<computes>:int =
        Print("show {N}")
        N
Count(O:printer, N:int)<computes><decides>:int =
    N > 0
    O.Show(N) | Count[O, N - 1]
Main():void =
    if (X := Count[printer{}, 3]) then Print("first {X}")
