# (#283) Choice points in sequence: a choice after its call of itself, in a <computes> function that prints (a method): taken lazily.
printer := class:
    Show(N:int)<computes>:int =
        Print("show {N}")
        N
Count(O:printer, N:int)<computes><decides>:int =
    N > 0
    O.Show(N) | Count[O, N - 1] + (0 | 1)
Main():void =
    if (X := Count[printer{}, 3]) then Print("first {X}")
