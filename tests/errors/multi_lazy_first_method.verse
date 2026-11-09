# expect: 12:18: Count has several values, is recursive and may print (printer.Show does) in its clauses
# (#246) a clause that prints through a method
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
