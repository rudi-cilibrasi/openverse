# a generator taken lazily where it is consumed and computed eagerly (F$all) for a recursive function that calls it (#246)
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
Tri(N:int)<computes><decides>:int =
    N > 0
    Upto[1, N] | Tri[N - 1]
Main():void =
    for (X := Tri[3]) { Print("t {X}") }
    for (X := Upto[2, 4]) { Print("u {X}") }
