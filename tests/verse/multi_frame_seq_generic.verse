# (#283) Choice points in sequence in a generic function and in a method,
# whose code after its call of itself sets a field.
Pairs(X:t, Y:t, N:int where t:type)<transacts><decides>:tuple(t, int) =
    N > 0
    P := Pairs[Y, X, N - 1] | (X, N)
    Print("pairs {N}")
    P | (P(0), P(1) + 100)
walker := class:
    var Seen:int = 0
    Walk(N:int)<transacts><decides>:int =
        N > 0
        X := Walk[N - 1] | N
        set Seen += 1
        X | X * 10
Main()<transacts>:void =
    for (P := Pairs["a", "b", 2]) { Print("p {P(0)} {P(1)}") }
    if (P := Pairs["a", "b", 2], P(1) > 100) then Print("first {P(0)} {P(1)}")
    W := walker{}
    for (V := W.Walk[2]) { Print("w {V} {W.Seen}") }
    if (V := W.Walk[2], V > 15) then Print("first {V} {W.Seen}")
