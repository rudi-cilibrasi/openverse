# expect: 2:0: M has several values and named parameters, and is called by a recursive one
M(A : int, ?B : int = A * 10)<computes>:int = A | B
R(N : int)<computes>:int =
    if (N > 0) then (M(N, ?B := 7) | R(N - 1)) else 0
Main()<transacts>:void =
    for (X := R(2)):
        Print("{X}")
