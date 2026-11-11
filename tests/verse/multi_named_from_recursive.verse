# A named callee reached by an eager recursive producer.
M(A : int, ?B : int = A * 10)<computes>:int = A | B
R(N : int)<computes>:int =
    if (N > 0) then (M(N, ?B := 7) | R(N - 1)) else 0
Main()<transacts>:void =
    for (X := R(2)):
        Print("{X}")
