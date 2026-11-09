# expect: 2:23: the default of ?B of M uses itself
M(A : int, ?B : int = M[A + 1])<decides><transacts>:int = A | B
Main()<transacts>:void =
    for (X := M[1]):
        Print("{X}")
