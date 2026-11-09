# expect: 3:22: unknown identifier 'K'
# (a default does not see the caller's names)
F(A : int, ?B : int = K)<transacts>:int = A | B
Main()<transacts>:void =
    K := 4
    for (X := F(1)):
        Print("{X}")
