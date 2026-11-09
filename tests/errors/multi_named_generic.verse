# expect: 2:0: F has several values and named parameters, and is generic
F(A : t, ?B : t where t : type)<transacts>:t = A | B
Main()<transacts>:void =
    for (X := F(1, ?B := 2)):
        Print("{X}")
