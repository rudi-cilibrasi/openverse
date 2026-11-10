# A generic function with several values and named parameters (#283): its type arguments inferred from the arguments, named ones too
F(A : t, ?B : t where t : type)<transacts>:t = A | B
Main()<transacts>:void =
    for (X := F(1, ?B := 2)):
        Print("{X}")
