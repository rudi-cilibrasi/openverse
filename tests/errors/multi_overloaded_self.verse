# expect: 2:0: F is overloaded with several values, and this overload calls F
F(N : int):int = N | F("x")
F(S : string):int = 1 | 2
Main()<transacts>:void =
    for (X := F(1)):
        Print("{X}")
