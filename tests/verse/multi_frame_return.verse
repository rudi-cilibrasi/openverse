# (#283) A return in an if's branch, then a call of itself with code after it.
F(N:int)<transacts>:int =
    if (N <= 0):
        return 7
    Print("in {N}")
    F(N - 1) * 2 | N
Main()<transacts>:void =
    for (V := F(2)) { Print("v {V}") }
    if (V := F(2), V > 20) then Print("first {V}")
