# (#283) Choice points in sequence: a call of itself after another: the second call runs on each value of the first.
T(N:int)<transacts>:int =
    if (N <= 0) then (1 | 2) else block:
        A := T(N - 1)
        B := T(N - 1)
        A * 10 + B
Main()<transacts>:void =
    for (V := T(1)) { Print("v {V}") }
