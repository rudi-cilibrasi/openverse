# expect: 3:0: T has several values and is recursive, or called by a recursive one, and it is not <computes>
# (a call of itself after another: not taken lazily yet, #283)
T(N:int)<transacts>:int =
    if (N <= 0) then (1 | 2) else block:
        A := T(N - 1)
        B := T(N - 1)
        A * 10 + B
Main()<transacts>:void =
    for (V := T(1)) { Print("v {V}") }
