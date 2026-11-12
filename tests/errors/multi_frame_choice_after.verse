# expect: 3:0: S has several values and is recursive, or called by a recursive one, and it is not <computes>: such a function must be <computes>, keep no local state, and reach nothing that prints or calls Err(), as all its values are computed at a call (#235), unless it is taken lazily
# (a choice after its call of itself: not taken lazily yet, #283)
S(N:int)<transacts>:int =
    if (N <= 0) then 0 else block:
        X := S(N - 1)
        Print("got {X}")
        X | X + N
Main()<transacts>:void =
    for (V := S(2)) { Print("v {V}") }
