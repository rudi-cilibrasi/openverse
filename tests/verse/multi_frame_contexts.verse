# (#283) Return frames in the other places that take a call's values: option{},
# not, or, nested for, a choice after the call in the for's clauses, a body
# that fails, named arguments and written types.
F(N:int)<transacts><decides>:int =
    N > 0
    Print("f {N}")
    F[N - 1] + 100 | N
Count(N:int)<transacts>:int =
    if (N <= 0) then 0 else (Count(N - 1) + 1 | N)
G(N:int, ?Step:int = 1)<transacts><decides>:int =
    N > 0
    Print("g {N}")
    X:int = G[N - Step, ?Step := Step] | N
    X * 10
Main()<transacts><decides>:void =
    O := option{F[3]}
    if (X := O?) then Print("got {X}")
    if (not F[0]) then Print("none")
    Y := F[2] or 99
    Print("{Y}")
    for (A := Count(1), B := Count(2), A < B) { Print("{A} {B}") }
    for (A := Count(1)):
        for (B := Count(1)) { Print("in {A}{B}") }
    for (V := Count(2), W := V | V * 10) { Print("{W}") }
    for (V := G[3, ?Step := 2]) { Print("g v {V}") }
    # (a body that fails stops the for, and Main with it, keeping what ran)
    for (V := F[2]):
        Print("body {V}")
        V > 100
