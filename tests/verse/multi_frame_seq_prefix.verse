# (#283) Choice points in sequence: after a call of itself, a choice inside an
# expression whose code before it (a call that prints) runs once, before the
# choice, and a choice in the argument of a call of itself.
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
F(N:int)<transacts><decides>:int =
    N > 0
    X := F[N - 1] | N
    Y := Tell("t {N} {X}", X * 10) + (1 | 2)
    Print("y {Y}")
    Y
G(N:int)<transacts>:int =
    if (N <= 0) then 0 else (G(N - 1 | N - 2) + 1 | N)
Main()<transacts>:void =
    for (V := F[2]) { Print("v {V}") }
    if (V := F[2], V > 120) then Print("first {V}")
    for (V := G(2)) { Print("g {V}") }
