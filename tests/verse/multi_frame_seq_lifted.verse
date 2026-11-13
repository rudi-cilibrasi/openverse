# (#283) Choice points in sequence where the lifter takes them: a call of
# itself in a named argument, a struct construction's field (evaluated in the
# struct's declaration order, not as written), a comparison's later operand,
# `and`'s operands, and a `set`'s value (its old value read before the call).
pt := struct:
    X:int = 0
    Y:int = 0
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
Tw(A:int, ?B:int = 1):int = A * 10 + B
Named(N:int)<transacts>:int =
    if (N <= 0) then 1 else (Tw(Tell("n {N}", 1), ?B := Named(N - 1)) | N)
Built(N:int)<transacts>:int =
    if (N <= 0) then 1 else block:
        P := pt{Y := Built(N - 1), X := Tell("x {N}", N)}
        P.X * 100 + P.Y | N
Compared(N:int)<transacts><decides>:int =
    if (N <= 0) then (1 | 7) else block:
        Y := Tell("c {N}", 5) > Compared[N - 1] > 0
        Y + N | N * 10
Both(N:int)<transacts><decides>:int =
    if (N <= 0) then (2 | 1) else block:
        X := (Compared[N - 1] > 1 and Tell("b {N}", N) > 0)
        X | N * 10
Added(N:int)<transacts>:int =
    if (N <= 0) then 1 else block:
        var K:int = 10
        set K += Added(N - 1)
        K | N
Main()<transacts>:void =
    for (V := Named(2)) { Print("named {V}") }
    if (V := Named(2), V > 15) then Print("first {V}")
    for (V := Built(2)) { Print("built {V}") }
    if (V := Built(2), V > 150) then Print("first {V}")
    for (V := Compared[1]) { Print("compared {V}") }
    if (V := Compared[1], V > 6) then Print("first {V}")
    for (V := Both[2]) { Print("both {V}") }
    if (V := Both[2], V > 2) then Print("first {V}")
    for (V := Added(2)) { Print("added {V}") }
    if (V := Added(2), V > 15) then Print("first {V}")
