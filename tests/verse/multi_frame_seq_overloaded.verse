# (#283, #575) A generator that is one overload of its name, with choice
# points in sequence: the code after its first point is a continuation
# member, whose calls of the name each take the overload their arguments
# fit, the other overload too (a function of its group through them), and
# calls where the lifter takes a choice (a named argument, an if's branch).
Tw(A:int, ?B:int = 1):int = A * 10 + B
Down(N:int)<transacts>:int =
    if (N <= 0) then 0 else block:
        X := Down(N - 1) | N
        Print("x {N} {X}")
        Y := Down("{X}") + 1 | X * 10
        Y
Down(S:string)<transacts>:int =
    Print("s {S}")
    Down(S.Length - 3) | 100
Up(N:int)<transacts>:int =
    if (N <= 0) then 1 else block:
        X := Up(N - 1) | N
        Print("u {N} {X}")
        Tw(X, ?B := (if (N > 1) then Up(N - 1) else Up("{X}")))
Up(S:string)<transacts>:int = Up(S.Length - 3) + 2 | 7
Main()<transacts>:void =
    for (V := Down(2)) { Print("v {V}") }
    if (V := Down(2), V > 50) then Print("first {V}")
    for (V := Down("ab")) { Print("w {V}") }
    for (V := Up(2)) { Print("up {V}") }
    if (V := Up(2), V > 100) then Print("first {V}")
