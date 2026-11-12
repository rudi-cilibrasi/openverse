# (#283) Choice points in sequence: a choice of values of another type than the
# function's (strings in an int function) with a choice point after it; a call
# of itself in such a choice, whose code (an interpolation) gives that type;
# and a choice of strings in an expression, its frame plain code. In a for and
# where the first success is taken, with and without effects.
T(N:int)<transacts><decides>:int =
    N > 0
    S := "a" | "bb"
    Print("s {N} {S}")
    T[N - 1] + S.Length | N
P(N:int)<transacts><decides>:int =
    N > 0
    S := "a" | "bb"
    P[N - 1] + S.Length | N
U(N:int)<transacts>:int =
    if (N <= 0) then 1 else:
        S := "x{U(N - 1)}" | "yy"
        Print("u {N} {S}")
        S.Length + U(N - 1) | N
W(N:int)<transacts>:int =
    if (N <= 0) then 1 else (("a" | "bb").Length + W(N - 1) | N)
Main()<transacts>:void =
    for (V := T[2]) { Print("v {V}") }
    if (V := T[2], V > 2) then Print("first {V}")
    if (V := P[2], V > 2) then Print("first {V}")
    for (V := U(2)) { Print("w {V}") }
    if (V := U(2), V > 4) then Print("first {V}")
    for (V := W(2)) { Print("x {V}") }
