# (#283) A call of a recursive function with several values in a field of a
# generic struct's construction is a choice point there, in the struct's
# declaration order (a computed default before it runs first, once), as in a
# non-generic struct's: the construction names its type arguments.
pair(t:type) := struct:
    C:int = Count(7)
    B:t
    A:t
Count(N:int)<transacts>:int =
    Print("count {N}")
    N
Build(N:int, X:t where t:type)<transacts>:pair(t) =
    if (N <= 0) then (pair(t){A := X, B := X, C := 1} | pair(t){B := X, A := X, C := 2}) else:
        Print("build {N}")
        P := pair(t){A := Build(N - 1, X).A, B := X}
        P
Sum(N:int)<transacts>:int =
    if (N <= 0) then (0 | 1) else:
        Print("sum {N}")
        O := pair(int){A := Sum(N - 1), B := N, C := 3}
        O.A + 10 * O.B + 100 * O.C
Main()<transacts>:void =
    for (V := Build(2, "s")) { Print("v {V.A} {V.C}") }
    for (V := Sum(2)) { Print("v {V}") }
    if (V := Sum(2), V > 330) then Print("taken {V}")
