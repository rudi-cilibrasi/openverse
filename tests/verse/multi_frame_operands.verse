# (#283) Where a call of itself may be in an alternative with code after it:
# after literals and the function's own names, in an operation, a call's
# arguments, a tuple, an interpolation, a comparison or a block, its result's
# member; each value of the call runs the code after it.
Tw(A:int, B:int):int = A * 10 + B
G(N:int)<transacts><decides>:int =
    N > 0
    Y := N * 2
    Y + G[N - 1] | 3 * G[N - 1] | Tw(Y, G[N - 1]) | N
S(N:int)<transacts>:string =
    if (N <= 0) then "" else ("<{S(N - 1)}>" | "{N}")
P(N:int)<transacts>:tuple(int, int) =
    if (N <= 0) then (0, 0) else ((N, P(N - 1)(0)) | (N, N))
L(N:int)<transacts><decides>:int =
    N > 0
    block{ R := L[N - 1]; Print("b {N} {R}"); R + 1 } | (L[N - 1] > 1) | N
Arr(N:int)<transacts>:[]int =
    if (N <= 0) then array{0} else (Arr(N - 1) + array{N} | array{Arr(N - 1).Length})
Main()<transacts>:void =
    for (V := G[2]) { Print("g {V}") }
    for (V := S(2)) { Print("s {V}") }
    for (V := P(2)) { Print("p {V(0)} {V(1)}") }
    for (V := L[2]) { Print("l {V}") }
    for (V := Arr(2)) { Print("a {V.Length}") }
