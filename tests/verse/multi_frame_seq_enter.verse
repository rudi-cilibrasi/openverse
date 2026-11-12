# (#283) Choice points in sequence: an alternative, one of several, with code
# before a choice in it (a call that prints): that code runs each time the
# alternative is taken, before its choice, and where the first success is
# taken it is undone with the path that leads to no success. And one whose
# code before its choice has no effects (`Tw`), taken by the lazy loop itself.
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
G(N:int)<transacts>:int =
    if (N <= 0) then 0 else (Tell("g {N}", N) + (G(N - 1) | 5) | N * 100)
H(N:int)<transacts><decides>:int =
    N > 0
    X := H[N - 1] | Tell("h {N}", 10) + (1 | 2) | N
    X + 1
Tw(A:int, B:int)<computes>:int = A * 10 + B
P(N:int)<transacts>:int =
    if (N <= 0) then 0 else (P(N - 1) | Tw(1, N) + (P(N - 1) | 3))
Main()<transacts>:void =
    for (V := G(2)) { Print("w {V}") }
    if (V := G(2), V > 100) then Print("first {V}")
    for (V := H[2]) { Print("v {V}") }
    if (V := H[2], V > 12) then Print("first {V}")
    for (V := P(2)) { Print("p {V}") }
    if (V := P(2), V > 20) then Print("first {V}")
