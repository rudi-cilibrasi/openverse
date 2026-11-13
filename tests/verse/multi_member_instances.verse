# (#283) A generic function with several values that a lazily taken group's code calls at several
# instances of its type parameters in one search: each call at an instance other than the first
# calls a copy of it of its own, another member of the machine, at its instance; in both consumers,
# with effects, for callees whose code calls another generic one (itself at two instances then),
# recursive callees, generic methods and mutual groups.
Three(X:t where t:type)<transacts>:t =
    Print("three")
    X | X
Two(X:t, Y:t where t:type)<transacts>:t =
    Z := Three(X)
    Z | Y
T(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        S := Two("a", "bb")
        T(N - 1) + Two(N, 10) + S.Length
Pick(X:t, Y:t where t:type)<transacts>:t =
    Print("pick")
    X | Y
A(N:int)<transacts>:int =
    if (N <= 0) then 0 else B(N - 1) + Pick(N, 100)
B(N:int)<transacts>:int =
    if (N <= 0) then 1 else:
        S := Pick("x", "yy")
        A(N - 1) + S.Length
Rep(X:t, N:int where t:type)<transacts>:t =
    if (N <= 0) then X else (X | Rep(X, N - 1))
R(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        S := Rep("ab", 1)
        R(N - 1) + Rep(N, 1) * 10 + S.Length
box(t:type) := class:
    V:t
    Both(W:t)<transacts>:t = V | W
M(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        S := box(string){V := "a"}.Both("bbb")
        M(N - 1) + box(int){V := N}.Both(7) + S.Length
Pair(X:t, Y:t where t:type)<transacts>:t =
    Print("pair")
    X | Y
D(N:int)<transacts><decides>:int =
    N > 0
    S := Pair("x", "yy")
    L := Pair(true, false)
    X := D[N - 1] | 0
    Q := Pair(X, 100)
    if (L?) then Q + S.Length else Q
Main()<transacts>:void =
    for (V := T(1)) { Print("t {V}") }
    if (V := T(1), V > 11) then Print("first {V}")
    for (V := A(2)) { Print("a {V}") }
    for (V := R(1)) { Print("r {V}") }
    for (V := M(1)) { Print("m {V}") }
    for (V := D[1]) { Print("d {V}") }
    if (V := D[2], V > 102) then Print("first {V}")
