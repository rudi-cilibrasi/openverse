# (#283) A generic mutual group whose second member is called only from the
# code after a choice point in the first (a continuation member's code): its
# type instance is found there.
A(X:t, N:int where t:type)<transacts><decides>:t =
    N > 0
    Y := A[X, N - 1] | X
    Print("a {N}")
    B[Y, N - 1] | Y
B(V:u, M:int where u:type)<transacts><decides>:u =
    M >= 0
    V | A[V, M]
Main()<transacts>:void =
    for (Z := A["s", 2]) { Print("z {Z}") }
    if (Z := A[7, 2], Z > 6) then Print("first {Z}") else Print("none")
