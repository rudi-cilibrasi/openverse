# expect: 8:5: K has several values and is called here at another instance of its type parameters than its machine takes it at in one search, and it is recursive with H: not supported yet (#283)
# (#283) A group's own function is taken at one instance of its type parameters for a whole
# search: a call of it at another is not given a copy of its own, as a callee's is.
Second(A:int, B:t where t:type):t = B
G(N:int)<transacts>:int = if (N <= 0) then 0 else H(N - 1) + 1
H(N:int)<transacts>:int =
    S := K(N, "s")
    K(N, 5) + S.Length
K(N:int, X:t where t:type)<transacts>:t = X | Second(G(N - 1), X)
Main()<transacts>:void =
    for (V := G(2)) { Print("v {V}") }
