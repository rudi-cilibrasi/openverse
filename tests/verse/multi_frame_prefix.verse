# (#283) What an alternative reads before its call of itself that may not
# read the same after it (a constant, which runs code where it is read; a
# field; a call of a function; a block's clauses) is read once, before the
# call, with its arguments, and the code after the call uses that value.
K:int = (Print("k"); 1)
box := class:
    var N:int = 0
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
F(N:int)<transacts><decides>:int =
    N > 0
    K + F[N - 1] | N
G(B:box, N:int)<transacts><decides>:int =
    N > 0
    set B.N += 1
    B.N * 100 + G[B, N - 1] | Tell("t{N}", N) + G[B, N - 1] | block{ Y := Tell("y{N}", 5); Z := G[B, N - 1]; Y + Z } | N
Main()<transacts>:void =
    for (V := F[2]) { Print("f {V}") }
    if (V := F[2], V > 2) then Print("first {V}")
    B := box{}
    for (V := G[B, 2]) { Print("g {V}") }
    C := box{}
    if (V := G[C, 2], V > 300) then Print("never {V} {C.N}")
    if (V := G[C, 2], V > 100) then Print("first {V} {C.N}")
