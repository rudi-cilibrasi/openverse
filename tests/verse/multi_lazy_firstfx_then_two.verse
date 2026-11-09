# two effectful generators, then a lazy one (#246 step 2, review)
G(N:int)<decides>:int =
    N >= 0
    Print("g {N}")
    N | G[N - 1]
H(N:int)<decides>:int =
    N >= 0
    N | H[N - 1]
Main():void =
    if (X := G[1], Y := G[1], Z := H[1], X + Y + Z = 0) then Print("x {X}")
