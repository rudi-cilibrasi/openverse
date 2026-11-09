# an effectful generator followed by a lazily taken one, where the first success is taken: the clauses after the first, lifted already, are not lifted again in its function (#246 step 2, review)
G(N:int)<decides>:int =
    N >= 0
    Print("g {N}")
    N | G[N - 1]
H(N:int)<decides>:int =
    N >= 0
    N | H[N - 1]
Main():void =
    if (X := G[1], Z := H[1], X + Z = 0) then Print("x {X}")
