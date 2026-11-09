# the same followed by an eagerly computed recursive call (#246 step 2, review)
G(N:int)<decides>:int =
    N >= 0
    Print("g {N}")
    N | G[N - 1]
E(N:int)<computes><decides>:int =
    N >= 0
    N | E[N - 1] + 0
Main():void =
    if (X := G[1], Z := E[1], X + Z = 0) then Print("x {X}")
