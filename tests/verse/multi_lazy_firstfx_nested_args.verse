# effectful generators in each other's arguments, in two clauses (#246 step 2, review)
G(N:int, A:int)<decides>:int =
    N >= 1
    Print("g {N}")
    A | G[N - 1, A]
Main():void =
    if (Y := G[1, G[1, 0]], X := G[1, G[1, 0] + 1]) then Print("x {X}")
