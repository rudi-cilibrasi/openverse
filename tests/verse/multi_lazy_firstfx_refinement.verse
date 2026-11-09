# values of a generator returning a refinement type, where the first success is taken (#246 step 2, review)
small := type{X:int where 0 <= X, X <= 10}
G(N:int)<transacts><decides>:small =
    N < 4
    Print("at {N}")
    3 | G[N + 1]
Main():void =
    if (X := G[0], X > 2) then Print("x {X}")
