# expect: the default of ?K of F uses itself
F(N:int,?K:int=F[N])<computes><decides>:int =
    N > 0
    N | F[N-1]
Main():void = if (X := F[1]) then Print("{X}")
