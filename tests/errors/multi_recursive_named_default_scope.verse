# expect: unknown identifier 'Hidden'
F(N:int,?K:int=Hidden)<computes><decides>:int =
    N > 0
    N | F[N-1]
Main():void =
    Hidden := 7
    if (X := F[1]) then Print("{X}")
