# expect: it may print
Tell(N:int)<computes>:int =
    Print("default {N}")
    N
F(N:int,?K:int=Tell(N))<computes>:int =
    if (N>0) then (N + F(N-1) | K) else 0
Main():void = for (X := F(2)): Print("{X}")
