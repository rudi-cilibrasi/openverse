# a function value that does not change objects, through a <transacts> function type, in a generator's clause where the first success is taken (#246, review of #267)
Quiet(N:int)<computes>:int = N
Loud(N:int)<transacts>:int =
    Print("loud")
    N
Gen(F:type{_(:int)<transacts>:int}, N:int)<transacts><decides>:int =
    F(N) > 0
    N | Gen[F, N - 1]
Main():void =
    if (X := Gen[Quiet, 3], X < 2) then Print("first {X}")
