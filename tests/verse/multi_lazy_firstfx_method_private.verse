# the same with private members (#246 step 2, methods)
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
finder := class:
    Limit<private>:int = 2
    Helper<private>(X:int):int = X * 2
    Find():int = if (X := Nat[0], Helper(X) > Limit) then X else -1
Main():void = Print("{finder{}.Find()}")
