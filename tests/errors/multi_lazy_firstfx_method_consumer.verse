# expect: 8:29: Nat has several values, is recursive and may print in its clauses
# (#246 step 2) in a method, the function of its own a call where the first success is taken would be compiled as is not supported yet
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
finder := class:
    Limit:int = 2
    Find():int = if (X := Nat[0], X > Limit) then X else -1
Main():void = Print("{finder{}.Find()}")
