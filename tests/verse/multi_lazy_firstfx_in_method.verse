# an effectful generator where the first success is taken, in a method: the clauses after it read Self's fields and call its methods (#246 step 2, methods)
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
finder := class:
    Limit:int = 2
    Find():int = if (X := Nat[0], X > Limit) then X else -1
Main():void = Print("{finder{}.Find()}")
