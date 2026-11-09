# a var bound after an effectful generator, still a var in the then-branch (#246 step 2, review)
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
Main():void =
    if (X := Nat[0], var Z:int = X, X > 1):
        set Z += 10
        Print("x {X} z {Z}")
