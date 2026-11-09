# an effectful generator where the first success is taken, in a function inlined at two sites: a function of its own for each (#246 step 2, review)
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
Big(L:int)<transacts><decides>:int =
    X := Nat[0]
    X > L
    X
Main():void =
    if (A := Big[1]) then Print("a {A}")
    if (B := Big[2]) then Print("b {B}")
