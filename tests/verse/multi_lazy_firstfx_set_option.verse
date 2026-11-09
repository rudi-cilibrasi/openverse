# set O? = … of a var after an effectful generator, where the first success is taken: copied in and back (#246 step 2, review)
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
Main():void =
    var O:?int = option{0}
    if (X := Nat[0], set O? = X, X > 1) then Print("x {X}")
    if (Q := O?) then Print("o {Q}")
