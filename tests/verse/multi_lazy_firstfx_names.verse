# the clauses after an effectful generator use and set the consumer's names: read, and a var set only for the attempt that succeeds; a name they bind is seen after (#246 step 2)
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
Main():void =
    Limit := 2
    var T:int = 0
    if (X := Nat[0], set T += 10, Y := X * 2, X > Limit) then Print("x {X} y {Y} t {T}")
