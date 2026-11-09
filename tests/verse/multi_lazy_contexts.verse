# a generator's first value taken lazily in option{…}, not and the left of or (#246)
Nat(N:int)<computes><decides>:int = N | Nat[N + 1]
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
Main():void =
    if (O := option{Nat[5]}, V := O?) then Print("opt {V}")
    if (not Upto[3, 1]) then Print("none")
    if (not Upto[1, 3]) then Print("wrong") else Print("some")
    X := Upto[4, 2] or 99
    Print("or {X}")
    Y := Upto[4, 6] or 99
    Print("or {Y}")
