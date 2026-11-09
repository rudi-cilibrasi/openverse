# an effectful generator in option{…} and not, and one in the clauses after another (#246 step 2)
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
Main():void =
    O := option{X := Nat[0]; X > 1; X}
    if (V := O?) then Print("opt {V}")
    if (X := Nat[0], Y := Nat[X], X + Y > 2) then Print("nested {X} {Y}")
    if (not Nat[0]) then Print("no") else Print("yes")
