# the same in a function with several values inlined at two consumers that are fors (#246 step 2, review)
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
H(M:int)<transacts><decides>:int =
    if (X := Nat[0], X > M) then Print("h {X}")
    M | M + 10
Main():void =
    for (A := H[1]) { Print("a {A}") }
    for (A := H[2]) { Print("a {A}") }
