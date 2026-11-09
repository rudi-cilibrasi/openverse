# an effectful generator where the first success is taken, in a generic function (#246 step 2)
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
Pick(V:t where t:type):?t = if (X := Nat[0], X > 1) then option{V} else false
Main():void =
    if (S := Pick("s")?) then Print(S)
