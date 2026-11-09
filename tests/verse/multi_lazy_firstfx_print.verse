# a generator printing in its clauses, where the first success is taken: compiled as a function of its own, so only the calls on the way to the value taken print, as in the Verse Calculus (#246 step 2)
Nat(N:int)<computes><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
Main():void =
    if (X := Nat[0], X > 2):
        Print("{X}")
