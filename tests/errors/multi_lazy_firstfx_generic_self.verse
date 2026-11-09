# expect: 9:27: Nat has several values, is recursive and may print in its clauses
# (#246 step 2) in a generic class's method, the clauses after the call use Self, whose type has its type parameters
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
holder(t:type) := class:
    V:t
    Len:int = 2
    Get():?t = if (X := Nat[0], X > Len) then option{V} else false
Main():void =
    if (V := holder(string){V := "s"}.Get()?) then Print(V)
