# A lazy first-success helper captures a generic method's Self.
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
holder(t:type) := class:
    V:t
    Len:int = 2
    Get():?t = if (X := Nat[0], X > Len) then option{V} else false
Main():void =
    if (V := holder(string){V := "s"}.Get()?) then Print(V)
