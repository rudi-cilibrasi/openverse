# the same with implicit members, a var field set after the call (kept only for the attempt that succeeds), and Self written (#246 step 2, methods)
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
finder := class:
    Limit:int = 2
    var Hits:int = 0
    Big(X:int):logic = if (X > Limit) then true else false
    Find()<transacts>:int =
        if (X := Nat[0], set Hits += 1, Big(X)?, X > Self.Limit) then X else -1
Main():void =
    F := finder{}
    Print("{F.Find()} hits {F.Hits}")
