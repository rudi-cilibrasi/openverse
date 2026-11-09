# expect: 7:16: Nat has several values, is recursive and may print in its clauses, its conditions or the arguments of its calls of itself
# (#246) its clauses run once for the values its call leads to: in an if, what they print for values the if rejects would stay
Nat(N:int)<computes><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
Main():void =
    if (X := Nat[0], X > 2):
        Print("{X}")
