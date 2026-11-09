# a generator with infinitely many values, taken lazily in an if: it stops at the first value the if's clauses accept (#246)
Nat(N:int)<computes><decides>:int = N | Nat[N + 1]
Main():void =
    if (X := Nat[0], X > 5):
        Print("{X}")
    if (X := Nat[3], Y := X * X, Y > 50):
        Print("{X} {Y}")
