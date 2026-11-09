# a generator with effects in its clauses, taken lazily in a for: they run as its values are taken, between the iterations (#246)
Upto(A:int, B:int)<transacts><decides>:int =
    A <= B
    Print("visit {A}")
    A | Upto[A + 1, B]
Main():void =
    R := for (X := Upto[1, 3]):
        Print("got {X}")
        X * 10
    if (A := R[0], B := R[2]) then Print("{R.Length} {A} {B}")
