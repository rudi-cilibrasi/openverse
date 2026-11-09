# generators consumed in generic functions: a for whose values are at a type parameter, nested, and an if (#246)
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
Pairs(X:t, N:int where t:type):[]tuple(t, int) =
    for (I := Upto[1, N]):
        (X, I)
Nested(X:t, N:int where t:type):[]t =
    for (I := Upto[1, N], J := Upto[I, N]):
        X
FirstOver(X:t, N:int where t:type):?t =
    if (I := Upto[1, 9], I > N) then option{X} else false
Main():void =
    P := Pairs("a", 3)
    Print("{P.Length}")
    for (Q : P) { Print("{Q(0)} {Q(1)}") }
    Print("{Nested(1.5, 3).Length}")
    if (V := FirstOver("z", 4)?) then Print(V)
