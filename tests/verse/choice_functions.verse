# functions with several values (#235): inlined at each call, so their
# values are the caller's, in spatial order, with rollback of failed ones
Digit():int = 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
Twice(X:int):int = X | X * 2
Tell(S:string, V:int):int =
    Print(S)
    V
Pick(X:int):int =
    Y := Tell("pick", X) | X + 100
    Y * 10
Small():int = Digit() * 0 + (1 | 2)
Main():void =
    for (X := Digit(), Y := Digit(), X + Y = 9, X < Y) { Print("{X}{Y}") }
    for (V := Twice(3)) { Print("twice {V}") }
    for (V := Twice(1) + Twice(10)) { Print("sum {V}") }
    if (P := Pick(5), P > 100) then Print("pick {P}")
    Xs := for{Small()}
    Print("small {Xs.Length}")
    if (Q := first{Z := Twice(Tell("arg", 4)); Z > 5; Z}) then Print("first {Q}")
