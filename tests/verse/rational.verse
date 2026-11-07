# rationals (#116): X / Y, int <: rational, Floor/Ceil, equality in lowest terms, exact ordering
Half(X:int)<decides>:rational = X / 2
Show(R:rational):string = "{Floor(R)}..{Ceil(R)}"
Main():void =
    if (R := 7 / 2):
        Print(Show(R))
    if (R := -7 / 2) then Print(Show(R))
    if (H := Half[9], H = 9 / 2) then Print("half equal")
    if (not (1 / 0 = 0)) then Print("div by zero fails")
    if (6 / 4 = 3 / 2) then Print("lowest terms")
    if (A := 1 / 3, B := 1 / 2, A < B, B > A, A <= A, A >= A, A <> B) then Print("ordered")
    if (2 / 1 = 2) then Print("int is rational")
    if (1 < 3 / 2, 3 / 2 < 2) then Print("between")
    if (1 / 3 < 1 / 2 < 2 / 3) then Print("chain")
    if (not (1 / 2 < 1 / 3)) then Print("not less")
    var V:rational = 1
    if (W := 5 / 3) then set V = W
    Print("{Floor(V)} {Ceil(V)} {Floor(4)}")
    X:rational = if (Y := 7 / 2) then Y else 3
    Print("{Floor(X)}")
    if (A := 9223372036854775807 / 3, B := 9223372036854775806 / 3, B < A) then Print("big ordered")
    if (A := 1 / 9223372036854775807, B := 1 / 9223372036854775806, A < B) then Print("tiny ordered")
