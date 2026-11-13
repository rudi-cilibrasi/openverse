# (#283) A for over a call of a recursive function with several values in the
# function's own code is a consumer like any other: it takes all the call's
# values while the outer call's are being taken, the call's code taking its
# own in turn, and keeps what each iteration does. Its value may be used, its
# body may set the function's vars or fail (which fails the for, as
# anywhere), and a condition in a for's body that takes the call's first
# success moves with it.
Sum(N:int)<transacts>:int =
    if (N <= 0) then 1 else:
        var S:int = 0
        for (X := Sum(N - 1)) { set S += X }
        Print("sum {N} {S}")
        S | S + 1
Count(N:int)<transacts>:int =
    if (N <= 0) then (1 | 2) else:
        S := for (X := Count(N - 1), X > 1) { X * 10 }
        Print("count {N} {S.Length}")
        S.Length | N
Body(N:int)<transacts>:int =
    if (N <= 0) then (1 | 2) else:
        var C:int = 0
        for (I := 1..N) { if (Body(N - 1) >= I) { set C += 1 } }
        Print("body {N} {C}")
        C | N
Pure(N:int)<computes>:int =
    if (N <= 0) then (1 | 2) else:
        var S:int = 0
        for (X := Pure(N - 1)) { set S += X }
        S | S * 10
Each(N:int)<transacts><decides>:int =
    N >= 0
    X := 1 | 2
    for (Y := Each[N - 1]) { Print("each {N} {X} {Y}") }
    X * 10 + N
Fails(N:int)<transacts><decides>:int =
    Print("fails {N}")
    if (N <= 0) then (1 | 2) else:
        for (Y := Fails[N - 1]) { Y < 3 * N }
        N | N * 10
Main()<transacts>:void =
    for (V := Sum(2)) { Print("v {V}") }
    if (V := Sum(2), V > 3) then Print("taken {V}")
    for (V := Count(2)) { Print("v {V}") }
    if (V := Count(2), V > 0) then Print("taken {V}")
    for (V := Body(2)) { Print("v {V}") }
    if (V := Body(2), V > 1) then Print("taken {V}")
    for (V := Pure(2)) { Print("v {V}") }
    for (V := Each[1]) { Print("v {V}") }
    if (V := Each[1], V > 15) then Print("taken {V}")
    for (V := Fails[3]) { Print("v {V}") }
    if (V := Fails[1], V > 5) then Print("taken {V}")
    if (V := Fails[2]) then Print("taken {V}") else Print("none")
