# (#283) Consumers in a recursive group's own code, in the group's other
# forms: a mutual group; a generic function, whose condition binds a value of
# its type parameter; a method; named arguments; an overloaded function; a
# condition that takes another function's values; one in the code after a
# choice point, which takes a name it bound; and one that reads a var the
# code after a choice point sets, a cell.
Even(N:int)<transacts>:int =
    if (N <= 0) then (0 | 1) else:
        Print("even {N}")
        if (Odd(N - 1) > 2) then (N | 10 * N) else Odd(N - 1)
Odd(N:int)<transacts>:int =
    if (N <= 0) then 2 else Even(N - 1) + 1
Pick(N:int, A:t, B:t where t:type)<transacts>:t =
    if (N <= 0) then (A | B) else:
        Print("pick {N}")
        if (X := Pick(N - 1, A, B), N > 1) then (X | A) else B
walker := class:
    Base:int
    Walk(N:int)<transacts>:int =
        if (N <= 0) then (Base | Base + 1) else:
            Print("walk {N}")
            if (Walk(N - 1) > Base) then (N | Walk(N - 1)) else N
Step(N:int, ?By:int = 1)<transacts>:int =
    if (N <= 0) then (1 | 2) else:
        Print("step {N} {By}")
        if (Step(N - By, ?By := By) > 1) then (N | By) else 0
Over(N:int)<transacts>:int =
    if (N <= 0) then (1 | 2) else:
        Print("over {N}")
        if (Over(N - 1) > 1) then (N | 10) else 0
Over(S:string)<transacts>:string = S
Tell(N:int)<transacts>:int =
    Print("tell {N}")
    N
Two(N:int)<transacts>:int = Tell(N) | N + 5
Other(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        if (X := Two(N), X >= N) then (Other(N - 1) + X | X) else N
After(N:int)<transacts>:int =
    if (N <= 0) then (1 | 2) else:
        X := After(N - 1) | N
        Print("after {N} {X}")
        if (After(N - 1) > X) then X * 10 else X
Cell(N:int)<transacts>:int =
    if (N <= 0) then (1 | 2) else:
        var K:int = 0
        X := Cell(N - 1)
        set K += X
        if (Cell(N - 1) > K) { set K += 100 }
        K
Main()<transacts>:void =
    for (V := Even(4)) { Print("v {V}") }
    for (V := Odd(3)) { Print("v {V}") }
    if (V := Odd(3), V > 2) then Print("taken {V}")
    for (V := Pick(3, "x", "y")) { Print(V) }
    for (V := walker{Base := 5}.Walk(2)) { Print("v {V}") }
    for (V := Step(4, ?By := 2)) { Print("v {V}") }
    for (V := Step(2)) { Print("v {V}") }
    for (V := Over(2)) { Print("v {V}") }
    Print(Over("s"))
    for (V := Other(2)) { Print("v {V}") }
    if (V := Other(2), V < 3) then Print("taken {V}")
    for (V := After(2)) { Print("v {V}") }
    if (V := After(2), V > 15) then Print("taken {V}")
    for (V := Cell(2)) { Print("v {V}") }
    if (V := Cell(2), V < 150) then Print("taken {V}")
