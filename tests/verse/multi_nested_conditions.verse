# (#283) A call of a recursive function with several values in a condition of
# its own code (an if's, not's, the left of or, option{}, logic{}, first{}) is
# a consumer like any other: it takes the first success of that call, whose
# own code takes its own in turn, while the outer call's values are taken.
# What a rejected attempt does is undone; the succeeding one's code stays.
Cond(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        Print("cond {N}")
        if (Cond(N - 1) > 0) then (N | 10 * N) else (N | 100 * N)
Not(N:int)<transacts><decides>:int =
    N >= 0
    Print("not {N}")
    not Not[N - 2]
    N | N + 10
Or(N:int)<transacts><decides>:int =
    N >= 0
    Print("or {N}")
    (Or[N - 1] > 5 or N = 1)
    N | N + 10
Rec(N:int)<transacts><decides>:int =
    N > 0
    Print("rec {N}")
    if (Rec[N - 1] > 1) then (N | Rec[N - 1]) else N
Binds(N:int)<transacts>:int =
    if (N <= 0) then (1 | 2) else:
        var K:int = 0
        if (X := Binds(N - 1), set K += X, Print("binds {N} {X}"), X > 1) then (K + 10 * N | K) else K
Opt(N:int)<transacts>:int =
    if (N <= 0) then (3 | 4) else:
        O := option{Opt(N - 1) > 3}
        L := logic{Opt(N - 1) > 10}
        Print("opt {N} {if (V := O?) then V else -1} {if (L?) then 1 else 0}")
        (if (V := O?) then V else 0) | N
First(N:int)<transacts><decides>:int =
    if (N <= 0) then (1 | 2 | 3) else:
        F := first{X := First[N - 1]; X > 1; X * 10}
        Print("first {N} {F}")
        F | N
Main()<transacts>:void =
    for (V := Cond(2)) { Print("v {V}") }
    if (V := Cond(2), V > 15) then Print("taken {V}")
    for (V := Not[1]) { Print("v {V}") }
    if (V := Not[1], V > 5) then Print("taken {V}")
    for (V := Not[2]) { Print("v {V}") }
    for (V := Or[2]) { Print("v {V}") }
    if (V := Or[2], V > 5) then Print("taken {V}")
    for (V := Rec[3]) { Print("v {V}") }
    if (V := Rec[3], V < 3) then Print("taken {V}")
    for (V := Binds(2)) { Print("v {V}") }
    if (V := Binds(2), V < 20) then Print("taken {V}")
    for (V := Opt(2)) { Print("v {V}") }
    for (V := First[2]) { Print("v {V}") }
    if (V := First[2], V < 100) then Print("taken {V}")
