# (#283) An `if` in an expression with a call of the function in a branch is
# a choice point: its conditions run first (rolled back when they fail),
# then its branch's values each go to the code after it, one frame for all
# its branches. So is the right of `or` (its `if`'s else), an `if` without
# `else` as a statement, and one in a `set`'s value.
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
Nested(N:int)<transacts>:int =
    if (N <= 0) then 1 else block:
        X := (if (N > 2) then Nested(N - 1) else if (N > 1) then (Nested(N - 1) | 3) else 4)
        Print("x {N} {X}")
        X | N * 100
Bound(N:int)<transacts>:int =
    if (N <= 0) then 1 else block:
        X := (if (Y := Tell("y {N}", N), Y > 1) then Bound(Y - 1) * 10 else N)
        X | N
Text(N:int)<transacts>:int =
    if (N <= 0) then 1 else block:
        S := (if (N > 1) then "{Text(N - 1)}" else ("a" | "b"))
        S.Length + N | N * 100
Either(N:int)<transacts><decides>:int =
    N >= 0
    X := (N = 0 or Either[N - 1] > 1)
    Print("e {N} {X}")
    X + N | 100
Statement(N:int)<transacts>:int =
    if (N <= 0) then (1 | 2) else block:
        if (N > 1):
            Print("in {Statement(N - 1)}")
        N | N * 100
Setting(N:int)<transacts>:int =
    if (N <= 0) then (1 | 2) else block:
        var K:int = Tell("k {N}", 10)
        set K = (if (N > 1) then Setting(N - 1) else (11 | 100)) + K
        K | N * 100
Main()<transacts>:void =
    for (V := Nested(3)) { Print("nested {V}") }
    if (V := Nested(3), V > 150) then Print("first {V}")
    for (V := Bound(3)) { Print("bound {V}") }
    if (V := Bound(3), V > 15) then Print("first {V}")
    for (V := Text(2)) { Print("text {V}") }
    if (V := Text(2), V > 150) then Print("first {V}")
    for (V := Either[2]) { Print("either {V}") }
    if (V := Either[2], V > 3) then Print("first {V}")
    for (V := Statement(2)) { Print("statement {V}") }
    for (V := Setting(2)) { Print("setting {V}") }
    if (V := Setting(2), V > 200) then Print("first {V}")
