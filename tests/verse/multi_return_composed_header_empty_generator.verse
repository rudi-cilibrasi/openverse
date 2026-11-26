# (#761) A loop with a `return` of several values whose header has a
# composed choice (an alternative that picks a branch with a choice) before
# a generator whose source writes. A row whose generator is empty reaches no
# body, so what its source wrote is undone, also when a body alternative
# falls through and the header is resumed (#686). The controls have the same
# rows from a written choice of values.
Cell := class{var N:int = 0}
C(S:Cell)<transacts><decides>:void =
    S.N >= 0
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1} else array{}
# The rows 3 and 5 are undone; the row 1 returns with N = 100.
Direct(S:Cell)<transacts>:int =
    for (V := (if (C[S]) then (3 | 5) else 4) | 1, W : Inner(S, V)):
        return (W + S.N) | (W + 1000 + S.N)
    0
DirectControl(S:Cell)<transacts>:int =
    for (V := (3 | 5 | 1), W : Inner(S, V)):
        return (W + S.N) | (W + 1000 + S.N)
    0
# Rows 3 and 5 are undone. Row 1 (N = 100) falls through with Y = 1 to the
# second row 1 (N = 200), which falls through to the loop's end, 200; then
# its Y = 11 returns 211, and the first row's Y = 11 returns 211.
Resumed(S:Cell)<transacts>:int =
    for (V := (if (C[S]) then (3 | 1 | 5) else 4) | 1, W : Inner(S, V)):
        Y := W | W + 10
        if (Y > 10):
            return Y + S.N
        Print("advance {V} {Y} {S.N}")
    S.N
ResumedControl(S:Cell)<transacts>:int =
    for (V := (3 | 1 | 5 | 1), W : Inner(S, V)):
        Y := W | W + 10
        if (Y > 10):
            return Y + S.N
        Print("advance {V} {Y} {S.N}")
    S.N
Main()<transacts>:void =
    A := Cell{}
    for (X := Direct(A)):
        Print("direct {X}")
    Print("direct state {A.N}")
    B := Cell{}
    for (X := DirectControl(B)):
        Print("direct {X}")
    Print("direct state {B.N}")
    D := Cell{}
    for (X := Resumed(D)):
        Print("resumed {X}")
    Print("resumed state {D.N}")
    E := Cell{}
    for (X := ResumedControl(E)):
        Print("resumed {X}")
    Print("resumed state {E.N}")
