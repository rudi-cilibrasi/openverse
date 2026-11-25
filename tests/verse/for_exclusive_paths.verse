# (#759) The paths of an `if` that picks a branch with a choice, in a `for`
# after another generator: a clause between the `if` and the next generator,
# a branch without a choice beside one with, an `if` inside a branch, a
# branch with two choices one after the other, and several rows under the
# generator after the choice. A row whose last generator is empty reaches
# no body and is undone with what its sources and filters wrote; a row that
# reaches the body keeps it. Each shape runs twice: with the `if`, and as a
# control with the same rows from written choices and a filter.
Cell := class{var N:int = 0}
C(S:Cell)<transacts><decides>:void =
    S.N >= 0
Tick(S:Cell)<transacts><decides>:void =
    set S.N += 1
    S.N >= 0
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1} else array{}
Both(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1, 2} else array{}
Run(Name:string, F(:Cell)<transacts>:void)<transacts>:void =
    S := Cell{}
    F(S)
    Print("{Name} state {S.N}")
BetweenIf(S:Cell)<transacts>:void =
    for (U : array{1, 2}, V := if (U = 1) then (3 | 1) else (4 | 1), Tick[S], W : Inner(S, V)):
        Print("between-if {U} {V} {W} {S.N}")
BetweenControl(S:Cell)<transacts>:void =
    for (U : array{1, 2}, V := (if (U = 1) then 3 else 4) | 1, Tick[S], W : Inner(S, V)):
        Print("between-control {U} {V} {W} {S.N}")
ScalarIf(S:Cell)<transacts>:void =
    for (U : array{1, 2}, V := if (U = 1) then (3 | 1) else 1, W : Inner(S, V)):
        Print("scalar-if {U} {V} {W} {S.N}")
ScalarControl(S:Cell)<transacts>:void =
    for (U : array{1, 2}, V := (3 | 1), (U = 1 or V = 1), W : Inner(S, V)):
        Print("scalar-control {U} {V} {W} {S.N}")
InsideIf(S:Cell)<transacts>:void =
    for (U : array{1, 2, 3}, V := if (U < 3) then (if (U = 1) then (3 | 1) else (5 | 1)) else (4 | 1), W : Inner(S, V)):
        Print("inside-if {U} {V} {W} {S.N}")
InsideControl(S:Cell)<transacts>:void =
    for (U : array{1, 2, 3}, V := (if (U = 1) then 3 else if (U = 2) then 5 else 4) | 1, W : Inner(S, V)):
        Print("inside-control {U} {V} {W} {S.N}")
TwoIf(S:Cell)<transacts>:void =
    for (U : array{1, 2}, V := if (U = 1) then block{X := (3 | 1); X | X + 10} else 1, W : Inner(S, V)):
        Print("two-if {U} {V} {W} {S.N}")
TwoControl(S:Cell)<transacts>:void =
    for (U : array{1, 2}, X := (3 | 1), V := (X | X + 10), (U = 1 or V = 1), W : Inner(S, V)):
        Print("two-control {U} {V} {W} {S.N}")
RowsIf(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1 | 1) else (4 | 1), W : Both(S, V)):
        Print("rows-if {V} {W} {S.N}")
RowsControl(S:Cell)<transacts>:void =
    for (V := (3 | 1 | 1), W : Both(S, V)):
        Print("rows-control {V} {W} {S.N}")
Main()<transacts>:void =
    Run("between-if", BetweenIf)
    Run("between-control", BetweenControl)
    Run("scalar-if", ScalarIf)
    Run("scalar-control", ScalarControl)
    Run("inside-if", InsideIf)
    Run("inside-control", InsideControl)
    Run("two-if", TwoIf)
    Run("two-control", TwoControl)
    Run("rows-if", RowsIf)
    Run("rows-control", RowsControl)
