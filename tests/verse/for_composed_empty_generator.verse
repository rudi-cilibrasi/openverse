# (#761) A `for` with a composed choice: a choice with an alternative that
# has choices of its own, here an `if` that picks a branch with a choice.
# Its alternatives are taken in turn, each with the generators after the
# choice, and a row that reaches no body is undone back to the alternative
# or element it is in. `Inner` adds 100 and gives an element only for
# V = 1, so only the rows with V = 1 keep their 100. Each form is beside a
# control with the same rows from a written choice of values or an array,
# which followed that rule already.
Cell := class{var N:int = 0, var M:int = 0}
C(S:Cell)<transacts><decides>:void =
    S.N >= 0
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1} else array{}
# Rows 3, 5, 1: only the last reaches the body.
First(S:Cell)<transacts>:void =
    for (V := (if (C[S]) then (3 | 5) else 4) | 1, W : Inner(S, V)):
        Print("first {V} {W} {S.N}")
FirstControl(S:Cell)<transacts>:void =
    for (V := (3 | 5 | 1), W : Inner(S, V)):
        Print("first {V} {W} {S.N}")
Else(S:Cell)<transacts>:void =
    for (V := (if (S.N < 0) then 4 else (3 | 5)) | 1, W : Inner(S, V)):
        Print("else {V} {W} {S.N}")
Typed(S:Cell)<transacts>:void =
    for (V:int = (if (C[S]) then (3 | 5) else 4) | 1, W : Inner(S, V)):
        Print("typed {V} {W} {S.N}")
# Rows 1, 3, 1: the first commits 100, the row 3 is undone back to it, the
# last commits 200.
Last(S:Cell)<transacts>:void =
    for (V := 1 | (if (C[S]) then (3 | 1) else 4), W : Inner(S, V)):
        Print("last {V} {W} {S.N}")
LastControl(S:Cell)<transacts>:void =
    for (V := (1 | 3 | 1), W : Inner(S, V)):
        Print("last {V} {W} {S.N}")
# Both alternatives pick a branch: rows 3, 5, 1, 7.
Both(S:Cell)<transacts>:void =
    for (V := (if (C[S]) then (3 | 5) else 4) | (if (C[S]) then (1 | 7) else 4), W : Inner(S, V)):
        Print("both {V} {W} {S.N}")
BothControl(S:Cell)<transacts>:void =
    for (V := (3 | 5 | 1 | 7), W : Inner(S, V)):
        Print("both {V} {W} {S.N}")
# A choice inside an alternative's expression, inside another: rows 3, 5, 7, 1.
Deep(S:Cell)<transacts>:void =
    for (V := ((if (C[S]) then (3 | 5) else 4) + 0 | 7) * 1 | 1, W : Inner(S, V)):
        Print("deep {V} {W} {S.N}")
# What an alternative does before its own choice is undone with it when none
# of its values reaches the body: M is 10, from the second alternative alone.
Own(S:Cell)<transacts>:void =
    for (V := (set S.M += 1; if (C[S]) then (3 | 5) else 4) | (set S.M += 10; 1), W : Inner(S, V)):
        Print("own {V} {W} {S.N} {S.M}")
OwnControl(S:Cell)<transacts>:void =
    for (V := (set S.M += 1; 3) | (set S.M += 1; 5) | (set S.M += 10; 1), W : Inner(S, V)):
        Print("own {V} {W} {S.N} {S.M}")
# It is kept when one does: the row 1 commits M = 1 and N = 100, the row 3
# is undone back to that, and the second alternative's row 5 with its M.
Kept(S:Cell)<transacts>:void =
    for (V := (set S.M += 1; if (C[S]) then (1 | 3) else 4) | (set S.M += 10; 5), W : Inner(S, V)):
        Print("kept {V} {W} {S.N} {S.M}")
# After a generator: A = 0 has the rows 3, 1, 1 and A = 1 the rows 4, 1.
Outer(S:Cell)<transacts>:void =
    for (A : array{0, 1}, V := (if (A = 0) then (3 | 1) else 4) | 1, W : Inner(S, V)):
        Print("outer {A} {V} {W} {S.N}")
OuterControl(S:Cell)<transacts>:void =
    for (P : array{(0, 3), (0, 1), (0, 1), (1, 4), (1, 1)}, W : Inner(S, P(1))):
        Print("outer {P(0)} {P(1)} {W} {S.N}")
# The choice last, after a source that writes: V = 5 passes and keeps the
# source's 100; with no V that passes, the source's write is undone.
Filter(S:Cell)<transacts>:void =
    for (W : Inner(S, 1), V := (if (C[S]) then (3 | 5) else 4) | 1, V > 4):
        Print("filter {V} {W} {S.N}")
FilterControl(S:Cell)<transacts>:void =
    for (W : Inner(S, 1), V := (3 | 5 | 1), V > 4):
        Print("filter {V} {W} {S.N}")
None(S:Cell)<transacts>:void =
    for (W : Inner(S, 1), V := (if (C[S]) then (3 | 5) else 4) | 1, V > 9):
        Print("none {V} {W} {S.N}")
NoneControl(S:Cell)<transacts>:void =
    for (W : Inner(S, 1), V := (3 | 5 | 1), V > 9):
        Print("none {V} {W} {S.N}")
Run(Name:string, F(:Cell)<transacts>:void)<transacts>:void =
    S := Cell{}
    F(S)
    Print("{Name} state {S.N} {S.M}")
Main()<transacts>:void =
    Run("first", First)
    Run("first", FirstControl)
    Run("else", Else)
    Run("typed", Typed)
    Run("last", Last)
    Run("last", LastControl)
    Run("both", Both)
    Run("both", BothControl)
    Run("deep", Deep)
    Run("own", Own)
    Run("own", OwnControl)
    Run("kept", Kept)
    Run("outer", Outer)
    Run("outer", OuterControl)
    Run("filter", Filter)
    Run("filter", FilterControl)
    Run("none", None)
    Run("none", NoneControl)
