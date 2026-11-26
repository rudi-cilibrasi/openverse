# (#761) A `for` whose clause picks a branch (an `if`, a `case`, an `or`)
# or an alternative that is a call of a function with several values. The
# call is inlined into its branch's path of the for's search, so a row that
# reaches no body is undone back to the alternative or element it is in.
# `Inner` adds 100 and gives an element only for V = 1, so only the rows
# with V = 1 keep their 100. The controls have the same rows from a written
# choice of values or an array, which followed that rule already.
Cell := class{var N:int = 0}
C(S:Cell)<transacts><decides>:void =
    S.N >= 0
Big(S:Cell)<transacts><decides>:int =
    S.N > 5
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1} else array{}
Pair(S:Cell)<transacts>:int =
    3 | 1
Two(S:Cell)<transacts>:int =
    if (C[S]) then (3 | 1) else (4 | 1)
Mark(S:Cell)<transacts>:int =
    set S.N += 10
    5 | 1
# Rows 3, 1.
Then(S:Cell)<transacts>:void =
    for (V := if (C[S]) then Pair(S) else (4 | 1), W : Inner(S, V)):
        Print("then {V} {W} {S.N}")
Else(S:Cell)<transacts>:void =
    for (V := if (S.N < 0) then (4 | 1) else Pair(S), W : Inner(S, V)):
        Print("else {V} {W} {S.N}")
Both(S:Cell)<transacts>:void =
    for (V := if (C[S]) then Pair(S) else Pair(S), W : Inner(S, V)):
        Print("both {V} {W} {S.N}")
# The function called in the branch picks a branch itself.
Nested(S:Cell)<transacts>:void =
    for (V := if (C[S]) then Two(S) else (4 | 1), W : Inner(S, V)):
        Print("nested {V} {W} {S.N}")
# `Big[S]` fails, so the values are the call's.
Or(S:Cell)<transacts>:void =
    for (V := (Big[S] or Pair(S)), W : Inner(S, V)):
        Print("or {V} {W} {S.N}")
Case(S:Cell)<transacts>:void =
    for (V := case (S.N) { 0 => Pair(S), _ => (4 | 1) }, W : Inner(S, V)):
        Print("case {V} {W} {S.N}")
Control(S:Cell)<transacts>:void =
    for (V := (3 | 1), W : Inner(S, V)):
        Print("control {V} {W} {S.N}")
# The function writes before its values, rows 5 and 1: its 10 is kept with
# the row 1, which reaches the body, and the row 5 is undone back to it.
Written(S:Cell)<transacts>:void =
    for (V := if (C[S]) then Mark(S) else (4 | 1), W : Inner(S, V)):
        Print("written {V} {W} {S.N}")
WrittenControl(S:Cell)<transacts>:void =
    for ((set S.N += 10; true?), V := (5 | 1), W : Inner(S, V)):
        Print("written {V} {W} {S.N}")
# No row reaches the body: the function's write is undone too.
None(S:Cell)<transacts>:void =
    for (V := if (C[S]) then Mark(S) else (4 | 1), W : Inner(S, V + 10)):
        Print("none {V} {W} {S.N}")
NoneControl(S:Cell)<transacts>:void =
    for ((set S.N += 10; true?), V := (5 | 1), W : Inner(S, V + 10)):
        Print("none {V} {W} {S.N}")
# The call as an alternative of a choice: rows 3, 1, 7.
Alt(S:Cell)<transacts>:void =
    for (V := Pair(S) | 7, W : Inner(S, V)):
        Print("alt {V} {W} {S.N}")
AltControl(S:Cell)<transacts>:void =
    for (V := (3 | 1 | 7), W : Inner(S, V)):
        Print("alt {V} {W} {S.N}")
# Rows 7, then the function's 10 and its rows 5 and 1: the row 7 is undone,
# the 10 is kept with the row 1.
AltWritten(S:Cell)<transacts>:void =
    for (V := 7 | Mark(S), W : Inner(S, V)):
        Print("alt-written {V} {W} {S.N}")
# After a generator: A = 0 has the rows 3, 1 and A = 1 the rows 4, 1.
After(S:Cell)<transacts>:void =
    for (A : array{0, 1}, V := if (A = 0) then Pair(S) else (4 | 1), W : Inner(S, V)):
        Print("after {A} {V} {W} {S.N}")
AfterControl(S:Cell)<transacts>:void =
    for (P : array{(0, 3), (0, 1), (1, 4), (1, 1)}, W : Inner(S, P(1))):
        Print("after {P(0)} {P(1)} {W} {S.N}")
# A loop with a `return` of several values: the row 3 is undone, the row 1
# returns with N = 100.
Direct(S:Cell)<transacts>:int =
    for (V := if (C[S]) then Pair(S) else (4 | 1), W : Inner(S, V)):
        return (W + S.N) | (W + 1000 + S.N)
    0
DirectControl(S:Cell)<transacts>:int =
    for (V := (3 | 1), W : Inner(S, V)):
        return (W + S.N) | (W + 1000 + S.N)
    0
# The header is resumed after a body alternative falls through (#686): the
# row 3 is undone, the row 1 (N = 100) falls through with Y = 1 to the
# loop's end, 100; then its Y = 11 returns 111.
Resumed(S:Cell)<transacts>:int =
    for (V := if (C[S]) then Pair(S) else (4 | 1), W : Inner(S, V)):
        Y := W | W + 10
        if (Y > 10):
            return Y + S.N
        Print("advance {V} {Y} {S.N}")
    S.N
ResumedControl(S:Cell)<transacts>:int =
    for (V := (3 | 1), W : Inner(S, V)):
        Y := W | W + 10
        if (Y > 10):
            return Y + S.N
        Print("advance {V} {Y} {S.N}")
    S.N
Resumes(S:Cell)<transacts>:void =
    for (X := Resumed(S)):
        Print("resumes {X}")
ResumesControl(S:Cell)<transacts>:void =
    for (X := ResumedControl(S)):
        Print("resumes {X}")
Returns(S:Cell)<transacts>:void =
    for (X := Direct(S)):
        Print("returns {X}")
ReturnsControl(S:Cell)<transacts>:void =
    for (X := DirectControl(S)):
        Print("returns {X}")
Run(Name:string, F(:Cell)<transacts>:void)<transacts>:void =
    S := Cell{}
    F(S)
    Print("{Name} state {S.N}")
Main()<transacts>:void =
    Run("then", Then)
    Run("else", Else)
    Run("both", Both)
    Run("nested", Nested)
    Run("or", Or)
    Run("case", Case)
    Run("control", Control)
    Run("written", Written)
    Run("written", WrittenControl)
    Run("none", None)
    Run("none", NoneControl)
    Run("alt", Alt)
    Run("alt", AltControl)
    Run("alt-written", AltWritten)
    Run("after", After)
    Run("after", AfterControl)
    Run("returns", Returns)
    Run("returns", ReturnsControl)
    Run("resumes", Resumes)
    Run("resumes", ResumesControl)
