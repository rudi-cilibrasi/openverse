# (#761) A `for` whose search has more than eight levels follows the same
# rule as a shorter one: a row that reaches no body is undone with what its
# sources wrote. Before, such a header kept the older lowering, where the
# writes of the row V = 3 stayed, so what a `for` meant depended on its size.
# Each shape runs beside a control with the same rows from a written choice,
# which was searched at any size.
Cell := class{var N:int = 0}
C(S:Cell)<transacts><decides>:void =
    S.N >= 0
# One element, and a write for the row to undo.
One(S:Cell, V:int)<transacts>:[]int =
    set S.N += 1
    array{V}
# An element only for V = 1.
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1} else array{}
# Nine levels: the choice of the picked branch, then eight generators.
Nine(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), A : One(S, V), B : One(S, A), D : One(S, B), E : One(S, D), F : One(S, E), G : One(S, F), H : One(S, G), W : Inner(S, H)):
        Print("nine {V} {W} {S.N}")
NineControl(S:Cell)<transacts>:void =
    for (V := (3 | 1), A : One(S, V), B : One(S, A), D : One(S, B), E : One(S, D), F : One(S, E), G : One(S, F), H : One(S, G), W : Inner(S, H)):
        Print("nine-control {V} {W} {S.N}")
# Eight levels, the most the search had before: unchanged.
Eight(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), A : One(S, V), B : One(S, A), D : One(S, B), E : One(S, D), F : One(S, E), G : One(S, F), W : Inner(S, G)):
        Print("eight {V} {W} {S.N}")
# The empty row in the middle of twelve levels, and a row that fails a filter
# after the last generator.
Twelve(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), A : One(S, V), B : One(S, A), D : One(S, B), E : One(S, D), W : Inner(S, E), F : One(S, W), G : One(S, F), H : One(S, G), I : One(S, H), J : One(S, I), K := (5 | 6), K + J > 6):
        Print("twelve {V} {W} {K} {S.N}")
TwelveControl(S:Cell)<transacts>:void =
    for (V := (3 | 1), A : One(S, V), B : One(S, A), D : One(S, B), E : One(S, D), W : Inner(S, E), F : One(S, W), G : One(S, F), H : One(S, G), I : One(S, H), J : One(S, I), K := (5 | 6), K + J > 6):
        Print("twelve-control {V} {W} {K} {S.N}")
# A function with many guarded returns, each a choice, taken by a `for`: its
# guards are exclusive choices one after another, a level each.
Pick(S:Cell, N:int)<transacts>:int =
    if (N = 0):
        set S.N += 1000
        return 3 | 1
    if (N = 1):
        set S.N += 1000
        return 3 | 1
    if (N = 2):
        set S.N += 1000
        return 3 | 1
    if (N = 3):
        set S.N += 1000
        return 3 | 1
    if (N = 4):
        set S.N += 1000
        return 3 | 1
    if (N = 5):
        set S.N += 1000
        return 3 | 1
    if (N = 6):
        set S.N += 1000
        return 3 | 1
    if (N = 7):
        set S.N += 1000
        return 3 | 1
    if (N = 8):
        set S.N += 1000
        return 3 | 1
    if (N = 9):
        set S.N += 1000
        return 3 | 1
    if (N = 10):
        set S.N += 1000
        return 3 | 1
    if (N = 11):
        set S.N += 1000
        return 3 | 1
    if (N = 12):
        set S.N += 1000
        return 3 | 1
    if (N = 13):
        set S.N += 1000
        return 3 | 1
    if (N = 14):
        set S.N += 1000
        return 3 | 1
    if (N = 15):
        set S.N += 1000
        return 3 | 1
    if (N = 16):
        set S.N += 1000
        return 3 | 1
    if (N = 17):
        set S.N += 1000
        return 3 | 1
    if (N = 18):
        set S.N += 1000
        return 3 | 1
    if (N = 19):
        set S.N += 1000
        return 3 | 1
    4 | 1
Guards(S:Cell)<transacts>:void =
    for (V := Pick(S, 19), W : Inner(S, V)):
        Print("guards {V} {W} {S.N}")
GuardsLast(S:Cell)<transacts>:void =
    for (V := Pick(S, 20), W : Inner(S, V)):
        Print("guards-last {V} {W} {S.N}")
# No row reaches the body: nothing of the header is kept.
GuardsNone(S:Cell)<transacts>:void =
    for (V := Pick(S, 7), V > 3, W : Inner(S, V)):
        Print("guards-none {V} {W} {S.N}")
Run(Name:string, F(:Cell)<transacts>:void)<transacts>:void =
    S := Cell{}
    F(S)
    Print("{Name} state {S.N}")
Main()<transacts>:void =
    Run("nine", Nine)
    Run("nine-control", NineControl)
    Run("eight", Eight)
    Run("twelve", Twelve)
    Run("twelve-control", TwelveControl)
    Run("guards", Guards)
    Run("guards-last", GuardsLast)
    Run("guards-none", GuardsNone)
