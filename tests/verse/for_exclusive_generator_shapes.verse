# (#759) The shapes around a `for` clause that picks a branch with a choice:
# the generator after it over a map, a string, a range with a bound that
# writes, a second generator, a filter after the generator, the choice after
# another generator, two such choices, an `or` with a choice on its right, a
# condition that writes when no row reaches the body, a loop inside a loop
# and a body with a `defer:`. A row that reaches no body is undone with what
# its sources wrote; when no row at all reaches the body, what the condition
# wrote is undone too. Each shape runs twice: with the `if`, and as a control
# with the same rows from a written choice, which printed this before.
Cell := class{var N:int = 0}
C(S:Cell)<transacts><decides>:void =
    S.N >= 0
Bump(S:Cell)<transacts><decides>:void =
    set S.N += 1000
    S.N >= 0
Miss(S:Cell)<transacts><decides>:int =
    set S.N += 1000
    S.N < 0
    7
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1} else array{}
InnerM(S:Cell, V:int)<transacts>:[int]int =
    set S.N += 100
    if (V = 1) then map{7 => 1} else map{}
InnerS(S:Cell, V:int)<transacts>:string =
    set S.N += 100
    if (V = 1) then "a" else ""
Run(Name:string, F(:Cell)<transacts>:void)<transacts>:void =
    S := Cell{}
    F(S)
    Print("{Name} state {S.N}")
MapIf(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), K -> W : InnerM(S, V)):
        Print("map-if {V} {K} {W} {S.N}")
MapControl(S:Cell)<transacts>:void =
    for (V := (3 | 1), K -> W : InnerM(S, V)):
        Print("map-control {V} {K} {W} {S.N}")
StringIf(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), W : InnerS(S, V)):
        Print("string-if {V} {S.N}")
StringControl(S:Cell)<transacts>:void =
    for (V := (3 | 1), W : InnerS(S, V)):
        Print("string-control {V} {S.N}")
SecondIf(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), W : array{1, 2}, X : Inner(S, V)):
        Print("second-if {V} {W} {X} {S.N}")
SecondControl(S:Cell)<transacts>:void =
    for (V := (3 | 1), W : array{1, 2}, X : Inner(S, V)):
        Print("second-control {V} {W} {X} {S.N}")
FilterIf(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), W : Inner(S, 1), W = V):
        Print("filter-if {V} {W} {S.N}")
FilterControl(S:Cell)<transacts>:void =
    for (V := (3 | 1), W : Inner(S, 1), W = V):
        Print("filter-control {V} {W} {S.N}")
RangeIf(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), W := 1..Inner(S, V).Length):
        Print("range-if {V} {W} {S.N}")
RangeControl(S:Cell)<transacts>:void =
    for (V := (3 | 1), W := 1..Inner(S, V).Length):
        Print("range-control {V} {W} {S.N}")
AfterIf(S:Cell)<transacts>:void =
    for (U : array{1, 2}, V := if (C[S]) then (3 | 1) else (4 | 1), W : Inner(S, V)):
        Print("after-if {U} {V} {W} {S.N}")
AfterControl(S:Cell)<transacts>:void =
    for (U : array{1, 2}, V := (3 | 1), W : Inner(S, V)):
        Print("after-control {U} {V} {W} {S.N}")
TwoIf(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), U := if (V = 1) then (10 | 20) else (30 | 40), W : Inner(S, V)):
        Print("two-if {V} {U} {W} {S.N}")
TwoControl(S:Cell)<transacts>:void =
    for (V := (3 | 1), U := (V * 10 | V * 10 + 10), W : Inner(S, V)):
        Print("two-control {V} {U} {W} {S.N}")
KeptIf(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (1 | 3) else (4 | 1), W : Inner(S, V)):
        Print("kept-if {V} {W} {S.N}")
KeptControl(S:Cell)<transacts>:void =
    for (V := (1 | 3), W : Inner(S, V)):
        Print("kept-control {V} {W} {S.N}")
NoneIf(S:Cell)<transacts>:void =
    for (V := if (Bump[S]) then (3 | 5) else (4 | 1), W : Inner(S, V)):
        Print("none-if {V} {W} {S.N}")
NoneControl(S:Cell)<transacts>:void =
    for (Bump[S], V := (3 | 5), W : Inner(S, V)):
        Print("none-control {V} {W} {S.N}")
SomeIf(S:Cell)<transacts>:void =
    for (V := if (Bump[S]) then (3 | 1) else (4 | 1), W : Inner(S, V)):
        Print("some-if {V} {W} {S.N}")
SomeControl(S:Cell)<transacts>:void =
    for (Bump[S], V := (3 | 1), W : Inner(S, V)):
        Print("some-control {V} {W} {S.N}")
OrIf(S:Cell)<transacts>:void =
    for (V := Miss[S] or (3 | 1), W : Inner(S, V)):
        Print("or-if {V} {W} {S.N}")
OrControl(S:Cell)<transacts>:void =
    for (V := (3 | 1), W : Inner(S, V)):
        Print("or-control {V} {W} {S.N}")
NestedIf(S:Cell)<transacts>:void =
    for (U : array{1, 2}):
        for (V := if (C[S]) then (3 | 1) else (4 | 1), W : Inner(S, V)):
            Print("nested-if {U} {V} {W} {S.N}")
NestedControl(S:Cell)<transacts>:void =
    for (U : array{1, 2}):
        for (V := (3 | 1), W : Inner(S, V)):
            Print("nested-control {U} {V} {W} {S.N}")
DeferIf(S:Cell)<transacts>:void =
    Xs := for (V := if (C[S]) then (3 | 1) else (4 | 1), W : Inner(S, V)):
        defer:
            Print("defer-if leaves {S.N}")
        Print("defer-if {V} {W} {S.N}")
        V * 10 + W
    Print("defer-if values {Xs.Length}")
DeferControl(S:Cell)<transacts>:void =
    Xs := for (V := (3 | 1), W : Inner(S, V)):
        defer:
            Print("defer-control leaves {S.N}")
        Print("defer-control {V} {W} {S.N}")
        V * 10 + W
    Print("defer-control values {Xs.Length}")
Main()<transacts>:void =
    Run("map-if", MapIf)
    Run("map-control", MapControl)
    Run("string-if", StringIf)
    Run("string-control", StringControl)
    Run("second-if", SecondIf)
    Run("second-control", SecondControl)
    Run("filter-if", FilterIf)
    Run("filter-control", FilterControl)
    Run("range-if", RangeIf)
    Run("range-control", RangeControl)
    Run("after-if", AfterIf)
    Run("after-control", AfterControl)
    Run("two-if", TwoIf)
    Run("two-control", TwoControl)
    Run("kept-if", KeptIf)
    Run("kept-control", KeptControl)
    Run("none-if", NoneIf)
    Run("none-control", NoneControl)
    Run("some-if", SomeIf)
    Run("some-control", SomeControl)
    Run("or-if", OrIf)
    Run("or-control", OrControl)
    Run("nested-if", NestedIf)
    Run("nested-control", NestedControl)
    Run("defer-if", DeferIf)
    Run("defer-control", DeferControl)
