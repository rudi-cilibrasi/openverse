# Generators in first, as in for (Book of Verse ch. 7, "first"; its tests,
# FlowControl/first.versetest): X : Xs, I -> X : Xs and X := a..b; the first
# iteration whose clauses succeed gives the body; a failed one is undone
# (FirstPos2: one Inc kept). A range binding may state its type, int
# (for.versetest:17, Exercises/TwoSum.versetest:20).
F(X:int, Xs:[]int)<decides>:int = first(I->Y:Xs; X = Y){I}
G(Xs:[]int)<decides>:int = first{X:Xs; X > 2}
value := class:
    var V:int = 0
    Inc()<decides><transacts>:int =
        set V += 1
FirstPos2(X:int, Xs:[]int):tuple(int, int) =
    W : value = value{}
    if (Z := first(I->Y:Xs; W.Inc[]; X = Y){I}):
        (Z, W.V)
    else:
        (-1, W.V)
Main():void =
    if (I := F[20, array{10, 20, 30}]) then Print("{I}")
    if (not F[5, array{10}]) then Print("none")
    if (X := G[array{1, 2, 3, 4}]) then Print("{X}")
    if (Y := first(K := 1..5; K * K > 5) { K }) then Print("{Y}")
    R := FirstPos2(20, array{10, 20, 30, 20})
    Print("{R(0)} {R(1)}")
    for (Q:int := 1..2) { Print("q{Q}") }
