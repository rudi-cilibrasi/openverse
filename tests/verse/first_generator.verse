# The Book's first takes generators as for does (ch. 7, "first"; its tests,
# FlowControl/first.versetest): the first iteration whose clauses succeed
# gives the body's value; none, and first fails.
Pos(X:int, Xs:[]int)<transacts><decides>:int =
    first(I->Y:Xs; X = Y){I}
Main():void =
    if (P := Pos[20, array{10, 20, 30, 20}]) then Print("at {P}")
    if (not Pos[5, array{10}]) then Print("none")
