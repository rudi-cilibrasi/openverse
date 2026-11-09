# a generator's argument that prints, for a call whose clauses fail: it has no values, and the print stays, as for a recursive call computed eagerly (main); an inlined function's call undoes it, as its clauses are the caller's (#246)
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
F(A:int)<transacts><decides>:int =
    A <= 2
    A | A + 10
Main():void =
    for (X := Upto[(Print("a"); 5), 3]) { Print("got {X}") }
    for (X := F[(Print("b"); 5)]) { Print("got {X}") }
    Print("end")
