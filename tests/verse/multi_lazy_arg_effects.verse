# the argument of a generator's call of itself prints: once per call, also for the last one, whose clauses fail (#246)
Upto(A:int, B:int)<transacts><decides>:int =
    A <= B
    A | Upto[(Print("arg {A + 1}"); A + 1), B]
Main():void =
    for (X := Upto[1, 2]) { Print("got {X}") }
