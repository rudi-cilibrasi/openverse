# a function that is not <computes>, an if with a choice in one branch, taken lazily in a for (#246)
Upto(A:int, B:int):int = if (A <= B) then (A | Upto(A + 1, B)) else 0
Main():void =
    for (X := Upto(1, 3)) { Print("{X}") }
