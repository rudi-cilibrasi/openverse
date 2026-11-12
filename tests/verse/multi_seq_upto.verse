# (#283) Choice points in sequence: a choice after its call of itself, in a function that is not <computes>: taken lazily.
Upto(A:int, B:int):int = if (A <= B) then (A | Upto(A + 1, B) + (0 | 1)) else 0
Main():void =
    for (X := Upto(1, 3)) { Print("{X}") }
