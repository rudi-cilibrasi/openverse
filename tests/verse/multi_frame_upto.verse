# (its call of itself with code after it: taken lazily, the code a return frame that runs on each of its values, #283)
Upto(A:int, B:int):int = if (A <= B) then (A | Upto(A + 1, B) + 0) else 0
Main():void =
    for (X := Upto(1, 3)) { Print("{X}") }
