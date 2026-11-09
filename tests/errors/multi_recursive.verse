# expect: 2:0: Upto has several values and is recursive, or called by a recursive one, and it is not <computes>
Upto(A:int, B:int):int = if (A <= B) then (A | Upto(A + 1, B)) else 0
Main():void =
    for (X := Upto(1, 3)) { Print("{X}") }
