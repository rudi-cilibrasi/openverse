# expect: 3:0: Upto has several values and is recursive, or called by a recursive one, and it is not <computes>
# (its call of itself inside an alternative: all its values computed at a call, F$all, not taken lazily, #246)
Upto(A:int, B:int):int = if (A <= B) then (A | Upto(A + 1, B) + 0) else 0
Main():void =
    for (X := Upto(1, 3)) { Print("{X}") }
