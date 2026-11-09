# expect: 2:0: Upto has several values and calls itself, directly or not: recursive functions with several values are not supported yet
Upto(A:int, B:int):int = if (A <= B) then (A | Upto(A + 1, B)) else 0
Main():void =
    for (X := Upto(1, 3)) { Print("{X}") }
