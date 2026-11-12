# choices and calls with several values in the bounds of a for's range (#283): lifted before it, as operands evaluated in order, so the range is a generator after them, one range for each value of its bounds
D():int = 1 | 2
Upto(A:int, B:int)<transacts><decides>:int =
    A <= B
    Print("visit {A}")
    A | Upto[A + 1, B]
Main()<transacts>:void =
    for (X := (1 | 2)..3) { Print("a {X}") }
    for (X := 0..D()) { Print("b {X}") }
    for (X := (1 | 3)..(2 | 4)) { Print("c {X}") }
    var N:int = 0
    for (X := block{set N += 1; N}..(N + (1 | 2))) { Print("d {X} {N}") }
    for (Y := 1 | 2, X := Y..Upto[2, 3], X > 2) { Print("e {Y} {X}") }
    for (X := 1..3, Y := X..(X | 3)) { Print("f {X} {Y}") }
