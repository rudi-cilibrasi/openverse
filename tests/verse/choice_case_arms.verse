# (#283) A case whose arms have choices, or calls of functions with several values, is lifted
# as the if chain that picks its arm: its scrutinee once, first, then the picked arm's values;
# so it may stand where a choice may, and end a function with several values.
Two(N:int):int = N | N + 1
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
F(X:int):int =
    case (X):
        1 => 10 | 11
        _ => X | X + 1
Main()<transacts>:void =
    for (V := F(1)) { Print("a {V}") }
    for (V := F(2)) { Print("b {V}") }
    for (X := 1..3, V := (case (X) { 1 => 10 | 11, 2 => Two(20), _ => 5 })) { Print("c {X} {V}") }
    if (V := (case (2) { 1 => 10, _ => 30 | 40 }), V > 30) then Print("first {V}")
    for (V := (case (Tell("s", 1) | 2) { 1 => 10, _ => 20 | 21 })) { Print("s {V}") }
    var N:int = 0
    for (X := 1..2, set N += (case (X) { 1 => (1 | 2), _ => 100 })) { Print("n {N}") }
