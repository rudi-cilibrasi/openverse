# choices in either operand of `and` (#283): A's clauses, then B's, each operand a scope of its own; values in spatial order, the left's slowest; the `and`'s value is the right's
Digit():int = 0 | 1 | 2 | 3
Upto(A:int, B:int)<transacts><decides>:int =
    A <= B
    Print("visit {A}")
    A | Upto[A + 1, B]
Main()<transacts>:void =
    # (a for takes all of them: each choice a generator)
    for (X := ((1 | 2) > 1 and (10 | 20))) { Print("a {X}") }
    for (X := (Digit() > 1 and Digit() < 2)) { Print("b {X}") }
    for (X := (Upto[1, 2] and Upto[5, 6])) { Print("c {X}") }
    # (the code before a choice runs once; each alternative runs the rest)
    var K:int = 0
    for (X := (block{set K += 1; 1 | 2} and block{set K += 10; 3 | 4})) { Print("d {X} {K}") }
    # (the first success: an alternative that leads to none is rolled back)
    var N:int = 0
    if (X := (block{set N += 1; 1 | 2} and block{set N += 10; 7 | 8}), X > 7) { Print("e {X} {N}") }
    if (F := first{X := ((1 | 2) > 1 and (3 | 4) > 3); X}) { Print("f {F}") }
    if (O := option{(1 | 2) > 1 and (3 | 4)}?) { Print("g {O}") }
    L := logic{(1 | 2) > 1 and (3 | 4) > 3}
    if (L?) { Print("h") }
    if (X := Upto[3, 9] > 4 and Upto[1, 2]) { Print("i {X}") }
    # (as a clause of its own, and a chain of them)
    for (X := 1 | 2, X > 1 and (X | X * 10) > 5) { Print("j {X}") }
    if (X := ((1 | 2) > 1 and (3 | 4) > 3 and (5 | 6) > 5)) { Print("k {X}") }
    # (each operand a scope of its own: the same name in both)
    if ((X := 1 | 2; X > 1) and (X := 5 | 6; X > 5)) { Print("l") }
    for (Y := (block{X := 1 | 2; X} and block{X := 3; X + 1})) { Print("m {Y}") }
    # (under not, which takes its first success and keeps nothing)
    if (not ((1 | 2) > 1 and (3 | 4) > 5)) { Print("n") }
    if (not (block{set N += 100; 1 | 2} > 1 and (3 | 4) > 3)) { Print("never") } else { Print("o {N}") }
    Print("end {K} {N}")
