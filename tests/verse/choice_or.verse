# choices on the right of `or` (#283): `A or B` is `if (T := A) then T else B`, so the left's first success, if it has one, is the only value (rolled back when it has none), and otherwise the values are the right's, taken by the context the `or` is in
Digit():int = 0 | 1 | 2 | 3
Upto(A:int, B:int)<transacts><decides>:int =
    A <= B
    Print("visit {A}")
    A | Upto[A + 1, B]
Nat(N:int)<computes><decides>:int = N | Nat[N + 1]
Run(O:?int)<transacts>:void =
    Print("-- {if (V := O?) then V else -1}")
    # (a for: the left's value, or each of the right's)
    for (X := (O? or (5 | 6))) { Print("a {X}") }
    for (X := (Digit() > 2 or Digit())) { Print("b {X}") }
    for (X := (O? or Upto[1, 2])) { Print("c {X}") }
    # (the left of or rolls back what it did when it fails)
    var N:int = 0
    for (X := (block{set N += 1; O?} or block{set N += 10; 7 | 8})) { Print("d {X} {N}") }
    # (the first success: the right's alternatives in turn, from where the or is)
    var M:int = 0
    if (X := (block{set M += 1; O?} or block{set M += 10; 1 | 2 | 3}), X > 1) { Print("e {X} {M}") }
    else { Print("e none {M}") }
    if (X := (O? or Nat[0]), X * X > 50) { Print("f {X}") } else { Print("f none") }
    if (F := first{X := (O? or (5 | 6)); X > 5; X}) { Print("g {F}") } else { Print("g none") }
    if (V := option{O? or (Digit() > 2 and (8 | 9))}?) { Print("h {V}") }
    # (the left succeeds: the right never runs, even when what follows fails)
    if (X := (O? or (1 | 9)), X > 8) { Print("i {X}") } else { Print("i none") }
    # (in a for, an or whose left succeeds adds no generator: a value the
    # filters after it reject undoes what came before it, as an if's does)
    var P:int = 0
    for (X := 1 | 2, (set P += 1; true?), Y := (O? or (5 | 6)), Y > 5) { Print("j {X} {Y} {P}") }
    Print("j end {P}")
    # (a chain, nesting, and not)
    if (X := (O? or block{false?; 0} or (3 | 4)), X > 3) { Print("k {X}") }
    if (X := (((1 | 2) > 1 and (3 | 4) > 5) or (9 | 10)), X > 9) { Print("l {X}") }
    if (not (O? or (1 | 2) > 5)) { Print("m") } else { Print("m not") }
    # (each operand a scope of its own)
    for (Y := ((X := O?) or block{X := 1 | 2; X * 10})) { Print("n {Y}") }
Main()<transacts>:void =
    Run(false)
    Run(option{5})
