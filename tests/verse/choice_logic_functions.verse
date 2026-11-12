# functions and methods with several values whose choices are in the operands of `and` or on the right of `or` (#283), a recursive one computed eagerly, a lazy generator on the right of `or`, a block's defer: in an operand, and `set` and written types
Pos(X:int)<decides>:int = X > 0 and (X | X * 10)
Or(O:?int):int = O? or (1 | 2)
Small(N:int)<computes><decides>:int = N < 3 and (N | Small[N + 1])
Walk(N:int)<transacts><decides>:int =
    Print("walk {N}")
    N < 3
    N | Walk[N + 1]
box := class:
    V:int
    Pick()<transacts><decides>:int = V > 1 and (V | V + 100)
Main()<transacts>:void =
    for (X := Pos[3]) { Print("pos {X}") }
    for (X := Pos[-1]) { Print("never {X}") }
    for (X := Or(option{7})) { Print("or {X}") }
    for (X := Or(false)) { Print("or {X}") }
    for (X := Small[0]) { Print("small {X}") }
    if (X := (block{false?; 0} or Walk[0]), X > 1) { Print("walk got {X}") }
    for (X := (Walk[1] > 1 and Walk[1])) { Print("ww {X}") }
    B := box{V := 2}
    for (X := B.Pick[]) { Print("pick {X}") }
    for (X := (block{defer: Print("d"); 1 | 2} and 5)) { Print("defer {X}") }
    var N:int = 0
    for (set N = ((1 | 2) > 1 and (3 | 4))) { Print("set {N}") }
    for (Y:int = (block{false?; 0} or (5 | 6))) { Print("typed {Y}") }
    var V:int = 0
    if (set V = (block{false?; 0} or (5 | 6)), V > 5) { Print("set or {V}") }
