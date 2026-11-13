# (#283) A return in a function with several values may be in a block or a case's arm, as in an
# if's branch: each is a scope that the return ends the invocation from, its values the
# function's, and the rest of the body is skipped for it; a block's defer: runs at the return,
# after the value and before the function's own.
Blk(X:int)<transacts>:int =
    defer: Print("f {X}")
    block:
        defer: Print("blk {X}")
        Y := X * 2
        if (Y > 4):
            return Y | Y + 1
        Print("fall {X}")
    X | X + 10
Last(X:int)<transacts>:int =
    Print("start {X}")
    block:
        Z := X + 1
        if (Z = 2):
            return 0
        Z * 10 | Z * 100
Rec(N:int)<transacts>:int =
    case (N):
        0 => return 7 | 8
        1 => Print("one")
        _ => {}
    N | Rec(N - 1)
Dec(X:int)<transacts><decides>:int =
    case (X):
        1 => return 10 | 11
        2 => Print("two")
    X | X * 100
Arms(X:int)<transacts>:int =
    case (X):
        1 => return 10 | 11
        2 => 20 | 21
        _ => X
Main()<transacts>:void =
    for (V := Blk(3)) { Print("a {V}") }
    for (V := Blk(1)) { Print("b {V}") }
    if (V := Blk(1), V > 5) then Print("first {V}")
    for (V := Last(1)) { Print("c {V}") }
    for (V := Last(2)) { Print("d {V}") }
    for (V := Rec(2)) { Print("e {V}") }
    if (V := Rec(2), V = 8) then Print("first {V}")
    for (V := Dec[1]) { Print("g {V}") }
    for (V := Dec[2]) { Print("h {V}") }
    for (V := Dec[3]) { Print("i {V}") }
    for (V := Arms(1) | Arms(2) | Arms(3)) { Print("j {V}") }
