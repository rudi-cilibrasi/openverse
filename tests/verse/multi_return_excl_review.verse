# Review of #318: two calls of the same function with an exclusive choice
# in one context (an if condition, separate clauses, an option, a return's
# value, a for over composed choices, a choice lifted in a path); a var its
# condition binds; the declared result type for `return array{}` and
# `return false`
F(X:int):int =
    if (X < 0):
        return 0
    X | X + 1
G(X:int):int =
    Y := X | X + 1
    if (Y = 2):
        return 99 | 98
    Y
Two(X:int):int = X * 10 | X * 20
F3(X:int):int =
    if (X < 0):
        return 0
    X | Two(X)
F4(X:int):int =
    if (X < 0):
        return 0
    X + (10 | 20)
FC(X:int):int =
    Y := (0 | X + (5 | 6))
    Y
FV(X:int):int =
    if (var N:int = X, N > 0):
        set N += 10
        return N | N + 1
    0 | 1
GV(X:int, Y:int):int =
    if (var A:int = X, var B:int = Y, A > 0):
        set A += 10
        set B += 100
        return A + B | A
    0 | 1
FA(X:int):[]int =
    if (X < 0):
        return array{}
    array{X} | array{X+1}
FO(X:int):?int =
    if (X < 0):
        return false
    option{X} | option{X+1}
Main():void =
    if (Z := F(1) + F(5), Z > 6):
        Print("{Z}")
    if (Y := F(1), Z := F(5), Y + Z > 6):
        Print("{Y} {Z}")
    if (O := option{F(1) + F(5)}, V := O?):
        Print("{V}")
    if (Z := G(1) + G(1), Z > 150):
        Print("{Z}")
    for (A := 1..2, Z := (F(A) | 7) + (F(A) | 8), Z > 9):
        Print("z {Z}")
    for (Z := F3(1) + F3(-1), Z > 10):
        Print("a {Z}")
    for (Z := F3(1) + F3(2), Z > 40):
        Print("b {Z}")
    if (Z := F3(1) + F3(2), Z > 40):
        Print("c {Z}")
    for (A := 1..1, Z := F4(A) + F4(2), Z > 40):
        Print("d {Z}")
    # (a composed choice in a body inlined twice: also on main before)
    if (A := FC(1), B := FC(2), A + B > 10):
        Print("{A} {B}")
    for (A := FC(1), B := FC(2), A + B > 13):
        Print("f {A} {B}")
    for (V := FV(1)) { Print("{V}") }
    for (V := FV(-1)) { Print("{V}") }
    if (V := FV(1), V > 11) { Print("if {V}") }
    for (V := GV(1, 2)) { Print("g {V}") }
    for (V := FA(-1)) { Print("{V.Length}") }
    for (V := FA(2)) { Print("{V.Length}") }
    for (V := FO(-1)) { Print("o {if (V?) then 1 else 0}") }
