# More uses of methods with several values whose name another class has
# (#283): b.Vals has several values only through a's, which the class of a
# field tells, and c.Vals through b's; a recursive one taken lazily, a
# <decides> one and one with a named parameter beside ordinary ones of the
# same names; an ordinary one as a function value, in a parameter's default
# and in a field's; and a function that calls the other family's through a
# typed parameter.
a := class:
    Vals()<transacts>:int = 1 | 2
b := class:
    A : a
    Vals()<transacts>:int = A.Vals() + 10
c := class:
    B : b
    Vals()<transacts>:int = B.Vals() + 100
    Walk(N : int)<computes>:int = N
    Pick(N : int)<decides><transacts>:int = N = 3
    Off(?D : int = 9)<transacts>:int = D
walker := class:
    Walk(N : int)<computes>:int = if (N > 0) then (N | Walk(N - 1)) else 0
    Pick(N : int)<decides><transacts>:int =
        N > 0
        N | N * 10
    Off(?D : int = 3)<transacts>:int = D | D + 1
Count(W : walker, N : int)<computes>:int = W.Walk(N)
Def(?X : int = c{B := b{A := a{}}}.Off())<transacts>:int = X
holder := class:
    Xs : []int = for (X := a{}.Vals()) { X * 1000 }
    O : int = c{B := b{A := a{}}}.Off(?D := 5)
Main()<transacts>:void =
    C := c{B := b{A := a{}}}
    for (X := C.Vals()) { Print("c {X}") }
    for (X := C.B.Vals()) { Print("b {X}") }
    W := walker{}
    for (X := W.Walk(3)) { Print("walk {X}") }
    if (X := W.Walk(9), X < 7) { Print("first walk {X}") }
    for (X := Count(W, 2)) { Print("count {X}") }
    Print("c walk {C.Walk(3)}")
    for (X := W.Pick[2]) { Print("pick {X}") }
    if (X := C.Pick[3]) { Print("c pick {X}") }
    for (X := W.Off(), Y := W.Off(?D := 7)) { Print("off {X} {Y}") }
    Print("c off {C.Off()} {Def()}")
    F := C.Walk
    Print("value {F(4)}")
    H := holder{}
    for (X : H.Xs) { Print("held {X}") }
    Print("o {H.O}")
