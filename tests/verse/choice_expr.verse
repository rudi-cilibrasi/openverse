# choice inside expressions (#208): a choice in an operand is lifted out of
# its clause, the code before it bound first, so it still runs once
Sq(X:int):int = X * X
Big(X:int)<decides>:int = X > 4
Tell(S:string):int =
    Print(S)
    1
pt := struct:
    X:int = 0
Main():void =
    # VC's example: the leftmost choice slowest
    Xs := for{(1 | 2) + (10 | 20)}
    for (X : Xs) { Print("{X}") }
    # comparisons
    X := 3
    if (X = 1 | 2 | 3) then Print("X is small")
    if (X = 4 | 5) then Print("no") else Print("X is not 4 or 5")
    # calls, and decides calls
    for (Y := Sq(1 | 2 | 3)) { Print("sq {Y}") }
    if (H := Big[3 | 5 | 8]) then Print("big {H}")
    # code before a choice runs once
    Zs := for{Tell("once") + (1 | 2)}
    Print("{Zs.Length}")
    # option, logic, not, or
    if (O := option{(1 | 2) > 1}?) then Print("option {O}")
    L := logic{X = 7 | 8}
    if (not L?) then Print("logic false")
    if (not (X = 2 | 3)) then Print("no") else Print("not: X is 2 or 3")
    W := (X = 9 | 10) or 42
    Print("or {W}")
    # strings and tuples, arrays
    for (S := "a{1 | 2}") { Print(S) }
    for (T := (1 | 2, 3)) { Print("{T(0)}{T(1)}") }
    for (A := array{0 | 9, 5}, V := A[0]) { Print("{V} of {A.Length}") }
    # member access and method receivers
    for (P := (pt{X := 4} | pt{X := 5}).X) { Print("pt {P}") }
    # set from a lifted expression
    var N:int = 0
    if (set N = (1 | 2) * 10, N > 15) then Print("set {N}")
    # a variable the clause sets is read where it is written: before the choice
    var M:int = 0
    if (Y := M + ((set M = 5; 1) | 2), Y > 1) then Print("read before: {Y} {M}") else Print("none {M}")
    # the code before a choice, once and in order
    if (V := Tell("a") + Tell("b") * (1 | 2 | 3), V > 2) then Print("v {V}")
