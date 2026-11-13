# A cast that refines type arguments in a branch of an if written as an
# expression, in a failure context (#243): the branch is the block of it,
# where the cast is a clause of its own, lifted out of the expression, so
# it runs only when that branch does, and its failure is the context's.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
cell := class:
    var N:int = 0
# both branches, an else if
Pick(H:cell, P:pair(a, b), Q:pair(c, d), N:int where a:type, b:type, c:type, d:type)<transacts><decides>:int =
    set H.N += 1
    if (N > 1) then dup[P].C + N else if (N > 0) then dup[Q].C * 10 else -1
# the branch's value at the refined type; a branch that is a cast alone
Same(P:pair(a, b), N:int where a:type, b:type)<decides>:b =
    if (N > 0) then dup[P].A else dup[P].B
Itself(P:pair(a, b), N:int where a:type, b:type)<decides>:dup(a) =
    if (N > 0) then dup[P] else dup[P]
# inside a refining if's branch
Two(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<decides>:int =
    if (D := dup[P]) then dup[Q].C + D.C else 0
# a statement if in a <decides> body
Stmt(H:cell, P:pair(a, b), N:int where a:type, b:type)<transacts><decides>:int =
    if (N > 0) then set H.N += dup[P].C
    H.N
# in a branch of an if that a block binds, in option{}
Br(P:pair(a, b), N:int where a:type, b:type):?int = option{X := (if (N > 0) then dup[P].C else 0); X + 1}
Main()<transacts>:void =
    H := cell{}
    Y:pair(int, int) = dup(int){A := 1, B := 2}
    Z:pair(int, int) = pair(int, int){A := 1, B := 2}
    for (P : array{Y, Z}, Q : array{Y, Z}, N : array{0, 1, 2}):
        if (V := Pick[H, P, Q, N]) then Print("Pick {V} {H.N}") else Print("Pick no {H.N}")
    if (V := Same[Y, 1], W := Same[Y, 0]) then Print("Same {V} {W}")
    if (D := Itself[Y, 1]) then Print("Self {D.C}")
    if (V := Two[Y, Y]) then Print("Two {V}")
    if (V := Two[Y, Z]) then Print("Two {V}") else Print("Two no")
    if (V := Stmt[H, Y, 1]) then Print("Stmt {V}")
    if (V := Stmt[H, Z, 1]) then Print("Stmt {V}") else Print("Stmt no {H.N}")
    if (V := Stmt[H, Z, 0]) then Print("Stmt {V}")
    for (P : array{Y, Z}, N : array{0, 1}):
        if (V := Br(P, N)?) then Print("Br {N} {V}") else Print("Br {N} no")
