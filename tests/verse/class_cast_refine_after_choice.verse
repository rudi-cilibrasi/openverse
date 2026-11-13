# A refining cast after a choice in an if's condition (#243): the cast takes
# the clauses after it as its branch in a clause of its own, which the
# choice's first success takes; a break leaves the loop from the if's branch.
# (A break among the clauses, before the cast or after it, is gone: it cannot
# leave the condition, a failure context, SOL-4199-BreakFromIf.versetest:4.)
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
A1(P:pair(a, b) where a:type, b:type):int =
    if (X := (1 | 2 | 3), X > 1, D := dup[P]) then D.C + X else -1
A2(P:pair(a, b) where a:type, b:type):?b =
    if (X := (1 | 2 | 3), X > 1, D := dup[P], Print("{X}")) then option{D.A} else false
A3(P:pair(a, b) where a:type, b:type):int =
    var R:int = 0
    loop:
        if (X := (1 | 2 | 3), X > 1, D := dup[P], X > 2) then (set R = D.C + X; break)
        set R = -1
        break
    R
Main():void =
    Y:pair(int, int) = dup(int){A := 1, B := 2}
    Z:pair(int, int) = pair(int, int){A := 1, B := 2}
    Print("A1 {A1(Y)} {A1(Z)}")
    if (V := A2(Y)?) then Print("A2 {V}")
    Print("A3 {A3(Y)} {A3(Z)}")
