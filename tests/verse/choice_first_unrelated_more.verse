# (#283, #335) More of the first success taken of values of unrelated classes, with the clauses
# after the choice copied for each alternative: a class below a base with one that is not (an
# any after the condition) and without it (the base), two such choices in one condition, and
# such an if in a loop.
base := class:
    K:int = 0
a := class(base):
    M()<transacts>:int = 1 | 2
c := class(base):
    M()<transacts>:int = 5 | 6
b := class:
    M()<transacts>:int = 30 | 40
d := class:
    M()<transacts>:int = 7
Dup(V:t where t:type):t = V | V
Take(V:any):void = Print("took")
Main()<transacts>:void =
    if (A := (Dup(a{}) | Dup(c{}) | Dup(b{})), X := A.M(), X > 5):
        Take(A)
        Print("three {X}")
    if (A := (Dup(a{}) | Dup(c{})), X := A.M(), X > 5):
        Print("base {A.K} {X}")
    if (A := (Dup(a{}) | Dup(b{})), X := A.M(), B := (Dup(c{}) | Dup(d{})), Y := B.M(), X + Y > 40):
        Print("two {X} {Y}")
    for (I := 1..3):
        if (A := (Dup(a{}) | Dup(b{})), X := A.M(), X > I * 15) then Print("loop {I} {X}") else Print("loop {I} none")
