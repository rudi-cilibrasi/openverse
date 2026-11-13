# (#283, #335) Methods of one name with several values in unrelated classes below a class that
# does not declare it: where the first success of a choice whose values are of those classes is
# taken, the clauses after it are copied for each, the receiver's class picks the family, and
# what the condition binds has the base class's type after it.
base := class:
    K:int = 0
a := class(base):
    M(N:int)<transacts>:int = N * 2 | N + 1
b := class(base):
    M(N:int)<transacts>:int = N * 10
c := class(base):
    M(N:int)<transacts>:int = N - 5 | N * 7
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    if (A := (Dup(a{}) | b{} | Dup(c{})), X := A.M(3), X > 9) { Print("first {X}") } else { Print("none") }
    if (A := (Dup(c{}) | b{} | Dup(a{})), X := A.M(3), X > 20) { Print("first {X}") } else { Print("none") }
    if (A := (Dup(a{}) | b{} | Dup(c{})), X := A.M(3), X > 99) { Print("first {X}") } else { Print("none") }
    if (Y := first{A := (Dup(c{}) | Dup(a{})); A.M(1)}) { Print("y {Y}") }
