# (#283, #335) More methods of one name with several values in unrelated classes, called in the
# clauses after a choice whose values are of those classes (copied for each, the receiver's class
# picking the family): an interface's family beside a class's, a generic class's, named
# parameters with defaults of their own, <decides> methods, two such choices in one for, and a
# method that prints before its values, whose sum a for's body keeps.
i := interface:
    M(N:int)<transacts>:int
ia := class(i):
    M<override>(N:int)<transacts>:int = N | N * 10
ib := class(i):
    M<override>(N:int)<transacts>:int = N + 100
ic := class:
    M(N:int)<transacts>:int = N - 1 | N - 2
box(t:type) := class:
    V:t
    G()<transacts>:int = 1 | 2
gc := class:
    G()<transacts>:int = 7
gd := class:
    G()<transacts>:int = 8 | 9
na := class:
    Nm(?K:int = 3)<transacts>:int = K | K + 1
nb := class:
    Nm(?K:int = 5)<transacts>:int = K * 10 | K * 100
da := class:
    D(N:int)<decides><transacts>:int =
        N > 0
        N | -N
db := class:
    D(N:int)<decides><transacts>:int =
        N < 5
        N + 1 | N + 2
pa := class:
    P()<transacts>:int =
        Print("pa")
        1 | 2
pb := class:
    P()<transacts>:int =
        Print("pb")
        30 | 40
wa := class:
    W()<transacts>:int = 1 | 2
wb := class:
    W()<transacts>:int = 30
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    for (A := (Dup(ia{}) | Dup(ic{}) | ib{}), X := A.M(3)) { Print("p {X}") }
    for (A := (Dup(box(int){V := 5}) | gc{} | Dup(gd{})), X := A.G()) { Print("q {X}") }
    for (A := (Dup(na{}) | nb{}), X := A.Nm()) { Print("r {X}") }
    for (A := (na{} | Dup(nb{})), X := A.Nm(?K := 2)) { Print("s {X}") }
    for (A := (Dup(da{}) | Dup(db{})), N := (0 | 7), X := A.D[N]) { Print("t {N} {X}") }
    for (A := (Dup(wa{}) | wb{}), B := (wa{} | Dup(wb{})), X := A.W(), Y := B.W()) { Print("w {X} {Y}") }
    var S:int = 0
    for (A := (Dup(pa{}) | pb{}), X := A.P(), X > 1) { set S += X; Print("x {X} {S}") }
    Print("S {S}")
