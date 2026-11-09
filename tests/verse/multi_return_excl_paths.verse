# An if with a return, when a choice comes after it, is an exclusive
# choice (#314); a for compiles it as the if it stands for on every path:
# an alternative with several values of its own, after a generator taken
# lazily, a path with a generator before the for's next one, two in one
# group, a for nested in an if condition or option with a choice, after a
# set, a condition that prints, a method. A rejected value undoes what came
# before the if, back to the last choice the program reached
G(X : int)<transacts>:int =
    Print("g{X}")
    if (X < 0):
        return 0
    X | X + 1
F(X : int)<transacts>:int =
    if (X < 0):
        return 0
    X | X + 1
K(X : int)<transacts>:int =
    if (Print("c{X}"), X < 0):
        return 0
    X | X + 1
Upto(A:int, B:int)<transacts><decides>:int =
    A <= B
    A | Upto[A + 1, B]
ctr := class:
    Base : int
    Pick(X : int)<transacts>:int =
        Print("p{X}")
        if (X < 0):
            return Base
        X | X + Base
Main()<transacts>:void =
    # an alternative with several values of its own: G(-1)'s print undone
    for (Z := (G(-1) | 7), Z > 5):
        Print("z {Z}")
    # after a generator taken lazily (#246)
    for (X := Upto[0, 2], Z := G(X - 1), Z > 1):
        Print("z {Z}")
    # a path with a generator, then the for's next generator
    for (Z := F(5), Y := 1..2, Z + Y > 7):
        Print("zy {Z} {Y}")
    # two in one group, after effects
    for (A := 1..2, Print("b{A}"), Z := G(-A), W := G(A - 2), Z + W > 0):
        Print("zw {Z} {W}")
    # after a choice whose alternative has several values
    for (Z := (1 | F(2)), W := G(-1), Z + W > 1):
        Print("zw {Z} {W}")
    # a for in an if condition with a choice of its own
    if (Y := 1 | 2, L := for (Z := G(-Y), Z > 5) { Z }, L.Length = 0):
        Print("empty {Y}")
    # a for in an option in a for's clauses
    for (A := 1..2, O := option{for (Z := G(A - 2), Z > 0) { Z }}, L := O?, L.Length > 0):
        Print("a{A} {L.Length}")
    # a set before it is undone with the rejected value
    var V : int = 0
    for (A := 1..2, set V += 1, Z := G(-A), Z > 0):
        Print("never")
    Print("v {V}")
    # a condition that prints: rolled back when it fails
    for (Z := K(-1), Z > 0):
        Print("never")
    for (Z := K(1), Z > 1):
        Print("z {Z}")
    # a method with several values
    C := ctr{Base := 10}
    for (A := 1..2, Z := C.Pick(A - 2), Z > 10):
        Print("z {Z}")
