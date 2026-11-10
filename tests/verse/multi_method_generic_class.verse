# Methods with several values of generic classes (#283): functions generic over
# the class's type parameters, their arguments inferred from the receiver
box(t : type) := class:
    A : t
    B : t
    Both()<transacts>:t = A | B
    Pairs()<transacts>:tuple(t, t) =
        Z : t = A
        (Z, B) | (B, Z)
    Pick(W : t)<transacts>:t = A | W
    Twice()<transacts>:t =
        V := Both()
        V
    Ret(N : int)<transacts>:t =
        if (N < 0):
            return A
        B | A
pr(a : type, b : type) := class:
    X : a
    Y : b
    Get()<transacts>:tuple(a, b) = (X, Y) | (X, Y)
ibox := class(box(int)):
    C : int = 7
Main()<transacts>:void =
    X := box(int){A := 1, B := 2}
    for (P := X.Pairs()):
        Print("a {P(0)} {P(1)}")
    for (V := X.Pick(5)):
        Print("b {V}")
    for (V := X.Twice()):
        Print("c {V}")
    for (V := X.Ret(-1)):
        Print("d {V}")
    for (V := X.Ret(1)):
        Print("e {V}")
    Q := pr(string, int){X := "q", Y := 3}
    for (G := Q.Get()):
        Print("f {G(0)} {G(1)}")
    I := ibox{A := 8, B := 9}
    for (V := I.Both()):
        Print("g {V}")
