# Overridden methods with several values of generic classes and
# interfaces (#283): the dispatch's casts take each class's type arguments
# from the receiver's, as a cast to a generic class does
box(t : type) := class:
    A : t
    B : t
    Both()<transacts>:t = A | B
    Pick(W : t)<transacts>:t = A | W
sbox(t : type) := class(box(t)):
    Both<override>()<transacts>:t = B | (super:)Both()
    Pick<override>(W : t)<transacts>:t = W
    Twice()<transacts>:t = Both()
i(t : type) := interface:
    M()<transacts>:t
k(t : type) := class(i(t)):
    X : t
    M<override>()<transacts>:t = X | X
Get(X : box(t) where t : type)<transacts>:[]t =
    for (V := X.Both()) { V }
Main()<transacts>:void =
    Xs : []box(int) = array{box(int){A := 1, B := 2}, sbox(int){A := 3, B := 4}}
    for (X : Xs, V := X.Both()):
        Print("a {V}")
    for (X : Xs, V := X.Pick(9)):
        Print("b {V}")
    S := sbox(string){A := "x", B := "y"}
    for (V := S.Twice()):
        Print("c {V}")
    for (V : Get(sbox(string){A := "p", B := "q"})):
        Print("d {V}")
    for (V := k(int){X := 7}.M()):
        Print("e {V}")
