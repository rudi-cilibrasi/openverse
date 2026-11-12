# A method with several values whose name another class has too (#283):
# each class or interface that declares Vals without <override> is the root
# of a family of its own, and the class of a call's receiver picks it. b.Vals
# is an ordinary method, so a function that calls it has one value; a
# function whose values come from a.Vals through a receiver of class a has
# several, as one through a.Vals alone would.
a := class:
    Vals()<transacts>:int = 1 | 2
b := class:
    Vals()<transacts>:int = 7
# (below a, without a Vals of its own: of a's family)
sub := class(a):
    K : int = 0
# (a receiver of a class in neither family: its own, an ordinary one)
c := class:
    Vals()<transacts>:int = 99
Show(B : b)<transacts>:void = Print("show {B.Vals()}")
Twice(A : a)<transacts>:int = A.Vals() * 2
Get(S : string)<transacts>:a =
    Print(S)
    a{}
Main()<transacts>:void =
    for (X := a{}.Vals()):
        Print("{X}")
    Print("b {b{}.Vals()}")
    Show(b{})
    for (X := Twice(a{})):
        Print("twice {X}")
    for (X := b{}.Vals()):
        Print("b in for {X}")
    for (X := sub{}.Vals()):
        Print("sub {X}")
    Print("c {c{}.Vals()}")
    # (the receiver once, first)
    for (X := Get("recv").Vals()):
        Print("got {X}")
    if (X := a{}.Vals(), X > 1):
        Print("first {X}")
