# Methods with several values (#283): a top-level function each, taking
# Self explicitly (C$M($Self:C, …)), so inlined, lazy when recursive, with
# named parameters, as functions with several values are
c := class:
    K : int
    var N : int = 0
    Vals()<transacts>:int = K | K + 1
    # (a call without a receiver, in the class: Self's)
    Twice()<transacts>:int = Vals() * 2
    Step(D : int)<transacts>:int =
        set N += D
        N | N * 10
    # (a recursive one: taken lazily)
    Upto(I : int)<computes>:int = if (I < K) then (I | Upto(I + 1)) else I
    # (a named parameter's default sees the fields)
    Off(?D : int = K)<transacts>:int = K | K + D
    Pick(A : int)<decides><transacts>:int =
        A > K
        A | K
sub := class(c):
    Extra()<transacts>:int = Vals() + 1000
G(S : string)<transacts>:c =
    Print(S)
    c{K := 2}
dice := class:
    (dice:)Sides : int
    Roll()<transacts>:int = 1 | (dice:)Sides
player := class:
    D : dice
    Two()<transacts>:int = D.Roll() + D.Roll() * 10
    Me()<transacts>:int = Sides(Self) | D.Sides * 100
Sides(P : player)<transacts>:int = P.D.Sides
Main()<transacts>:void =
    O := c{K := 3}
    for (X := O.Vals()):
        Print("{X}")
    for (X := O.Twice()):
        Print("twice {X}")
    if (X := O.Vals(), X > 3):
        Print("if {X}")
    # (in a for, what Step did is kept; in a failed if, undone)
    for (X := O.Step(1)):
        Print("step {X} {O.N}")
    if (X := O.Step(5), X > 1000):
        Print("big {X}")
    Print("n {O.N}")
    # (the receiver once, first)
    for (X := G("recv").Vals()):
        Print("r {X}")
    for (X := O.Upto(1)):
        Print("upto {X}")
    for (X := O.Off()):
        Print("off {X}")
    for (X := O.Off(?D := 100)):
        Print("off d {X}")
    for (X := O.Pick[9]):
        Print("pick {X}")
    for (X := O.Pick[1]):
        Print("never {X}")
    S := sub{K := 7}
    for (X := S.Vals()):
        Print("sub {X}")
    for (X := S.Extra()):
        Print("extra {X}")
    Pl := player{D := dice{Sides := 6}}
    for (X := Pl.Two()):
        Print("two {X}")
    for (X := Pl.Me()):
        Print("me {X}")
