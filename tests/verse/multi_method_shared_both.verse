# Two unrelated classes' methods with several values of one name (#283), a
# family each: the class of a call's receiver picks it, Self's in a class
# (a bare call too), a field's from its type. Their values come in order,
# where the first success is taken and in a for.
a := class:
    K : int
    Vals()<transacts>:int = K | K + 1
    Twice()<transacts>:int = Vals() * 2
    Thrice()<transacts>:int = Self.Vals() * 3
b := class:
    Other : a
    var Count : int = 0
    Vals()<transacts>:int =
        set Count += 1
        10 | 20 | Other.Vals()
    # (b's own, then the field's a's)
    Sum()<transacts>:int = Vals() + Other.Vals()
Main()<transacts>:void =
    A := a{K := 1}
    B := b{Other := a{K := 5}}
    for (X := A.Vals()) { Print("a {X}") }
    for (X := B.Vals()) { Print("b {X}") }
    for (X := A.Twice()) { Print("twice {X}") }
    for (X := A.Thrice()) { Print("thrice {X}") }
    for (X := B.Sum()) { Print("sum {X}") }
    for (X := B.Other.Vals(), Y := A.Vals()) { Print("pair {X} {Y}") }
    # (the first success: what the rejected values did undone)
    if (X := B.Vals(), X > 15, Y := A.Vals(), X + Y > 21):
        Print("first {X} {Y}")
    if (X := B.Vals(), X > 100):
        Print("never {X}")
    else:
        Print("none")
    Print("count {B.Count}")
