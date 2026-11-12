# A condition whose only choice is a call of a method with several values
# whose name another class has (#283), directly or through a function: it
# can fail once the receiver's class has picked the family, so it is no
# condition that cannot fail, where it is and where the function is called.
First(A : a)<transacts>:int = if (X := A.Vals(), X > 1) then X else 0
a := class:
    Vals()<transacts>:int = 1 | 2
b := class:
    Vals()<transacts>:int = 7
Both(A : a)<transacts>:int = A.Vals()
Main()<transacts>:void =
    Print("first {First(a{})}")
    if (X := Both(a{})) { Print("both {X}") }
    if (X := a{}.Vals(), X > 1) { Print("direct {X}") }
    L := logic{a{}.Vals() > 1}
    if (L?) { Print("logic") }
    Print("b {b{}.Vals()}")
