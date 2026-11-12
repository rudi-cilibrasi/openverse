# Qualified calls X.(q:)M(…) (#125) of methods with several values (#283): a call in the family of
# the root q is below, dispatched on X's class as an unqualified call is. Before, one whose method
# kept a stub in its class (overridden, of a name unrelated classes share, or overloaded) called the
# stub and stopped with an error, and one overridden nowhere was refused
i1 := interface:
    M(X:int)<transacts>:int = X | X + 1
c1 := class(i1):
    K:int = 0
i2 := interface:
    M(X:int)<transacts>:int = X | X + 1
c2 := class(i2):
    M<override>(X:int)<transacts>:int = X * 10 | X
a := class:
    N(X:int)<transacts>:int = X | X + 1
b := class:
    N(X:int)<transacts>:int = X * 2 | X
i3 := interface:
    P(X:int)<transacts>:int = X | X + 1
    P(X:string)<transacts>:int
c3 := class(i3):
    P<override>(X:string)<transacts>:int = 1 | 2
Main()<transacts>:void =
    for (V := c1{}.(i1:)M(7)) { Print("direct {V}") }
    for (V := c2{}.(i2:)M(7)) { Print("overridden {V}") }
    for (V := a{}.(a:)N(7)) { Print("shared {V}") }
    for (V := b{}.(b:)N(7)) { Print("shared b {V}") }
    C := c3{}
    for (V := C.(i3:)P(7)) { Print("overloaded {V}") }
    for (V := C.(i3:)P("x")) { Print("overloaded s {V}") }
    if (V := C.(i3:)P(1), V > 1) then Print("first {V}")
