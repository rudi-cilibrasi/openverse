# (#283, #106) A method with several values in one class, whose name an unrelated class's
# hierarchy overloads: a's M stays in its class (as a family's stub) while a use's list is not
# known yet, so a call of it types (it was "class a has no method 'M'"). Where copies of the
# clauses after a choice whose values are of both classes elaborate one call, each hierarchy's
# list is the one its root's case takes; an override below b reaches b's list with (super:).
a := class:
    M()<transacts>:int = 1 | 2
b := class:
    M()<transacts>:int = 30 | 40
    M(N:int)<transacts>:int = N
b1 := class(b):
    M<override>()<transacts>:int = 300 | (super:)M()
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    for (X := a{}.M()) { Print("a {X}") }
    for (X := b{}.M()) { Print("b {X}") }
    Print("one {b{}.M(5)}")
    for (A := (Dup(a{}) | Dup(b{})), X := A.M()) { Print("x {X}") }
    for (A := (a{} | Dup(b1{})), X := A.M(), X > 1) { Print("y {X}") }
