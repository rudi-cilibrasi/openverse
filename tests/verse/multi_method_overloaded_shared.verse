# Overloaded methods with several values (#283) whose name unrelated classes also declare (#555's
# families): a class that overloads it with a list of several values, one with a plain one of several
# values, one with an ordinary one; two unrelated classes that both overload it, so a call is picked
# its list, then its family; a function calling the ordinary list; and an interface's overloaded
# method whose list with several values has a default, implemented by classes
a := class:
    Vals()<transacts>:int = 1 | 2
    Vals(X : int)<transacts>:int = X
b := class:
    Vals()<transacts>:int = 30 | 40
c := class:
    Vals():int = 500
d := class:
    Vals()<transacts>:int = 7 | 8
    Vals(S : string)<transacts>:int = S.Length | 9
Twice(O : a):int = O.Vals(7) * 2
shape := interface:
    Parts()<transacts>:int = 0 | 1
    Parts(N : int)<transacts>:int
sq := class(shape):
    Parts<override>()<transacts>:int = 4 | 40
    Parts<override>(N : int)<transacts>:int = N * 4
tri := class(shape):
    Parts<override>(N : int)<transacts>:int = N * 3
Main()<transacts>:void =
    A := a{}
    B := b{}
    C := c{}
    D := d{}
    for (X := A.Vals()) { Print("a {X}") }
    for (X := B.Vals()) { Print("b {X}") }
    Print("c {C.Vals()}")
    Print("a1 {A.Vals(9)}")
    Print("tw {Twice(A)}")
    for (X := D.Vals()) { Print("d {X}") }
    for (X := D.Vals("xyz")) { Print("ds {X}") }
    for (X := A.Vals(), Y := D.Vals()) { Print("ad {X} {Y}") }
    Ss : []shape = array{sq{}, tri{}}
    for (S : Ss, X := S.Parts()) { Print("p {X}") }
    for (S : Ss) { Print("n {S.Parts(2)}") }
