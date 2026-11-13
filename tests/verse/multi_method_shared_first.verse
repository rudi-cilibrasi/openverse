# (#283, #335) Where the first success is taken of a choice whose values are of unrelated
# classes, the clauses after it, with a call of a method with several values in each class,
# cannot be shared by the alternatives (an operation dictionary has one value per call), so they
# are copied for each, and what the condition binds has, after it, the join of its types in the
# copies: A an any (it was refused, saying to use a for), X an int.
a := class:
    M()<transacts>:int = 1 | 2
b := class:
    M()<transacts>:int = 30 | 40
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    if (A := (Dup(a{}) | Dup(b{})), X := A.M(), X > 1) { Print("x {X}") }
    if (A := (Dup(a{}) | Dup(b{})), X := A.M(), X > 2) { Print("x {X}") }
