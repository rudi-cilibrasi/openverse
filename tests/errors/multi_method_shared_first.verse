# expect: 12:8: the values of this choice are of types with nothing above both, a and b, and the clauses after it cannot be shared by them (#335)
# (#283, #335) Where the first success is taken of a choice whose values are of unrelated
# classes, the clauses after it, with a call of a method with several values in each class,
# cannot be shared by the alternatives (an operation dictionary has one value per call), and
# copied for each, A would have a or b's type after them: refused, saying to use a for.
a := class:
    M()<transacts>:int = 1 | 2
b := class:
    M()<transacts>:int = 30 | 40
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    if (A := (Dup(a{}) | Dup(b{})), X := A.M(), X > 1) { Print("x {X}") }
