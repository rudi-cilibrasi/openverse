# expect: 19:8: after the first success of this choice, A would be of type a or b, which have more than one nearest common supertype (#283)
# (#283, #335) Where the first success is taken of values of classes with two nearest common
# supertypes (interfaces, neither below the other), what the condition binds has no join after
# it, as an if's branches of those types have none: refused, A used or not.
i := interface:
    K():int
j := interface:
    L():int
a := class(i, j):
    K<override>():int = 1
    L<override>():int = 2
    M()<transacts>:int = 1 | 2
b := class(i, j):
    K<override>():int = 3
    L<override>():int = 4
    M()<transacts>:int = 30 | 40
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    if (A := (Dup(a{}) | Dup(b{})), X := A.M(), X > 2):
        Print("x {X}")
