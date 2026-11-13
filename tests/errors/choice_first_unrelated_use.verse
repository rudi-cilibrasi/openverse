# expect: 14:71: any has no method 'Q' (A is an any here: after the first success of the choice at 14:8, what the clauses after it bind has the join of its types in its alternatives (#283)
# (#283, #335) Where the first success is taken of values of unrelated classes, the clauses
# after the choice copied for each alternative, what the condition binds has, after it, the
# join of its types in the alternatives: A is an any there, which has no method Q, and the
# error says why, and which choice.
a := class:
    M()<transacts>:int = 1 | 2
    Q():int = 7
b := class:
    M()<transacts>:int = 30 | 40
    Q():int = 8
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    if (A := (Dup(a{}) | Dup(b{})), X := A.M(), X > 2) then Print("{A.Q()}")
