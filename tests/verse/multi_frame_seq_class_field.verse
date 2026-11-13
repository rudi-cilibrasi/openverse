# (#283) A call of the recursive function in a field of a class's
# construction is a choice point there, in the class's field order (its
# superclass's fields first), the elaborator's, as an earlier elaboration
# noted it; so is a choice of values there.
base := class:
    B:int
c := class(base):
    A:int
T(N:int)<transacts>:int =
    if (N <= 0) then (0 | 1) else:
        Print("t {N}")
        O := c{A := T(N - 1), B := N}
        O.A + 10 * O.B
Pick(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        O := c{A := Pick(N - 1), B := (N | N * 100)}
        O.A + O.B
Main()<transacts>:void =
    for (V := T(2)) { Print("v {V}") }
    if (V := T(2), V > 20) then Print("first {V}")
    for (V := Pick(2)) { Print("p {V}") }
