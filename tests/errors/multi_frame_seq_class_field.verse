# expect: 8:0: T has several values and is recursive, or called by a recursive one, and it is not <computes>: such a function must be <computes>, keep no local state, and reach nothing that prints or calls Err(), as all its values are computed at a call (#235), unless it is taken lazily: clauses, then a choice whose alternatives are values, calls of its recursive group, or such a call or a choice with code after it that may reach another, not in a field of a class's construction (#246, #283)
# (#283) A call of the recursive function in a field of a class's
# construction: the class's layout is the elaborator's, so the lifter keeps
# the construction, and the function is not of the shape taken lazily.
c := class:
    A:int
    B:int
T(N:int)<transacts>:int =
    if (N <= 0) then (0 | 1) else:
        Print("t {N}")
        O := c{A := T(N - 1), B := N}
        O.A + 10 * O.B
Main()<transacts>:void =
    for (V := T(2)) { Print("v {V}") }
