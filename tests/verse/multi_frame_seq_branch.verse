# (#283) A choice bound in an if's branch, with code after it: the branch is
# the choice of that code after each alternative, as at the top of a body.
# A var set there is a cell: each later value sees what a kept one set.
Step(N:int)<transacts>:int =
    var Local:int = 0
    if (N <= 0) then 0 else:
        Y := Step(N - 1) + 1 | N * 10
        set Local += Y
        Local
Show(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        Y := Show(N - 1) + 1 | N * 10
        Print("y {Y}")
        Y
Main()<transacts>:void =
    for (V := Step(2)) { Print("v {V}") }
    for (V := Show(2)) { Print("s {V}") }
    if (V := Show(2), V > 15) then Print("first {V}")
