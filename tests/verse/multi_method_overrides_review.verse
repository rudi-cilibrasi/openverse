# Review of overridden methods with several values (#283): arguments at
# their parameters' types (array{}, map{}, false), one tuple argument to
# several parameters with a single-valued implementation, and the eager
# route (F$all) with the dispatch in a nested for
shape := class:
    Count(Xs : []int, M : [int]int, O : ?int)<transacts>:int = Xs.Length + M.Length | (if (V := O?) then V else 7)
    Add2(A : int, B : int)<transacts>:int = A + B | A * B
    Sizes()<computes>:int = 1 | 2
big := class(shape):
    Count<override>(Xs : []int, M : [int]int, O : ?int)<transacts>:int = 100
    Add2<override>(A : int, B : int)<transacts>:int = 1000
    Sizes<override>()<computes>:int = 7
Walk(O : shape, N : int)<computes>:int =
    A := for (X := O.Sizes()) { X }
    if (N > 0) then (N | Walk(O, N - 1)) else A.Length
Main()<transacts>:void =
    for (X := shape{}.Count(array{}, map{}, false)):
        Print("c {X}")
    for (X := big{}.Count(array{}, map{}, false)):
        Print("b {X}")
    T := (3, 4)
    for (X := shape{}.Add2(T)):
        Print("t {X}")
    for (X := big{}.Add2(T)):
        Print("u {X}")
    for (V := Walk(shape{}, 1)):
        Print("w {V}")
    for (V := Walk(big{}, 1)):
        Print("v {V}")
