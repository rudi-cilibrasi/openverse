# More calls in an if's branches (#283): a set, inlined bodies whose value is
# such an if, first-success contexts with effects, nested ifs, eager and
# lazy recursive ones, two calls in one branch
Two(N : int):int = N | N + 10
H(N : int):int = if (N > 0) then Two(N) else 0
E(N : int)<computes>:int = if (N > 1) then N else (N | E(N + 1) + 0)
Down(N : int):int = if (N > 0) then (N | Down(N - 1)) else 0
PT(N : int)<transacts>:int =
    Print("pt")
    N | N + 10
Main()<transacts>:void =
    var N : int = 0
    for (C := 0..1, set N = (if (C = 0) then Two(1) else 5)):
        Print("a {N}")
    for (X := H(1)):
        Print("b {X}")
    for (X := H(0)):
        Print("c {X}")
    A := 1
    if (Y := (if (A > 0) then PT(1) else 0), Y > 5):
        Print("d {Y}")
    for (C := 0..1, X := (if (C = 0) then (if (C = 0) then Two(1) else 3) else 4)):
        Print("e {C} {X}")
    M : ?int = option{3}
    for (X := (if (V := M?) then V + (0 | 100) else 7)):
        Print("f {X}")
    for (C := 0..1, X := (if (C = 0) then E(0) else 9)):
        Print("g {C} {X}")
    if (Y := (if (V := M?) then Down(V) else 0), Y < 2):
        Print("h {Y}")
    for (C := 0..1, X := (if (C = 0) then Two(1) + Two(2) else 0)):
        Print("i {C} {X}")
