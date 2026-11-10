# Calls in an if's branches (#283) inside recursive bodies, generic
# functions, methods, option{…} and first{…}
Two(N : int):int = N | N + 10
H(N : int):int = if (N > 0) then Two(N) else 0
Twoc(N : int)<computes>:int = N | N + 10
H2(N : int)<computes>:int = if (N > 0) then (N | H2(N - 1)) else Twoc(100)
G(X:t where t:type):t = X | X
cc := class:
    K : int = 5
    Mv(N : int):int = N + K | N + K + 1
Main()<transacts>:void =
    if (Y := H(1), Y > 5):
        Print("a {Y}")
    for (X := H2(1)):
        Print("b {X}")
    if (Z := option{if (1 = 1) then Two(1) else 0}, V := Z?):
        Print("c {V}")
    for (C := 0..1, X := (if (C = 0) then G(7) else 1)):
        Print("d {C} {X}")
    O := cc{}
    for (C := 0..1, X := (if (C = 0) then O.Mv(1) else 1)):
        Print("e {C} {X}")
    if (X := first{ (if (1 = 2) then 0 else Two(4)) }):
        Print("f {X}")
