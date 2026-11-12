# A lazily taken generator whose branch's value is an `if` with no choice in it
# (#283): that `if` is the value, so its conditions run with it and are undone
# with it where the consumer rejects it, as any value's code is. An `if` with a
# choice in a branch still picks the branch once, its conditions kept.
G(N:int, A:int):int =
    if (N <= 1) then (if (Print("c {N}"), A > -1) then 5 else 3) else (N | G(N - 1, A))
E(N:int):int =
    if (N > 1) then (N | E(N - 1)) else (if (Print("e {N}"), N = 1) then 30 else 40)
R(N:int):int =
    if (N <= 1):
        return (if (Print("r {N}"), N = 1) then 7 else 8)
    N | R(N - 1)
H(N:int)<transacts>:int =
    if (N <= 0) then 0 else if (Print("h {N}"), N = 1) then (10 | 20) else (N | H(N - 1))
Main()<transacts>:void =
    for (X := G(0, 4), X > 10) { Print("never {X}") }
    for (X := G(3, -1)) { Print("x {X}") }
    for (X := G(2, 4), X < 4) { Print("y {X}") }
    if (X := G(2, 4), X > 4) then Print("first {X}")
    for (X := E(2), X > 35) { Print("never {X}") }
    for (X := E(2), X < 35) { Print("e {X}") }
    for (X := R(2), X > 7) { Print("never {X}") }
    for (X := R(2)) { Print("r {X}") }
    for (X := H(2)) { Print("v {X}") }
