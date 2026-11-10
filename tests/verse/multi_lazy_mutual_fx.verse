# Mutually recursive generators with effects (#283; tim-61's expectations,
# written from the design before the code): in a for, with a filter, and
# where the first success is taken (the path's prints kept)
Evens(N:int)<transacts>:int =
    Print("e{N}")
    if (N > 6) then 0 else (N | Odds(N + 1))
Odds(N:int)<transacts>:int =
    Print("o{N}")
    if (N > 6) then 1 else Evens(N + 1)
Main()<transacts>:void =
    for (X := Evens(0)) { Print("x{X}") }
    Print("--")
    for (X := Evens(0), X > 3) { Print("x{X}") }
    Print("--")
    if (X := Evens(0), X > 3) then Print("f{X}") else Print("none")
