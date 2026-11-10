# An else if whose condition calls a lazily taken generator with effects and
# binds a name its branch uses, in a for, with no type written (#331): the
# join, elaborated apart, uses no function of its own made for the path
Gz0(N:int)<decides>:int =
    N >= 1
    Print("g1")
    ((2 + 5) | Gz0[(N - 1)])
Main()<transacts>:void =
    N0b : int = 4
    for (X7 := (if (-1 = 1) then (2) else if (Gz0[3] <> 1, X9 := N0b) then (X9) else (N0b | -1))):
        Print("f {X7}")
