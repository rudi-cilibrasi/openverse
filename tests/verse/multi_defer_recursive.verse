# (#283) A recursive function with several values and a defer: of its own, computed at the call
# (<computes>) or taken lazily (here, as it prints): the defer: runs as each value leaves it.
R(N:int)<computes>:int =
    defer: Print("d")
    if (N > 0) then R(N - 1) else (N | N + 1)
Main()<transacts>:void =
    for (X := R(1)) { Print("{X}") }
