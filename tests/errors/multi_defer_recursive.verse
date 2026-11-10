# expect: 2:0: R has several values and a defer:, and is recursive
R(N:int)<computes>:int =
    defer: Print("d")
    if (N > 0) then R(N - 1) else (N | N + 1)
Main()<transacts>:void =
    for (X := R(1)) { Print("{X}") }
