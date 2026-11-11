# Registrations after an earlier return run only on paths that reach them.
F(N:int)<transacts>:int =
    if (N > 5) then return 0
    defer: Print("d")
    N | N + 1
Main()<transacts>:void =
    for(N:array{9,1}):
        Print("case {N}")
        for (X := F(N)) { Print("{X}") }
