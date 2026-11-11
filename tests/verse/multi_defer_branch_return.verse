# A returning/fallthrough branch cleans up before the function's tail.
F(N:int)<transacts>:int =
    if (N > 5) then { defer: Print("x"); if (N > 7) then return 1; Print("y") }
    N | N + 1
Main()<transacts>:void =
    for(N:array{9,6,1}):
        Print("case {N}")
        for (X := F(N)) { Print("{X}") }
