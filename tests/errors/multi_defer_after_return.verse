# expect: 2:0: F has several values and a defer: after a return
F(N:int)<transacts>:int =
    if (N > 5) then return 0
    defer: Print("d")
    N | N + 1
Main()<transacts>:void =
    for (X := F(1)) { Print("{X}") }
