# expect: 3:0: F has several values and a branch of an if with a defer: of its own, a return before its end and a path that does not return
# (#283: the rest of the function would follow the branch before its defer: runs)
F(N:int)<transacts>:int =
    if (N > 5) then { defer: Print("x"); if (N > 7) then return 1; Print("y") }
    N | N + 1
Main()<transacts>:void =
    for (X := F(9)) { Print("{X}") }
