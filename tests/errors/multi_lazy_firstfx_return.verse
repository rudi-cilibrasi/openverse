# expect: 7:14: G has several values, is recursive and may print in its clauses
# (#246, #283) the clauses after an effectful generator, where the first success is taken, run in a function of their own: a return there would leave it, not F; refused
G(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | G[N + 1]
F():tuple(int, int, logic) =
    if (X := G[0], if (X = 2) then return (42, 99, true) else true, X = 3) then (7, 0, false) else (8, 0, false)
Main():void =
    R := F()
    Print("{R(0)}")
