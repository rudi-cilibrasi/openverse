# A source return commits the retained recursive prefixes and skips later conditions.
G(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | G[N + 1]
F():tuple(int, int, logic) =
    if (X := G[0], if (X = 2) then return (42, 99, true) else true, X = 3) then (7, 0, false) else (8, 0, false)
Main():void =
    R := F()
    Print("{R(0)}")
