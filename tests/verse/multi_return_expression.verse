F(X:int)<transacts>:int =
    Y := if (X > 2) then (return 0) else X * 10
    Y | Y + 1
Main()<transacts>:void =
    for (V := F(3)) { Print("a {V}") }
    for (V := F(1)) { Print("b {V}") }
