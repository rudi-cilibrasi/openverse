# A block as an if's branch, with a call with several values or a choice
# in it (#283): its names are its own, renamed for its branch, so the
# clauses after the if may bind them again
Two(N : int):int = N | N + 10
P(S : string)<transacts>:int =
    Print(S)
    1
Main()<transacts>:void =
    for (C := 0..1, X := (if (C = 0) then { Y := Two(1); Y + 1 } else 0)):
        Print("a {C} {X}")
    for (X := (if (1 = 1) then { Y := Two(1); Y } else 0), Y := X * 2):
        Print("b {X} {Y}")
    if (X := (if (1 = 1) then { Z := Two(4); Z * 2 } else 0), X > 10):
        Print("c {X}")
    for (X := if (1 = 1) then { W := (1 | 2); W * 3 } else 0):
        Print("d {X}")
    for (A := P("e"), X := (if (A > 5) then 0 else { Q := Two(A); Q }), X > 5):
        Print("e {X}")
    for (C := 0..2, X := if (C = 0) then 0 else if (C = 1) then { V := Two(C); V } else 9):
        Print("f {C} {X}")
