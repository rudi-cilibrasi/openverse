# Exclusive choices in a for (#314's returns, #331's ifs) followed by
# another such choice: the clauses after each and the body are a function
# of their own, which each path calls (#335, phase 2b), instead of a copy in
# each path; the values and effects are the copy's
P(S : string, V : int)<transacts>:int =
    Print(S)
    V
F(X:int)<transacts>:int =
    if (X < 0):
        return 0
    X | X + 1
G(X:int)<transacts>:int =
    Y := P("f{X}", X)
    if (P("c{X}", X) < 0):
        return 0
    Z := P("g{X}", 0)
    Y + Z | Y + 1
ctr := class:
    var Cn : int = 0
    Run()<transacts>:void =
        for (A := F(Cn), set Cn += 1, B := F(A * 10)):
            Print("m {A} {B} {Cn}")
T()<transacts>:void =
    for (A := F(1), B := F(10), C := F(100), D := F(1000)):
        Print("a {A + B + C + D}")
    var N : int = 0
    for (A := G(1), A > 1, B := G(10), set N += 1, C := (if (P("i", B) > 10) then (B | 100) else B), A + B + C > 30):
        Print("b {A} {B} {C} {N}")
    Print("n {N}")
    for (A := (if (P("j", 1) > 0) then (1 | 2) else 0), B := (if (A > 1) then 5 else (6 | 7)), C := F(A)):
        Print("c {A} {B} {C}")
    ctr{}.Run()
Main()<suspends>:void =
    T()
    # (a body that suspends cannot run in a failure context, and a
    # <suspends> function's effects are not a continuation's: copied)
    for (A := F(1), B := F(10)):
        Sleep(0.0)
        Print("d {A} {B}")
