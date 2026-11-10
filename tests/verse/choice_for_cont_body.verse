# Two or more exclusive choices in a for's clauses, with a body that may not
# run in a failure context (a return, a suspension, a signal): the clauses
# copied, as before (#335, phase 2)
F(X:int)<transacts>:int =
    if (X < 0):
        return 0
    X | X + 1
First(N:int)<transacts>:int =
    for (Z := F(N), W := F(N), Z + W > 2):
        return Z * 10 + W
    -1
Main()<suspends>:void =
    Print("first {First(1)}")
    for (Z := F(1), W := F(-1)):
        Sleep(0.0)
        Print("z {Z} {W}")
    E := event(int){}
    for (Z := F(1), W := F(-1)):
        E.Signal(Z + W)
        Print("s {Z} {W}")
