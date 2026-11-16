F(X : int)<transacts>:int =
    for (I := 1..X):
        if (I = 2):
            return I
    X | X + 1
Main()<transacts>:void =
    for (V := F(3)):
        Print("{V}")
    for (V := F(1)):
        Print("{V}")
    Print("after")
