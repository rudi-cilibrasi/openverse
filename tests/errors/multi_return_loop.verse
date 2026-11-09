# expect: 2:0: F has several values and a return other than in the branches of an if
F(X : int)<transacts>:int =
    for (I := 1..X):
        if (I = 2):
            return I
    X | X + 1
Main()<transacts>:void =
    for (V := F(3)):
        Print("{V}")
