# expect: 2:0: F has several values and a return in a for or a loop, which would leave its caller once inlined
F(X : int)<transacts>:int =
    for (I := 1..X):
        if (I = 2):
            return I
    X | X + 1
Main()<transacts>:void =
    for (V := F(3)):
        Print("{V}")
