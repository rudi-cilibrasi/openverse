# expect: expected tuple(int, int), found tuple(int, string)
# The group checks its elements as a tuple parameter does
F(A:int, (B:int, C:int)):int = A + B + C
Main():void =
    Print("{F(1, (2, "x"))}")
