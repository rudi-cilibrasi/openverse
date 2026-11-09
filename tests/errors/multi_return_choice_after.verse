# expect: 3:0: F has several values and a return in an if after which, or in whose return, there is a choice
# (that if would become a choice, a generator in a for: not yet)
F(X : int)<transacts>:int =
    if (X < 0):
        return 0
    else:
        D := X * 2
        Print("d {D}")
    D := X + 1
    D | D * 2
Main()<transacts>:void =
    for (V := F(3)):
        Print("f {V}")
