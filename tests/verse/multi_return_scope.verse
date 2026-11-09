# Returns in functions with several values (#283), from the review of
# #312: a branch's names are its own (a name declared in a branch, or bound
# by its condition, may be declared again after the if); nested ifs; a
# return without a value in a void function
Leak(X : int)<transacts>:int =
    if (X < 0):
        return 0
    else:
        D := X * 2
        Print("d {D}")
    D := X + 1
    D | D * 2
Nest(X : int)<transacts>:int =
    if (X > 0):
        Z := X * 2
        if (Z > 10):
            return Z
        Print("t {Z}")
    Z := 100
    Z | Z + 1
Names(M : ?int)<transacts>:int =
    if (V := M?):
        if (V > 10):
            return V
        Print("small {V}")
    V := 7
    V | V + 1
Bare(X : int)<transacts>:void =
    Y := X | X + 1
    if (Y > 1):
        Print("pos{Y}")
        return
    Print("n{Y}")
Main()<transacts>:void =
    for (V := Leak(3)):
        Print("f {V}")
    for (V := Nest(1)):
        Print("a {V}")
    for (V := Nest(9)):
        Print("b {V}")
    for (V := Nest(-1)):
        Print("c {V}")
    for (R := Names(option{3})):
        Print("a {R}")
    for (R := Names(option{30})):
        Print("b {R}")
    for (R := Names(false)):
        Print("c {R}")
    for (V := Bare(1)):
        Print("x")
