# Returns with a choice after the if, or in the return's value (#314): the
# if becomes an exclusive choice, which a for compiles as the if it stands
# for, with no generator: a rejected value undoes what came before it (the
# caller's print too) as without the return; prints before a real choice stay
G(S : string, V : int)<transacts>:int =
    Print(S)
    V
F(X : int)<transacts>:int =
    if (X < 0):
        return 0
    X | X + 1
RT(X : int)<transacts>:int =
    Y := X | X + 1 | X + 2
    Print("pre{Y}")
    if (Y = X + 1):
        return 99 | 98
    else:
        Print("e{Y}")
    Y * 10 | Y * 100
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
Main()<transacts>:void =
    # the caller's print is undone with the rejected value: F(-1)'s path has no choice
    for (A := G("a", 1), Z := F(-1), Z > 100):
        Print("never {Z}")
    for (Z := F(5), Z > 5):
        Print("z {Z}")
    for (Z := RT(1), Z > 98):
        Print("rt {Z}")
    if (Z := RT(1), Z > 150):
        Print("if {Z}")
    Print("done")
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
