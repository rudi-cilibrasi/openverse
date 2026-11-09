# Returns in functions with several values (#283): an if with a return,
# after the function's choices, gives the value of the alternative it is
# reached in and skips the rest of the body for it. It stays an if (no
# choice is added), so effects roll back as without the return
G(S : string, V : int)<transacts>:int =
    Print(S)
    V
# a return after the choice, for one alternative
H()<transacts>:int =
    Y := 1 | 2 | 3
    if (Y = 2):
        return 99
    Y * 10
# a condition that binds a name; else-if chains; nested ifs; both branches
Cls(X : int)<transacts>:int =
    Y := X | X * 10
    if (Y < 0):
        return -1
    else if (Y = 0):
        return 0
    if (Y > 10):
        if (Y > 200):
            return 3
        return 2
    Y
M(K : int)<transacts>:int =
    Ks : [int]int = map{1 => 100, 3 => 300}
    Y := K | K + 1 | K + 2
    if (V := Ks[Y]):
        return V
    Y
# a branch's names are its own: the rest may declare the same ones
Sc(X : int)<transacts>:int =
    Y := X | X + 1
    if (Y < 0):
        return 0
    else:
        D := Y * 2
        Print("d {D}")
    D := Y + 1
    D
# effects in the branch, before and after the if
Eff(X : int)<transacts>:int =
    Y := X | X + 1 | X + 2
    Print("pre {Y}")
    if (Y = X + 1):
        return G("ret", 50)
    G("post", Y)
c := class:
    K : int
    Vals()<transacts>:int =
        Y := K | K + 1
        if (Y = 0):
            return 7
        Y * 2
# a plain function with an early return stays one
P(X : int):int =
    if (X > 0):
        return 1
    2
Main()<transacts>:void =
    for (V := H()):
        Print("h {V}")
    if (V := H(), V > 50):
        Print("if {V}")
    for (X : array{0, 1, 2, 30}, V := Cls(X)):
        Print("{X}: {V}")
    for (V := M(1)):
        Print("m {V}")
    for (V := Sc(3)):
        Print("sc {V}")
    for (V := Eff(1)):
        Print("eff {V}")
    if (V := Eff(1), V > 2):
        Print("first {V}")
    for (V := c{K := 0}.Vals()):
        Print("c0 {V}")
    for (V := c{K := 4}.Vals()):
        Print("c4 {V}")
    Print("p {P(1)} {P(0)}")
