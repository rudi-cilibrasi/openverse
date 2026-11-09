# Returns in functions with several values (#283): in an if's branches, a
# return gives the value of its alternative and skips the rest of the body;
# the condition runs once (its names reach the branch through an option)
G(S : string, V : int)<transacts>:int =
    Print(S)
    V
# an early return before the choice
F(X : int)<transacts>:int =
    if (X < 0):
        return 0
    X | X + 1
# a return after the choice, for one alternative
H()<transacts>:int =
    Y := 1 | 2 | 3
    if (Y = 2):
        return 99
    Y * 10
# a return with several values; both branches return
Both(X : int)<transacts>:int =
    if (X > 0):
        return X | X * 2
    else:
        return G("neg", 7)
# a plain function with an early return stays single-valued
P(X : int):int =
    if (X > 0):
        return 1
    2
# else-if chain, nested if
Cls(X : int)<transacts>:int =
    if (X < 0):
        return -1
    else if (X = 0):
        return 0 | 100
    if (X > 10):
        if (X > 20):
            return 3
        return 2
    X | G("small", X * 10)
# rollback in first success: the failed alternative's print is undone
R(X : int)<transacts>:int =
    if (X > 0):
        return G("pos", X) | G("pos2", X + 1)
    G("rest", 0)
c := class:
    K : int
    Vals()<transacts>:int =
        if (K = 0):
            return 7
        K | K + 1
Opt(X : ?int)<transacts>:int =
    if (V := X?):
        return V | V * 10
    1 | 2
Pair(M : [int]int, K : int)<transacts>:int =
    if (A := M[K], B := M[K + 1]):
        return A + B
    G("miss", 0) | -1
Main()<transacts>:void =
    for (V := F(-5)):
        Print("f- {V}")
    for (V := F(5)):
        Print("f {V}")
    for (V := H()):
        Print("h {V}")
    for (V := Both(3)):
        Print("b {V}")
    for (V := Both(-1)):
        Print("bn {V}")
    if (V := H(), V > 50):
        Print("if {V}")
    Print("p {P(1)} {P(0)}")
    for (X : array{-3, 0, 5, 15, 25}, V := Cls(X)):
        Print("{X}: {V}")
    if (V := R(1), V > 1):
        Print("r {V}")
    for (V := c{K := 0}.Vals()):
        Print("m0 {V}")
    for (V := c{K := 4}.Vals()):
        Print("m {V}")
    for (V := Opt(option{4})):
        Print("some {V}")
    for (V := Opt(false)):
        Print("none {V}")
    M : [int]int = map{1 => 10, 2 => 20}
    for (V := Pair(M, 1)):
        Print("p {V}")
    for (V := Pair(M, 2)):
        Print("q {V}")
