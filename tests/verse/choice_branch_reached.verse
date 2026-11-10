# An if picks one branch, once; only the choices the program reaches are
# generators (#331): in a for, an if expression with choices in its branches
# whose picked branch is a plain value adds no choice, so a value the
# filters after it reject undoes what came before it, as the same function
# written with a return does (F, G); a picked branch with a choice of its
# own is a generator, which keeps it (j); names its condition binds
F(X : int)<transacts>:int =
    if (X < 0):
        return 0
    X | X + 1
G(X : int)<transacts>:int =
    if (X < 0) then 0 else (X | X + 1)
P(S : string)<transacts>:int =
    Print(S)
    1
Main()<transacts>:void =
    for (A := P("f"), Z := F(-1), Z > 5):
        Print("never")
    for (A := P("g"), Z := G(-1), Z > 5):
        Print("never")
    for (A := P("i"), Z := (if (A > 0) then 0 else (1 | 2)), Z > 5):
        Print("never")
    for (A := P("j"), Z := (if (A > 0) then (1 | 2) else 0), Z > 5):
        Print("never")
    M : ?int = option{3}
    for (Z := if (V := M?) then (V | V * 10) else 0):
        Print("z {Z}")
    for (Z := if (V := M?, V > 5) then (V | V * 10) else (7 | 8)):
        Print("w {Z}")
    # (an if as a set's value, #331: the same)
    var N : int = 0
    for (A := P("k"), set N = (if (Print("c"), A > 5) then (1 | 2) else 3), N > 5):
        Print("never")
    Print("n {N}")
