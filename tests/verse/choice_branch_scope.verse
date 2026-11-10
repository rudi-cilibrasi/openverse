# An if with choices in its branches, in a for (#331): the names its
# condition binds are its branch's only, so the clauses after the if may
# bind them again; `set L = if …` takes the branches at L's type
nonneg := type{_X:int where 0 <= _X}
Main()<transacts>:void =
    M : ?int = option{3}
    N : ?int = false
    for (Z := (if (V := M?) then (V | 1) else 0), V := Z + 1):
        Print("a {Z} {V}")
    for (Z := (if (V := M?, W := V + 1) then (V | W) else 0), W := Z + 1, V := 7):
        Print("b {Z} {W} {V}")
    for (Z := (if (V := N?) then V else if (W := M?) then (W | 1) else 0), W := Z * 2):
        Print("c {Z} {W}")
    # (the same name in an if and its else if)
    for (Z := (if (V := N?) then V else if (V := M?) then (V | 1) else 0)):
        Print("d {Z}")
    var O : ?int = false
    for (C := (1 | 2), set O = (if (C = 1) then false else (option{C} | false))):
        Print("o {if (V := O?) then V else 0}")
    var P : nonneg = 0
    for (C := (1 | 2), set P = (if (C = 1) then 1 else (2 | 3))):
        Print("p {P}")
    var A : []int = array{9}
    for (C := (1 | 2), set A = (if (C = 1) then array{} else (array{} | array{5}))):
        Print("q {A.Length}")
