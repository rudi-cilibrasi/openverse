# choice (#208): a choice's values in spatial order; for takes all of them,
# if and first{} the first success; failed alternatives are rolled back
Pick()<decides>:int = first(X := 2 | 3 | 4, X > 2) { X * 10 }
Main():void =
    # for: all values, the leftmost choice slowest; nested choices spliced
    for (X := 1 | 2 | 3):
        Print("{X}")
    for (X := 1 | 2, Y := 10 | 20):
        Print("{X + Y}")
    Xs := for{(1 | 2) | 3}
    Print("{Xs.Length}")
    # a failing alternative gives no value
    Ys := for (X := 1 | 2 | 3, X <> 2) { X * 10 }
    for (Y : Ys) { Print("{Y}") }
    # if: the first success; later alternatives never run
    if (X := 1 | 2 | 3, X > 1) then Print("first {X}")
    if (X := 5 | Err()) then Print("lazy {X}")
    if (F := first{X := 4 | 6 | 9; X > 5; X}) then Print("first-macro {F}")
    if (X := 1 | 2, X > 5) then Print("no") else Print("none")
    # rollback: of a variable, and of output
    var N:int = 0
    if (X := (set N = 1; 1) | (set N = 2; 2), X > 1) then Print("{X} {N}")
    if (X := (Print("a"); 1) | (Print("b"); 2), X = 2) then Print("got {X}")
    # in a for, the effects of each success stay
    for (X := (Print("p"); 1) | (Print("q"); 2)) { Print("{X}") }
    if (set N = 7 | 8, N > 7) then Print("set {N}")
    # nested choices: an inner one exhausted rolls the outer one back
    if (X := 1 | 2 | 3, Y := X | 10, X + Y = 12) then Print("{X} {Y}")
    Zs := for (X := 1 | 2, X > 1, Y := X | 0) { X * 100 + Y }
    for (Z : Zs) { Print("{Z}") }
    Ps := for{X := 1 | 2; Y := 3 | 4; X * Y}
    for (P : Ps) { Print("{P}") }
    # types: the join, or the written type
    if (S := "a" | "bc", S.Length > 1) then Print(S)
    if (T:int = 3 | 4, T > 3) then Print("typed {T}")
    if (X := 1 | 2 | 3, X > 2):
        Print("block {X}")
    else:
        Print("else")
    V := if{X := 0 | 7; X > 0} else 99
    Print("macro {V}")
    if (R := Pick[]) then Print("first-body {R}")
