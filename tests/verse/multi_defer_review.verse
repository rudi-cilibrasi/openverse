# A defer: of its own in functions and blocks with several values (#283), the shapes #391's review found:
# a branch's own defer: at its return (before the function's), or at its end before the rest; an
# else-block's defer: for each of its values; values typed by where they are inside a tuple, array or
# map (Y, false), array{array{}}, (Z, map{}); a void function that ends in a defer:; a branch that always
# returns, with a return before its end
F(N:int)<transacts>:int =
    if (N > 5) then { defer: Print("x{N}"); return 0 }
    N | N + 1
G(N:int)<transacts>:int =
    defer: Print("g{N}")
    if (N > 5) then { defer: Print("x{N}"); return 0 }
    N | N + 1
H(N:int)<transacts>:int =
    if (N > 5) then { defer: Print("y{N}"); return N | N * 2 } else { defer: Print("z{N}"); N | N + 1 }
E(N:int)<transacts>:int =
    if (N > 5) then return 0 else { defer: Print("d"); Print("in-else") }
    Print("rest")
    N | N + 1
# (a branch that always returns, its own defer: before its returns: for each value, before the function's)
Nr(N:int)<transacts>:int =
    defer: Print("n")
    if (N > 5) then { defer: Print("x"); if (N > 7) then return (1 | 2); return 0 }
    N | N + 1
# (a branch that always returns, its own defer: after a return: only where it is reached)
Q(N:int)<transacts>:int =
    if (N > 5) then { if (N > 7) then return (1 | 2); defer: Print("q"); return (3 | 4) }
    N | N + 1
V()<transacts>:void =
    Y := 1 | 2
    Print("y {Y}")
    defer: Print("b")
Main()<transacts>:void =
    for (X := F(9)) { Print("for-f {X}") }
    for (X := G(9)) { Print("for-g {X}") }
    if (X := G(9)) { Print("if-g {X}") }
    if (X := first{ G(9) }) { Print("first-g {X}") }
    for (X := G(1)) { Print("for-g1 {X}") }
    for (X := H(1)) { Print("h {X}") }
    for (X := H(9)) { Print("h {X}") }
    for (X := E(1)) { Print("e {X}") }
    for (V()) { Print("v") }
    for (X := Nr(9)) { Print("n9 {X}") }
    for (X := Nr(6)) { Print("n6 {X}") }
    for (X := Q(9)) { Print("q9 {X}") }
    for (X := Q(6)) { Print("q6 {X}") }
    for (T:tuple(int, ?int) := block{ defer: Print("d"); Y := 1 | 2; (Y, false) }) { Print("t {T(0)}") }
    for (A:[][]int := block{ defer: Print("d"); Y := 1 | 2; array{array{}} }) { Print("a {A.Length}") }
    for (M:tuple(int, [int]string) := block{ defer: Print("d"); Z := 1 | 2; (Z, map{}) }) { Print("m {M(0)}") }
    for (I := 1..2, P:tuple(int, ?int) := (if (I = 1) then { defer: Print("t"); Z := 1 | 2; (Z, option{Z}) } else { defer: Print("e"); Z := 3 | 4; (Z, false) })):
        Print("p {P(0)}")
