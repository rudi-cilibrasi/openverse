# A choice in a set's path (#283), where the first success is taken, in a
# block, through a struct's field, in a set used as a value, and with an if
# as the new value (plain, and with choices in its branches), and as a
# block's last statement, its value
Down(N : int):int = if (N > 0) then (N | Down(N - 1)) else 0
Pv(S : string, V : int)<transacts>:int =
    Print(S)
    V
st := struct:
    Items : []int = array{0, 0}
Main()<transacts>:void =
    var B : []int = array{0, 0, 0}
    if (set B[Down(2)] = 9, B[0] = 9):
        Print("a {B[0] or 8}{B[1] or 8}{B[2] or 8}")
    var A : []int = array{0, 0}
    for (X := block{ set A[0 | 1] = 2; (A[0] or 9) + (A[1] or 9) }):
        Print("b {X}")
    var S : st = st{}
    for (set S.Items[0 | 1] = 4):
        Print("c {S.Items[0] or 9}{S.Items[1] or 9}")
    var Q : []int = array{0, 0}
    for (X := (set Q[0 | 1] = 5)):
        Print("d {X} {Q[0] or 9}{Q[1] or 9}")
    Y := 1
    var E : []int = array{0, 0}
    for (set E[0 | 1] = if (Y > 0) then 5 else 6):
        Print("e {E[0] or 9}{E[1] or 9}")
    var F : []int = array{0, 0}
    for (set F[Pv("i", 0) + (0 | 1)] = if (Y > 0) then (5 | 6) else 7):
        Print("f {F[0] or 9}{F[1] or 9}")
    var G : []int = array{0, 0, 0}
    for (set G[Down(2)] = if (Y > 0) then 5 else 6):
        Print("g {G[0] or 9}{G[1] or 9}{G[2] or 9}")
    var K : []int = array{0, 0}
    for (X := block{ set K[0 | 1] = 2 }):
        Print("k {X} {K[0] or 9}{K[1] or 9}")
    for (X := block{ Z := 1; set K[0 | 1] += Z }):
        Print("l {X} {K[0] or 9}{K[1] or 9}")
    for (X := block{ set K[1] = Pv("p", 0) + (5 | 6) }):
        Print("m {X} {K[0] or 9}{K[1] or 9}")
