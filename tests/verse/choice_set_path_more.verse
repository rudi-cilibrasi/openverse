# A choice in a set's path (#283), where the first success is taken, in a
# block, through a struct's field, and in a set used as a value
Down(N : int):int = if (N > 0) then (N | Down(N - 1)) else 0
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
