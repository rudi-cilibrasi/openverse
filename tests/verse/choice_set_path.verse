# A choice or a call with several values in a set's path (#283): the
# path's indices are evaluated first, as set evaluates them, then for op=
# the old value, then the new one; each index's choice is a generator in a
# for, and is searched where the first success is taken
Two(N : int):int = N | N + 10
Down(N : int):int = if (N > 0) then (N | Down(N - 1)) else 0
P(S : string)<transacts>:int =
    Print(S)
    1
Main()<transacts>:void =
    var A : []int = array{0, 0, 0}
    for (set A[0 | 1] = 5):
        Print("a {A[0] or 9}{A[1] or 9}{A[2] or 9}")
    var B : []int = array{0, 0, 0}
    for (set B[Down(2)] = 7):
        Print("b {B[0] or 9}{B[1] or 9}{B[2] or 9}")
    var D : []int = array{1, 2, 3}
    for (set D[Two(0)] += 10):
        Print("d {D[0] or 9}")
    var E : []int = array{0, 0}
    if (set E[0 | 1] = 3, E[0] = 9):
        Print("never")
    Print("e {E[0] or 9}{E[1] or 9}")
    if (set E[0 | 1] = 4, E[0] = 0):
        Print("f {E[0] or 9}{E[1] or 9}")
    var G : []int = array{0, 0}
    for (set G[P("i") - 1 + (0 | 1)] = P("v")):
        Print("g {G[0] or 9}{G[1] or 9}")
    var H : []int = array{0, 0}
    for (set H[0 | 1] = (7 | 8)):
        Print("h {H[0] or 9}{H[1] or 9}")
