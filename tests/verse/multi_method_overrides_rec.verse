# A recursive overridden method with several values (#283): computed at the
# call, its recursive calls dispatching on Self too
node := class:
    K : int
    Down(N : int)<computes>:int = if (N > 0) then (N | Down(N - 1)) else 0
odd := class(node):
    Down<override>(N : int)<computes>:int = if (N > 0) then (N * 100 | Down(N - 2)) else -1
mid := class(node):
    Extra : int = 0
low := class(mid):
    Down<override>(N : int)<computes>:int = 7
Main()<transacts>:void =
    Ns : []node = array{node{K := 0}, odd{K := 0}, mid{K := 0}, low{K := 0}}
    for (X : Ns, V := X.Down(3)):
        Print("{V}")
