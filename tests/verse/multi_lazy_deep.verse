# an in-order walk of a chain 10000 deep: the stack of pending alternatives grows with it, in cells, in linear time and space (#246, review of #267)
node := class:
    V:int = 0
    L:?node = false
Walk(T:node)<computes><decides>:int =
    if (A := T.L?) then (Walk[A] | T.V) else T.V
Chain(N:int):node = if (N > 0) then node{V := N, L := option{Chain(N - 1)}} else node{}
Main():void =
    T := Chain(10000)
    var S:int = 0
    for (X := Walk[T]) { set S += X }
    Print("{S}")
