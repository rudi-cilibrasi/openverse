# a tree walked in order by a generator whose last expression is an if with a choice of calls in one branch: in a for, then in an if (#246)
node := class:
    V:int = 0
    L:?node = false
    R:?node = false
Walk(T:node)<computes><decides>:int =
    if (A := T.L?, B := T.R?) then (Walk[A] | T.V | Walk[B]) else T.V
Main():void =
    Leaf1 := node{V := 1}
    Leaf3 := node{V := 3}
    Leaf5 := node{V := 5}
    Leaf7 := node{V := 7}
    N2 := node{V := 2, L := option{Leaf1}, R := option{Leaf3}}
    N6 := node{V := 6, L := option{Leaf5}, R := option{Leaf7}}
    Root := node{V := 4, L := option{N2}, R := option{N6}}
    R := for (X := Walk[Root]):
        X
    for (X : R):
        Print("{X}")
    if (X := Walk[Root], X > 4):
        Print("first above 4: {X}")
