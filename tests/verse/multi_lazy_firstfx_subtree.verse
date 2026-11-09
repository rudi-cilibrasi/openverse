# a tree walk printing at each node, where the first success is taken: the left subtree, all of whose values are rejected, is undone, as the Verse Calculus undoes it; a for keeps it (#246 step 2)
node := class:
    V:int = 0
    L:?node = false
    R:?node = false
Walk(T:node)<transacts><decides>:int =
    Print("visit {T.V}")
    if (A := T.L?, B := T.R?) then (Walk[A] | Walk[B]) else T.V
Main():void =
    N4 := node{V := 4}
    N5 := node{V := 5}
    N6 := node{V := 6}
    N7 := node{V := 7}
    Root := node{V := 1, L := option{node{V := 2, L := option{N4}, R := option{N5}}}, R := option{node{V := 3, L := option{N6}, R := option{N7}}}}
    if (X := Walk[Root], X = 6) then Print("found {X}")
    Print("--")
    for (X := Walk[Root], X = 6) { Print("for {X}") }
