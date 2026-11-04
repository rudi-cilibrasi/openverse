# Full minimax over tic-tac-toe: recursion, arrays, failure-driven tests.
Lines:[]tuple(int, int, int) = array{(0, 1, 2), (3, 4, 5), (6, 7, 8), (0, 3, 6),
                                   (1, 4, 7), (2, 5, 8), (0, 4, 8), (2, 4, 6)}

# Succeeds with the player who owns a full line.
Winner(B:[]int)<decides>:int =
    W := for (L : Lines, A := B[L(0)], A <> 0, A = B[L(1)], A = B[L(2)]) { A }
    W[0]

Full(B:[]int)<decides>:void =
    not (for (X : B, X = 0) { X })[0]


# The value of the position for X (+1 win, 0 draw, -1 loss), with Player to move.
Minimax(B:[]int, Player:int, Count:int):tuple(int, int) =
    var Visited:int = Count + 1
    if (W := Winner[B]):
        return (if (W = 1) then 1 else -1, Visited)
    if (Full[B]):
        return (0, Visited)
    var Best:int = if (Player = 1) then -2 else 2
    for (I -> X : B, X = 0):
        if (Next := B.ReplaceElement[I, Player]):
            R := Minimax(Next, 3 - Player, Visited)
            set Visited = R(1)
            if (Player = 1, R(0) > Best) { set Best = R(0) }
            if (Player = 2, R(0) < Best) { set Best = R(0) }
    (Best, Visited)

Main():void =
    Empty:[]int = array{0, 0, 0, 0, 0, 0, 0, 0, 0}
    R := Minimax(Empty, 1, 0)
    Print("value of the empty board: {R(0)}")
    Print("positions visited: {R(1)}")
    Corner := Minimax(array{1, 0, 0, 0, 2, 0, 0, 0, 0}, 1, 0)
    Print("X corner, O centre, X to move: {Corner(0)}")
