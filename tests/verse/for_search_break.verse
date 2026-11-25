# (#759) A `break` in the body of a `for` whose clauses are searched (a
# generator's source writes, so a row that reaches no body is undone) leaves
# the loop around the `for`, and the `for` with it, as from any `for`: the
# search runs the body in a loop of its own, which the `break` must not be
# taken to leave alone. With a written choice, which went round the outer
# loop again before this, and with an `if` that picks a branch with a choice.
# The row V = 3 has no W and is undone; "first" breaks on the first row,
# V = 1 with N = 100, "later" on the second, the next V = 1 with N = 200.
Cell := class{var N:int = 0}
C(S:Cell)<transacts><decides>:void =
    S.N >= 0
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1} else array{}
FirstChoice(S:Cell)<transacts>:void =
    var Rounds:int = 0
    loop:
        set Rounds += 1
        if (Rounds > 3):
            Print("first-choice goes round")
            break
        for (V := (3 | 1 | 1), W : Inner(S, V)):
            Print("first-choice {V} {W} {S.N}")
            if (S.N >= 100):
                break
        Print("first-choice left the for only")
    Print("first-choice after {S.N}")
FirstIf(S:Cell)<transacts>:void =
    var Rounds:int = 0
    loop:
        set Rounds += 1
        if (Rounds > 3):
            Print("first-if goes round")
            break
        for (V := if (C[S]) then (3 | 1 | 1) else (4 | 1), W : Inner(S, V)):
            Print("first-if {V} {W} {S.N}")
            if (S.N >= 100):
                break
        Print("first-if left the for only")
    Print("first-if after {S.N}")
LaterChoice(S:Cell)<transacts>:void =
    var Rounds:int = 0
    loop:
        set Rounds += 1
        if (Rounds > 3):
            Print("later-choice goes round")
            break
        for (V := (3 | 1 | 1), W : Inner(S, V)):
            Print("later-choice {V} {W} {S.N}")
            if (S.N >= 200):
                break
        Print("later-choice left the for only")
    Print("later-choice after {S.N}")
LaterIf(S:Cell)<transacts>:void =
    var Rounds:int = 0
    loop:
        set Rounds += 1
        if (Rounds > 3):
            Print("later-if goes round")
            break
        for (V := if (C[S]) then (3 | 1 | 1) else (4 | 1), W : Inner(S, V)):
            Print("later-if {V} {W} {S.N}")
            if (S.N >= 200):
                break
        Print("later-if left the for only")
    Print("later-if after {S.N}")
Main()<transacts>:void =
    FirstChoice(Cell{})
    FirstIf(Cell{})
    LaterChoice(Cell{})
    LaterIf(Cell{})
