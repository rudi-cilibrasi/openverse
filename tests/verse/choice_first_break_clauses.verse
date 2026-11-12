# A break in the clauses of an if with a choice leaves the loop (#283),
# keeping what the clauses did up to it, as with no choice: an alternative
# that failed before it is rolled back, as backtracking does.
Two(N:int):int = N | N + 1
Leave()<transacts>:int =
    var V:int = 0
    defer: Print("function cleanup V={V}")
    loop:
        defer: Print("loop cleanup V={V}")
        # (a block of its own runs its cleanup as the break leaves it)
        if (X := 1 | 2, Z := block{ defer: Print("block cleanup X={X} V={V}"); set V += X; if (X = 2) then break; X }, Z > 5):
            Print("not reached")
        Print("not reached")
    V
Main()<transacts>:void =
    var V:int = 0
    # before the choice, which never runs
    loop:
        if (set V = 1, break, X := 1 | 2, X > 1) then Print("not reached")
        Print("not reached")
    Print("before: V={V}")
    # between choices, which run as far as the break
    loop:
        if (set V = 10, X := 1 | 2 | 3, set V += X, Print("try {X}"), X >= 2, break, Y := 7 | 8, Y > 7):
            Print("not reached")
    Print("between: V={V}")
    # after them: the first pair whose sum is 5, from functions with several values
    loop:
        if (X := Two(1), Y := Two(X), set V = X * 10 + Y, X + Y = 5, break) then Print("not reached")
    Print("after: V={V}")
    # on some alternatives only: the others fail or reach the branch
    var N:int = 0
    loop:
        set N += 1
        if (X := 1 | 2 | 3, X + N > 3, Y := (if (X + N = 6) then break else X * 10), Print("Y={Y}"), Y > 20):
            Print("then N={N} Y={Y}")
        else:
            Print("else N={N}")
    Print("N={N}")
    Print("left: {Leave()}")
