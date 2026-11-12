# (#283) Choice points in sequence where the first success is taken and the
# clauses after the call leave: a return from them leaves the function, a
# break the loop around them, through the functions of their own of the
# continuation members (the code after the call prints). And a continuation
# member's own var, set in its code and read by each of its alternatives.
T(N:int)<transacts><decides>:int =
    N > 0
    X := T[N - 1] | N
    Print("t {N} {X}")
    X | X + 100
M(N:int)<transacts><decides>:int =
    N > 0
    X := M[N - 1] | N
    var Z:int = X
    set Z += 1
    Print("m {N} {Z}")
    Z | Z * 10
Find(Limit:int, Never:int)<transacts>:int =
    if (V := T[2], V > Never, Print("found {V}")):
        return V
    var Count:int = 0
    loop:
        set Count += 1
        if (V := T[2], V > Limit, Print("see {V}"), break) then Print("not reached")
        if (Count > 3) then break
    Count
Main()<transacts>:void =
    for (V := M[2]) { Print("v {V}") }
    if (V := M[2], V > 25) then Print("first {V}")
    Print("find {Find(100, 150)}")
    Print("find {Find(100, 1000)}")
    Print("find {Find(500, 1000)}")
