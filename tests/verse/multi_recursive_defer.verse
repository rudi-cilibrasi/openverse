# (#283) A recursive function with several values, or a function with several values its code
# calls, may have a defer: of its own: it runs as each value leaves the function, after the value
# is computed and before the code after the call, as an inlined body's does; a value whose clauses
# fail runs none. A block's own defer: in such a function's code runs as each value leaves the block.
R(N:int)<transacts>:int =
    defer: Print("r {N}")
    if (N <= 0) then (0 | 1) else (N | R(N - 1))
B(N:int)<transacts>:int =
    if (N <= 0) then block{ defer: Print("b0"); 0 | 1 } else (N | B(N - 1))
W(N:int)<transacts><decides>:int =
    N > 0
    defer: Print("w {N}")
    X := W[N - 1] | N
    Print("at {N} got {X}")
    X + 1
Ev(N:int)<transacts>:int =
    defer: Print("ev {N}")
    if (N <= 0) then 0 else (N | Od(N - 1))
Od(N:int)<transacts>:int =
    defer: Print("od {N}")
    if (N <= 0) then 1 else (N * 10 | Ev(N - 1))
Ret(N:int)<transacts>:int =
    defer: Print("outer {N}")
    if (N <= 0):
        defer: Print("base")
        return 7 | 8
    Print("mid {N}")
    N | Ret(N - 1)
Two(N:int)<transacts>:int =
    defer: Print("two {N}")
    if (N > 5) then N else (N | N + 1)
Sum(N:int)<transacts><decides>:int =
    N > 0
    defer: Print("sum {N}")
    (Sum[N - 1] | 0) + Two(N)
Blk(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        X := block:
            defer: Print("blk {N}")
            Y := Blk(N - 1) | N * 10
            Y + 1
        Print("after {N} {X}")
        X
node := class:
    V:int
    Walk(N:int)<transacts>:int =
        defer: Print("walk {V} {N}")
        if (N <= 0) then V else (N | Walk(N - 1))
Main()<transacts>:void =
    for (X := R(1)) { Print("v {X}") }
    if (X := R(1), X < 1) then Print("first {X}")
    for (X := B(1)) { Print("v {X}") }
    for (V := W[2]) { Print("v {V}") }
    if (V := W[2], V > 2) then Print("first {V}")
    for (X := Ev(2)) { Print("v {X}") }
    if (X := Ev(2), X = 10) then Print("first {X}")
    for (X := Ret(1)) { Print("v {X}") }
    if (X := Ret(1), X > 7) then Print("first {X}")
    for (V := Sum[2], V > 2) { Print("v {V}") }
    if (V := Sum[2], V = 5) then Print("first {V}")
    for (V := Blk(2)) { Print("v {V}") }
    for (X := node{V := 5}.Walk(1)) { Print("v {X}") }
