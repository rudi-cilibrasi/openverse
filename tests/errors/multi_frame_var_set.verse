# expect: 3:0: F has several values and is recursive, or called by a recursive one, and it has a var or a set
# (a var set in the code after its call of itself, which runs on a copy of the names: not taken lazily, #283)
F(N:int)<computes><decides>:int =
    N > 0
    var K:int = N
    X := F[N - 1] | N
    set K += X
    K
Main():void =
    for (V := F[2]) { Print("v {V}") }
