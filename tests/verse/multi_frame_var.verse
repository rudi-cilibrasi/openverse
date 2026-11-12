# (#283) A var set in the code after a call of itself: a cell, so every later
# value of the call, and the caller's later alternatives, see what a kept
# value set, and a rejected value's write is undone with it.
F(N:int)<transacts><decides>:int =
    N > 0
    var K:int = N * 10
    X := F[N - 1] | N
    set K += X
    Print("F {N} K {K}")
    K
counter := class:
    var Seen:int = 0
    G(N:int)<transacts><decides>:int =
        N > 0
        var Hits:int = 0
        X := G[N - 1] * 2 | N
        set Hits += 1
        set Seen += 1
        X + Hits * 100
Main()<transacts>:void =
    for (V := F[2]) { Print("v {V}") }
    for (V := F[2], V > 31) { Print("w {V}") }
    if (V := F[2], V > 31) then Print("never {V}") else Print("none")
    if (V := F[2], V > 25) then Print("first {V}")
    C := counter{}
    for (V := C.G[2]) { Print("g {V} seen {C.Seen}") }
