# Producer effects interleave with bodies; failed filters undo only their iteration.
counter := class:
    var N:int = 0
Two(N:int):int = N | N + 1
Lazy(C:counter, N:int)<transacts><decides>:int =
    N >= 0
    set C.N += 1
    Print("visit {N}")
    N | Lazy[C, N - 1]
Even(C:counter, N:int)<transacts><decides>:int =
    N >= 0
    set C.N += 1
    N | Odd[C, N - 1]
Odd(C:counter, N:int)<transacts><decides>:int =
    N >= 0
    set C.N += 1
    N | Even[C, N - 1]
Main():void =
    C := counter{}
    var Total:int = 0
    R := for (A := (Lazy[C, 1] | Two(0)), set Total += A,
        B := (Lazy[C, 1] | Two(0)), set Total += B, B = 0):
        set Total += 10
        Print("body {A} {B} {Total} {C.N}")
        Total
    Print("end {R.Length} {Total} {C.N}")
    S := for (A := (Two(0) | Two(2)), set Total += A,
        B := (Two(0) | Two(2)), set Total += B, L := Even[C, 1], L = 0):
        set Total += L
        Total
    Print("mutual {S.Length} {Total} {C.N}")
    if (A := (Even[C, 2] | Two(0)), B := (Even[C, 2] | Two(0)),
        D := (Even[C, 2] | Two(0)), D = 1):
        Print("first mutual {A} {B} {D} {C.N}")
