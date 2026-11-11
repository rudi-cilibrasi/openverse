# Lazy alternatives retain their actual suffix as outer choices become continuations.
counter := class:
    var N:int = 0
Two(N:int):int = N | N + 1
Lazy(C:counter, N:int)<transacts><decides>:int =
    N >= 0
    set C.N += 1
    N | Lazy[C, N - 1]
First():void =
    C := counter{}
    var Total:int = 0
    if (A0 := (Lazy[C, 2] | Two(0)), set Total += A0, A1 := (Lazy[C, 2] | Two(0)), set Total += A1, A2 := (Lazy[C, 2] | Two(0)), set Total += A2, A2 = 1):
        Print("first {A0} {A1} {A2} total {Total} visits {C.N}")
    else:
        Print("none {Total} {C.N}")
Exhausted():void =
    C := counter{}
    var Total:int = 0
    if (A0 := (Lazy[C, 2] | Two(0)), set Total += A0, A1 := (Lazy[C, 2] | Two(0)), set Total += A1, A2 := (Lazy[C, 2] | Two(0)), set Total += A2, A2 < 0):
        Print("first {A0} {A1} {A2} total {Total} visits {C.N}")
    else:
        Print("none {Total} {C.N}")
Deep():void =
    C := counter{}
    var Total:int = 0
    if (A0 := (Lazy[C, 1] | Two(0)), set Total += A0, A1 := (Lazy[C, 1] | Two(0)), set Total += A1, A2 := (Lazy[C, 1] | Two(0)), set Total += A2, A3 := (Lazy[C, 1] | Two(0)), set Total += A3, A4 := (Lazy[C, 1] | Two(0)), set Total += A4, A5 := (Lazy[C, 1] | Two(0)), set Total += A5, A6 := (Lazy[C, 1] | Two(0)), set Total += A6, A7 := (Lazy[C, 1] | Two(0)), set Total += A7, A7 = 0):
        Print("{Total} {C.N}")
Main():void =
    First()
    Exhausted()
    Deep()
