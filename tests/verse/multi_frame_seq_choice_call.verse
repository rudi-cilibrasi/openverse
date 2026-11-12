# (#283) Choice points in sequence: a choice followed by a call of itself.
# The code after the choice (here a Print) runs once for each of its values,
# then the call; the choice's values share that code, which is compiled once.
V(N:int)<transacts><decides>:int =
    N > 0
    X := 1 | 2
    Print("v {N} {X}")
    V[N - 1] + X | N
F(N:int)<transacts>:int =
    if (N <= 0) then 5 else:
        Wf := (1 | 2)
        Wq := F(N - 1)
        Print("q {Wq}")
        (Wq + Wf | Wf)
Main()<transacts>:void =
    for (W := V[2]) { Print("w {W}") }
    if (W := V[2], W > 2) then Print("first {W}")
    if (W := V[2], W > 9) then Print("first {W}") else Print("none")
    for (W := F(1)) { Print("f {W}") }
