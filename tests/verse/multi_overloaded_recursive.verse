# Overloaded functions with several values (#283) called by recursive ones whose values are computed
# at the call (effect-free, not of a generator's shape): each call takes the overload its arguments
# fit, by type and by arity, also with a named argument and a default; and an overload that is such a
# recursive one itself, through its other overload
Two(N:int)<computes>:int = N | N * 10
Two(S:string)<computes>:int = S.Length | 100
Two(A:int, B:int, ?Scale:int = 2)<computes>:int = A * Scale | B
R(N:int)<computes><decides>:int =
    N < 3
    Two(N) | R[N + 1]
Q(N:int)<computes><decides>:int =
    N < 2
    X := Two("{N}") + Two(N, 5, ?Scale := 3)
    X | Q[N + 1]
P(N:int)<computes><decides>:int =
    N < 2
    Two(N, 7) + P[N + 1] | N
Walk(N:int)<computes><decides>:int =
    N > 0
    Walk("{N}") | Walk[N - 1]
Walk(S:string)<computes>:int = S.Length | 7
Main():void =
    for (X := R[1]) { Print("a {X}") }
    if (X := R[1], X > 15) { Print("b {X}") }
    for (X := Q[0]) { Print("c {X}") }
    for (X := P[0]) { Print("d {X}") }
    for (X := Walk[11]) { Print("e {X}") }
