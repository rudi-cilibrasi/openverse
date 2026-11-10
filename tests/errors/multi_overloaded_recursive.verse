# expect: 4:0: R has several values and is recursive, or called by a recursive one (so its values are computed at the call, F$all), and it calls Two, which is overloaded with several values
Two(N:int)<computes>:int = N | N * 10
Two(S:string)<computes>:int = S.Length | 100
R(N:int)<computes><decides>:int =
    N < 3
    Two(N) | R[N + 1]
Main():void =
    for (X := R[1]) { Print("a {X}") }
    if (X := R[1], X > 15) { Print("b {X}") }
