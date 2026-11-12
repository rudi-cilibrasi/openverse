# (#283) Choice points in sequence: a choice after its call of itself, in a <computes> function that may call Err(): taken lazily.
Check(N:int)<computes>:int = if (N < 0) then Err() else N
R(N:int)<computes><decides>:int =
    N > 0
    Check(N) | R[N - 1] + (0 | 1)
Main():void = for (X := R[3]) { Print("{X}") }
