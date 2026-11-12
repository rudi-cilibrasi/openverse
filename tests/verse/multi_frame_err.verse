# (its call of itself with code after it: taken lazily, the code a return frame that runs on each of its values, #283)
Check(N:int)<computes>:int = if (N < 0) then Err() else N
R(N:int)<computes><decides>:int =
    N > 0
    Check(N) | R[N - 1] + 0
Main():void = for (X := R[3]) { Print("{X}") }
