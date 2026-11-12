# expect: 4:0: R has several values and is recursive, or called by a recursive one, and it may call Err() (Check does)
# (a choice after its call of itself: all its values computed at a call, F$all, not taken lazily, #246, #283)
Check(N:int)<computes>:int = if (N < 0) then Err() else N
R(N:int)<computes><decides>:int =
    N > 0
    Check(N) | R[N - 1] + (0 | 1)
Main():void = for (X := R[3]) { Print("{X}") }
